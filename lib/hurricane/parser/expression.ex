defmodule Hurricane.Parser.Expression do
  @moduledoc """
  Pratt parser for Elixir expressions.

  Uses binding power to handle operator precedence and associativity.
  Higher binding power = tighter binding.

  For left-associative operators: right BP = left BP + 1
  For right-associative operators: left BP = right BP + 1
  """

  alias Hurricane.Ast
  alias Hurricane.Parser.{State, Recovery}

  ## BINDING POWER TABLES

  # Infix operators: {left_bp, right_bp}
  # Listed from lowest to highest precedence
  @infix_bp %{
    # Right-associative (left > right)
    # Default argument
    :\\ => {5, 4},
    # Cons
    :| => {9, 8},
    # NOTE: :-> is NOT an infix operator - it's handled explicitly by stab clause parsing
    # Guard
    :when => {11, 10},
    # Type annotation
    :"::" => {13, 12},
    # Comprehension, with
    :<- => {17, 16},
    # Match
    := => {19, 18},

    # Left-associative (right > left)
    :|| => {21, 22},
    :||| => {21, 22},
    :or => {21, 22},
    :&& => {23, 24},
    :&&& => {23, 24},
    :and => {23, 24},

    # Comparison (left-associative)
    :== => {25, 26},
    :!= => {25, 26},
    :=~ => {25, 26},
    :=== => {25, 26},
    :!== => {25, 26},

    # Relational (left-associative)
    :< => {27, 28},
    :> => {27, 28},
    :<= => {27, 28},
    :>= => {27, 28},

    # Pipe (left-associative)
    :|> => {29, 30},

    # Membership
    :in => {31, 32},
    :"not in" => {31, 32},

    # Bitwise xor
    :"^^^" => {33, 34},

    # Concat (right-associative!)
    :++ => {35, 34},
    :-- => {35, 34},
    :+++ => {35, 34},
    :--- => {35, 34},
    :<> => {35, 34},

    # Range
    :.. => {37, 36},
    :"../" => {37, 36},

    # Arithmetic (left-associative)
    :+ => {39, 40},
    :- => {39, 40},

    # Multiply/divide (left-associative)
    :* => {41, 42},
    :/ => {41, 42},

    # Power (left-associative - despite math convention!)
    :** => {43, 44},

    # Dot (highest infix precedence)
    :dot => {61, 62}
  }

  # Prefix operators: right binding power only
  @prefix_bp %{
    :! => 55,
    :not => 55,
    :"~~~" => 55,
    # Pin
    :^ => 57,
    # Capture - VERY LOW so &Enum.map/2 captures entire expression
    # Despite docs saying 59, actual Elixir behavior is that & captures everything
    :& => 1,
    # Unary minus
    :- => 53,
    # Unary plus
    :+ => 53,
    # Module attribute
    :@ => 63
  }

  # Postfix binding power (for calls and access)
  @call_bp 60
  @access_bp 60

  ## PUBLIC API

  @doc """
  Parse an expression with given minimum binding power.

  Options:
  - `:allow_do` - whether to parse trailing do blocks (default: true)
                  Set to false when parsing inside case/if/etc where do belongs to outer
  """
  def parse_expression(state, min_bp \\ 0, opts \\ []) do
    allow_do = Keyword.get(opts, :allow_do, true)

    # 1. Parse prefix (atom, literal, unary op, parenthesized expr)
    {state, lhs} = parse_prefix(state, allow_do)

    # 2. Loop: while next op binds tighter than min_bp
    parse_infix_loop(state, lhs, min_bp)
  end

  ## PREFIX PARSING

  defp parse_prefix(state, allow_do) do
    token = State.current(state)

    cond do
      # Prefix operators
      prefix_op?(token) ->
        parse_prefix_op(state)

      # Literals
      State.at?(state, :integer) ->
        {state, _} = State.advance(state)
        {state, token.value}

      State.at?(state, :float) ->
        {state, _} = State.advance(state)
        {state, token.value}

      State.at?(state, :atom) ->
        {state, _} = State.advance(state)
        {state, token.value}

      State.at?(state, :atom_unsafe) ->
        # Atom with interpolation like :"foo_#{x}"
        parse_atom_unsafe(state)

      State.at?(state, :string) ->
        parse_string(state)

      State.at?(state, :heredoc) ->
        parse_heredoc(state)

      State.at?(state, :charlist) ->
        {state, _} = State.advance(state)
        {state, token.value}

      State.at?(state, true) ->
        {state, _} = State.advance(state)
        {state, true}

      State.at?(state, false) ->
        {state, _} = State.advance(state)
        {state, false}

      State.at?(state, nil) ->
        {state, _} = State.advance(state)
        {state, nil}

      # Special forms
      State.at?(state, :case) ->
        parse_case(state)

      State.at?(state, :cond) ->
        parse_cond(state)

      State.at?(state, :if) ->
        parse_if(state)

      State.at?(state, :unless) ->
        parse_unless(state)

      State.at?(state, :with) ->
        parse_with(state)

      State.at?(state, :try) ->
        parse_try(state)

      State.at?(state, :receive) ->
        parse_receive(state)

      State.at?(state, :for) ->
        parse_for(state)

      State.at?(state, :quote) ->
        parse_quote(state)

      # Identifiers and calls - different token types based on what follows
      # Plain identifier: variable or no-paren call (space before any parens/brackets)
      State.at?(state, :identifier) ->
        parse_identifier_or_call(state, allow_do)

      # Paren identifier: foo( - identifier immediately followed by (
      State.at?(state, :paren_identifier) ->
        parse_paren_identifier(state, allow_do)

      # Do identifier: foo do - identifier followed by do (no args)
      # Behavior depends on allow_do flag:
      # - allow_do=true: parse as zero-arg call with do block (foo do ... end)
      # - allow_do=false: just return identifier, do belongs to outer (case foo do)
      State.at?(state, :do_identifier) ->
        parse_do_identifier(state, allow_do)

      # Bracket identifier: foo[ - identifier immediately followed by [
      State.at?(state, :bracket_identifier) ->
        parse_bracket_identifier(state)

      # Op identifier: foo +b - identifier followed by space then operator with no space after
      # The tokenizer marks this as :op_identifier to indicate the operator should be prefix
      # This is a no-parens call where the first arg starts with a unary operator
      State.at?(state, :op_identifier) ->
        parse_op_identifier(state, allow_do)

      # Special keywords that work like function calls
      State.at?(state, :raise) ->
        parse_keyword_call(state, :raise)

      State.at?(state, :reraise) ->
        parse_keyword_call(state, :reraise)

      State.at?(state, :throw) ->
        parse_keyword_call(state, :throw)

      State.at?(state, :unquote) ->
        parse_keyword_call(state, :unquote)

      State.at?(state, :unquote_splicing) ->
        parse_keyword_call(state, :unquote_splicing)

      # Directives (use, import, require, alias) can appear as expressions
      State.at?(state, :use) ->
        parse_keyword_call(state, :use)

      State.at?(state, :import) ->
        parse_keyword_call(state, :import)

      State.at?(state, :require) ->
        parse_keyword_call(state, :require)

      State.at?(state, :alias_directive) ->
        parse_keyword_call(state, :alias)

      # Definition keywords can appear as calls in desugared syntax: defmodule(...)
      State.at?(state, :defmodule) ->
        parse_keyword_call(state, :defmodule)

      State.at?(state, :def) ->
        parse_keyword_call(state, :def)

      State.at?(state, :defp) ->
        parse_keyword_call(state, :defp)

      State.at?(state, :defmacro) ->
        parse_keyword_call(state, :defmacro)

      State.at?(state, :defmacrop) ->
        parse_keyword_call(state, :defmacrop)

      State.at?(state, :defdelegate) ->
        parse_keyword_call(state, :defdelegate)

      State.at?(state, :defguard) ->
        parse_keyword_call(state, :defguard)

      State.at?(state, :defguardp) ->
        parse_keyword_call(state, :defguardp)

      # Module aliases
      State.at?(state, :alias) ->
        parse_alias(state)

      # Parenthesized expression
      State.at?(state, :lparen) ->
        parse_parenthesized(state)

      # List
      State.at?(state, :lbracket) ->
        parse_list(state)

      # Tuple
      State.at?(state, :lbrace) ->
        parse_tuple(state)

      # Map
      State.at?(state, :map_open) ->
        parse_map(state)

      # Struct (%Foo{})
      State.at?(state, :percent) ->
        parse_struct(state)

      # Binary/bitstring
      State.at?(state, :langle) ->
        parse_binary(state)

      # Sigil
      State.at?(state, :sigil) ->
        parse_sigil(state)

      # Anonymous function
      State.at?(state, :fn) ->
        parse_fn(state)

      # Capture argument placeholder (&1, &2, etc.)
      State.at?(state, :capture_int) ->
        parse_capture_arg(state)

      # Keyword identifier starts implicit keyword list (e.g., `only: [from: 2]`)
      State.at?(state, :kw_identifier) ->
        parse_implicit_keyword_list(state)

      # Recovery or end of expression
      Recovery.at_recovery?(state, Recovery.expression()) or State.at_end?(state) ->
        {state, nil}

      # Unknown - error
      true ->
        state = State.add_error(state, "expected expression, got #{inspect(token && token.kind)}")
        {state, _} = State.advance(state)
        {state, Ast.error_at(token)}
    end
  end

  defp prefix_op?(nil), do: false
  defp prefix_op?(%{kind: kind}), do: Map.has_key?(@prefix_bp, kind)

  defp parse_prefix_op(state) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = Ast.token_meta(token)
    bp = Map.fetch!(@prefix_bp, token.kind)

    # RHS of prefix op shouldn't consume do blocks - they belong to outer constructs
    # e.g., in `if !f(x) do 1 end`, the `do` belongs to `if`, not `f`
    {state, operand} = parse_expression(state, bp, allow_do: false)
    ast = Ast.unary_op(token.kind, meta, operand)
    {state, ast}
  end

  ## INFIX LOOP

  defp parse_infix_loop(state, lhs, min_bp) do
    token = State.current(state)

    # If there's a newline before an operator that can also be prefix,
    # treat it as start of new expression (e.g., -x\n+y is two expressions)
    if State.newline_before?(state) and prefix_op?(token) do
      {state, lhs} = maybe_parse_postfix(state, lhs, min_bp)
      {state, lhs}
    else
      case infix_bp(token) do
        {left_bp, right_bp} when left_bp >= min_bp ->
          # Infix operator: must consume at least the operator token
          state = State.advance_push(state)
          {state, lhs} = parse_infix_op(state, lhs, token, right_bp)
          state = State.advance_pop!(state)
          parse_infix_loop(state, lhs, min_bp)

        _ ->
          # Check for postfix (call, access)
          state = State.advance_push(state)
          {state, new_lhs} = maybe_parse_postfix(state, lhs, min_bp)

          # If postfix consumed something, continue the loop to check for more infix/postfix
          if new_lhs != lhs do
            state = State.advance_pop!(state)
            parse_infix_loop(state, new_lhs, min_bp)
          else
            # Legitimate exit: didn't consume anything
            state = State.advance_drop(state)
            {state, lhs}
          end
      end
    end
  end

  defp infix_bp(nil), do: nil
  defp infix_bp(%{kind: kind}), do: Map.get(@infix_bp, kind)

  defp parse_infix_op(state, lhs, op_token, right_bp) do
    {state, _} = State.advance(state)
    meta = Ast.token_meta(op_token)

    cond do
      # Special handling for dot operator
      op_token.kind == :dot ->
        parse_dot_rhs(state, lhs, meta)

      # Special handling for "not in" - produces {:not, _, [{:in, _, [lhs, rhs]}]}
      op_token.kind == :"not in" ->
        # RHS of binary op shouldn't consume do blocks
        {state, rhs} = parse_expression(state, right_bp, allow_do: false)
        in_ast = {:in, meta, [lhs, rhs]}
        ast = {:not, meta, [in_ast]}
        {state, ast}

      true ->
        # RHS of binary op shouldn't consume do blocks - they belong to outer constructs
        {state, rhs} = parse_expression(state, right_bp, allow_do: false)
        ast = Ast.binary_op(op_token.kind, meta, lhs, rhs)
        {state, ast}
    end
  end

  ## DOT ACCESS

  defp parse_dot_rhs(state, lhs, dot_meta) do
    token = State.current(state)

    cond do
      # Remote call with parens: Foo.bar(args)
      # :paren_identifier means identifier immediately followed by (
      State.at?(state, :paren_identifier) ->
        id_token = token
        {state, _} = State.advance(state)
        name = id_token.value
        id_meta = Ast.token_meta(id_token)

        # Consume lparen and parse args
        {state, _} = State.advance(state)
        {state, args} = parse_call_args(state)
        {state, closing} = State.expect(state, :rparen)

        call_meta = if closing, do: Ast.with_closing(id_meta, closing), else: id_meta
        dot_ast = {:., dot_meta, [lhs, name]}
        ast = {dot_ast, call_meta, args}
        {state, ast}

      # Remote field access or no-paren call: Foo.bar
      # Also handles :do_identifier - after a dot, the `do` belongs to outer construct
      # e.g., `case user.provider do` - the do is for case, not provider
      State.at_any?(state, [:identifier, :do_identifier]) ->
        id_token = token
        {state, _} = State.advance(state)
        name = id_token.value
        id_meta = Ast.token_meta(id_token)

        # Check for call with parens (from space: Foo.bar (x) - rare but valid)
        if State.at?(state, :lparen) do
          {state, _} = State.advance(state)
          {state, args} = parse_call_args(state)
          {state, closing} = State.expect(state, :rparen)

          # Use identifier position for call meta, not dot position
          call_meta = if closing, do: Ast.with_closing(id_meta, closing), else: id_meta
          dot_ast = {:., dot_meta, [lhs, name]}
          ast = {dot_ast, call_meta, args}
          {state, ast}
        else
          # Field access (no parens) - use identifier position with no_parens flag
          call_meta = [{:no_parens, true} | id_meta]
          dot_ast = {:., dot_meta, [lhs, name]}
          ast = {dot_ast, call_meta, []}
          {state, ast}
        end

      # Remote bracket access: Foo.bar[key]
      State.at?(state, :bracket_identifier) ->
        id_token = token
        {state, _} = State.advance(state)
        name = id_token.value
        id_meta = Ast.token_meta(id_token)

        # Build the field access first
        call_meta = [{:no_parens, true} | id_meta]
        dot_ast = {:., dot_meta, [lhs, name]}
        field_ast = {dot_ast, call_meta, []}

        # The bracket is handled in postfix - just return the field access
        {state, field_ast}

      # Multi-alias or tuple access: Foo.{A, B}
      State.at?(state, :lbrace) ->
        {state, _lbrace} = State.advance(state)
        {state, elements} = parse_collection_elements(state, :rbrace)
        {state, rbrace} = State.expect(state, :rbrace)
        dot_ast = {:., dot_meta, [lhs, :{}]}
        call_meta = if rbrace, do: Ast.with_closing(dot_meta, rbrace), else: dot_meta
        ast = {dot_ast, call_meta, elements}
        {state, ast}

      true ->
        state = State.add_error(state, "expected identifier after '.'")
        {state, lhs}
    end
  end

  ## POSTFIX (Calls and Access)

  defp maybe_parse_postfix(state, lhs, min_bp) do
    cond do
      # Function call with parens: foo(...)
      # NOT if there's a newline before ( - that's a separate expression
      State.at?(state, :lparen) and min_bp < @call_bp and not State.newline_before?(state) ->
        parse_call(state, lhs)

      # Bracket access: foo[...]
      # NOT if there's a newline before [ - that's a separate expression
      # Use <= to allow chaining: foo[:a][:b]
      State.at?(state, :lbracket) and min_bp <= @access_bp and not State.newline_before?(state) ->
        parse_access(state, lhs)

      # Anonymous function call: fun.(args)
      State.at?(state, :dot_call) and min_bp < @call_bp ->
        parse_anon_call(state, lhs)

      true ->
        {state, lhs}
    end
  end

  defp parse_call(state, lhs) do
    {state, lparen} = State.advance(state)
    lparen_meta = Ast.token_meta(lparen)
    {state, args} = parse_call_args(state)
    {state, closing} = State.expect(state, :rparen)

    ast =
      case lhs do
        {name, meta, nil} when is_atom(name) ->
          # Variable -> call
          call_meta = if closing, do: Ast.with_closing(meta, closing), else: meta
          {name, call_meta, args}

        {name, meta, context} when is_atom(name) and is_atom(context) ->
          # Already a call, wrap differently?
          call_meta = if closing, do: Ast.with_closing(meta, closing), else: meta
          {name, call_meta, args}

        {:., _dot_meta, _} = dot ->
          # Remote call
          call_meta = if closing, do: Ast.with_closing(lparen_meta, closing), else: lparen_meta
          {dot, call_meta, args}

        other ->
          # Expression call (rare)
          call_meta = if closing, do: Ast.with_closing(lparen_meta, closing), else: lparen_meta
          {{:., lparen_meta, [other]}, call_meta, args}
      end

    # Check for more postfix
    maybe_parse_postfix(state, ast, @call_bp)
  end

  defp parse_access(state, lhs) do
    {state, lbracket} = State.advance(state)
    meta = Ast.token_meta(lbracket)
    {state, key} = parse_expression(state, 0)
    {state, rbracket} = State.expect(state, :rbracket)

    # Add from_brackets and closing metadata (order: from_brackets, closing, line, column)
    bracket_meta =
      if rbracket do
        closing_meta = Ast.token_meta(rbracket)
        [{:from_brackets, true}, {:closing, closing_meta} | meta]
      else
        [{:from_brackets, true} | meta]
      end

    # Access is {{:., _, [Access, :get]}, _, [lhs, key]}
    access_ast = {{:., bracket_meta, [Access, :get]}, bracket_meta, [lhs, key]}
    maybe_parse_postfix(state, access_ast, @access_bp)
  end

  defp parse_anon_call(state, lhs) do
    {state, dot_call_token} = State.advance(state)
    meta = Ast.token_meta(dot_call_token)

    # Expect opening paren (should be there since we have dot_call_op)
    {state, _lparen} = State.expect(state, :lparen)
    {state, args} = parse_call_args(state)
    {state, closing} = State.expect(state, :rparen)

    # Anonymous call: {{:., meta, [lhs]}, call_meta, args}
    dot_ast = {:., meta, [lhs]}
    call_meta = if closing, do: Ast.with_closing(meta, closing), else: meta
    ast = {dot_ast, call_meta, args}

    maybe_parse_postfix(state, ast, @call_bp)
  end

  ## ATOMS AND IDENTIFIERS

  # Plain identifier: either variable or no-paren call
  # The tokenizer gives us :identifier when there's symmetric spacing around operators
  # (e.g., "a + b" has space before AND after +, so a is :identifier)
  # For asymmetric spacing ("foo +b"), the tokenizer gives us :op_identifier instead
  defp parse_identifier_or_call(state, allow_do) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = Ast.token_meta(token)

    # No-parens call: identifier followed by arg on same line (no newline)
    # IMPORTANT: We use starts_no_paren_arg_strict? which excludes + and -
    # The tokenizer handles the "foo +b" case via :op_identifier
    # So for plain :identifier, we only check for non-ambiguous arg starters
    if not State.newline_before?(state) and starts_no_paren_arg_strict?(state) do
      {state, args} = parse_no_paren_args(state, [])
      ast = Ast.call(token.value, meta, args)
      # No-paren calls can have trailing do blocks (like `schema "users" do`)
      # But only if allow_do is true
      if allow_do do
        maybe_parse_do_block(state, ast, meta)
      else
        {state, ast}
      end
    else
      # Plain variable
      ast = Ast.var(token.value, meta)
      {state, ast}
    end
  end

  # Op identifier: foo +b - identifier followed by operator-as-prefix
  # The tokenizer gives us :op_identifier when there's space before op but not after
  # This is definitively a no-parens call with first arg being a unary expression
  defp parse_op_identifier(state, allow_do) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = Ast.token_meta(token)

    # Parse args - the first one will start with a prefix operator
    {state, args} = parse_no_paren_args(state, [])
    ast = Ast.call(token.value, meta, args)

    if allow_do do
      maybe_parse_do_block(state, ast, meta)
    else
      {state, ast}
    end
  end

  # Paren identifier: foo( - identifier immediately followed by (
  # This can have a do block after the closing paren: foo(1) do ... end
  defp parse_paren_identifier(state, allow_do) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = Ast.token_meta(token)

    # Consume the lparen (tokenizer already verified it's there)
    {state, _} = State.advance(state)
    {state, args} = parse_call_args(state)
    {state, closing} = State.expect(state, :rparen)

    # Include closing metadata - this is preserved even if do block follows
    call_meta = if closing, do: Ast.with_closing(meta, closing), else: meta
    ast = Ast.call(token.value, call_meta, args)

    # Paren calls CAN have do blocks: foo(1) do ... end
    # But only if allow_do is true
    if allow_do do
      maybe_parse_do_block(state, ast, call_meta)
    else
      {state, ast}
    end
  end

  # Do identifier: foo do - identifier followed by do with no arguments
  # Behavior controlled by allow_do parameter:
  # - allow_do=true: parse as zero-arg call with do block (foo do ... end)
  # - allow_do=false: just return identifier, do belongs to outer construct
  defp parse_do_identifier(state, allow_do) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = Ast.token_meta(token)

    if allow_do and State.at?(state, :do) do
      # Parse as zero-arg call with do block: foo do ... end
      call_ast = {token.value, meta, []}
      maybe_parse_do_block(state, call_ast, meta)
    else
      # Return as plain variable - do belongs to outer construct (case/if/etc)
      ast = Ast.var(token.value, meta)
      {state, ast}
    end
  end

  # Bracket identifier: foo[ - identifier immediately followed by [
  # This is a variable with bracket access, NOT a call
  # The bracket access is handled in postfix (maybe_parse_postfix)
  defp parse_bracket_identifier(state) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = Ast.token_meta(token)

    # Return as variable - bracket access is handled in postfix parsing
    ast = Ast.var(token.value, meta)
    {state, ast}
  end

  # Check if current token can start a no-parens function argument (STRICT version)
  # This version EXCLUDES + and - because those are ambiguous with infix operators
  # The tokenizer handles the disambiguation via :op_identifier for "foo +b" patterns
  # Use this for plain :identifier tokens where we need to distinguish "a + b" from "a b"
  defp starts_no_paren_arg_strict?(state) do
    State.at_any?(state, [
      :string,
      :integer,
      :float,
      :atom,
      :alias,
      :identifier,
      :paren_identifier,
      :do_identifier,
      :bracket_identifier,
      :op_identifier,
      :charlist,
      :heredoc,
      :sigil,
      :lbracket,
      :lbrace,
      :map_open,
      :percent,
      :lparen,
      :langle,
      :fn,
      :capture_int,
      true,
      false,
      nil,
      :not,
      :&,
      :^,
      # NOTE: :+ and :- are NOT here - they're ambiguous with infix
      # The tokenizer tells us via :op_identifier when they should be prefix
      :!,
      :~~~
    ])
  end

  # Parse no-parens call arguments (similar to parse_keyword_call_args but simpler)
  defp parse_no_paren_args(state, acc) do
    # Stop at expression boundaries or do block
    if State.at_any?(state, [:do, :end, :else, :rescue, :catch, :after]) or
         State.at_end?(state) or State.newline_before?(state) do
      {state, Enum.reverse(acc)}
    else
      state = State.advance_push(state)
      {state, arg} = parse_call_arg(state)
      state = State.advance_pop!(state)
      acc = [arg | acc]

      if State.at?(state, :comma) and not State.at?(State.peek(state) && state, :do) do
        # Check if comma is followed by keyword (do:) which ends args
        next = State.peek(state)

        if next && next.kind == :kw_identifier do
          # Keyword arg - parse it and we're done
          {state, _comma} = State.advance(state)
          state = State.advance_push(state)
          {state, kw} = parse_trailing_keywords(state)
          state = State.advance_pop!(state)
          {state, Enum.reverse([kw | acc])}
        else
          {state, _comma} = State.advance(state)
          parse_no_paren_args(state, acc)
        end
      else
        {state, Enum.reverse(acc)}
      end
    end
  end

  # Parse trailing keyword arguments like `do: expr, else: expr`
  defp parse_trailing_keywords(state) do
    {state, pairs} = parse_keyword_pairs(state)
    {state, pairs}
  end

  # Check for and parse trailing do block, adding it to args
  defp maybe_parse_do_block(state, {name, meta, args}, original_meta) when is_list(args) do
    if State.at?(state, :do) do
      {state, do_token} = State.advance(state)
      {state, body} = parse_block_until(state, [:else, :end])

      {state, else_body, end_token} =
        if State.at?(state, :else) do
          {state, _} = State.advance(state)
          {state, else_body} = parse_block_until(state, [:end])
          {state, end_token} = State.expect(state, :end)
          {state, else_body, end_token}
        else
          {state, end_token} = State.expect(state, :end)
          {state, nil, end_token}
        end

      # Build the do block keyword list
      do_kw =
        if else_body do
          [do: body, else: else_body]
        else
          [do: body]
        end

      call_meta = Ast.with_do_end(original_meta, do_token, end_token)
      ast = {name, call_meta, args ++ [do_kw]}
      {state, ast}
    else
      {state, {name, meta, args}}
    end
  end

  defp maybe_parse_do_block(state, ast, _original_meta), do: {state, ast}

  # Parse keyword calls like raise, throw, unquote etc.
  defp parse_keyword_call(state, name) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = Ast.token_meta(token)

    # Check for call with parens
    if State.at?(state, :lparen) do
      {state, _} = State.advance(state)
      {state, args} = parse_call_args(state)
      {state, closing} = State.expect(state, :rparen)

      call_meta = if closing, do: Ast.with_closing(meta, closing), else: meta
      ast = Ast.call(name, call_meta, args)
      {state, ast}
    else
      # No parens - parse comma-separated arguments
      {state, args} = parse_keyword_call_args(state, [])
      ast = Ast.call(name, meta, args)
      {state, ast}
    end
  end

  defp parse_keyword_call_args(state, acc) do
    # Check for end of arguments - stop at expression boundaries
    if State.at_any?(state, Recovery.expression()) or State.at_end?(state) do
      {state, Enum.reverse(acc)}
    else
      # Use parse_call_arg to properly handle keyword arguments
      state = State.advance_push(state)
      {state, arg} = parse_call_arg(state)
      state = State.advance_pop!(state)

      # Keyword args return a keyword list, keep it as a single arg
      acc = [arg | acc]

      if State.at?(state, :comma) do
        {state, _comma} = State.advance(state)
        parse_keyword_call_args(state, acc)
      else
        {state, Enum.reverse(acc)}
      end
    end
  end

  defp parse_alias(state) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = Ast.token_meta(token)

    # Parse dotted aliases: Foo.Bar.Baz
    # Track last token for 'last' metadata
    {state, segments, last_token} = parse_alias_segments(state, [token.value], token)

    ast = Ast.alias_node(segments, meta, last_token)
    {state, ast}
  end

  defp parse_alias_segments(state, acc, last_token) do
    if State.at?(state, :dot) do
      # Peek ahead to see if next is an alias
      next = State.peek(state)

      if next && next.kind == :alias do
        {state, _dot} = State.advance(state)
        {state, alias_token} = State.advance(state)
        parse_alias_segments(state, acc ++ [alias_token.value], alias_token)
      else
        {state, acc, last_token}
      end
    else
      {state, acc, last_token}
    end
  end

  ## STRINGS

  defp parse_heredoc(state) do
    token = State.current(state)
    {state, _} = State.advance(state)
    # Heredocs are simple string values (already joined in lexer)
    {state, token.value}
  end

  defp parse_string(state) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = [{:delimiter, "\""} | Ast.token_meta(token)]

    case token.value do
      # Simple string - no interpolation
      [str] when is_binary(str) ->
        {state, str}

      # Multiple parts with possible interpolation
      parts when is_list(parts) ->
        has_interpolation? = Enum.any?(parts, &match?({{_, _, _}, {_, _, _}, _}, &1))

        if has_interpolation? do
          ast_parts = build_interpolation_parts(parts)
          {state, {:<<>>, meta, ast_parts}}
        else
          # Just string parts, join them
          joined =
            Enum.map_join(parts, fn
              str when is_binary(str) -> str
              _ -> ""
            end)

          {state, joined}
        end

      other ->
        {state, to_string(other)}
    end
  end

  defp build_interpolation_parts(parts) do
    Enum.map(parts, fn
      str when is_binary(str) ->
        str

      {{start_line, start_col, _}, {_end_line, end_col, _}, tokens} ->
        # Parse the interpolated tokens
        parsed_expr = parse_interpolation_tokens(tokens)

        # Build the interpolation AST structure
        dot_meta = [line: start_line, column: start_col]

        call_meta = [
          from_interpolation: true,
          closing: [line: start_line, column: end_col],
          line: start_line,
          column: start_col
        ]

        binary_meta = [line: start_line, column: start_col]
        type_meta = [line: start_line, column: start_col]

        to_string_call = {{:., dot_meta, [Kernel, :to_string]}, call_meta, [parsed_expr]}
        {:"::", type_meta, [to_string_call, {:binary, binary_meta, nil}]}
    end)
  end

  defp parse_interpolation_tokens(tokens) do
    # Convert raw tokens to our Token structs and parse
    normalized = Enum.map(tokens, &Hurricane.Token.from_raw/1)
    normalized = normalized ++ [Hurricane.Token.eof(0, 0)]

    inner_state = %State{
      tokens: normalized,
      pos: 0,
      errors: [],
      checkpoints: []
    }

    {_state, ast} = parse_expression(inner_state, 0)
    ast
  end

  defp parse_atom_unsafe(state) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = Ast.token_meta(token)
    call_meta = [{:delimiter, "\""} | meta]

    # Build the interpolated string
    ast_parts = build_interpolation_parts(token.value)

    # Wrap in {:erlang, :binary_to_atom} call
    binary_ast = {:<<>>, meta, ast_parts}
    dot_ast = {:., meta, [:erlang, :binary_to_atom]}
    ast = {dot_ast, call_meta, [binary_ast, :utf8]}

    {state, ast}
  end

  ## COLLECTIONS

  defp parse_list(state) do
    {state, _lbracket} = State.advance(state)
    {state, elements} = parse_collection_elements(state, :rbracket)
    {state, _rbracket} = State.expect(state, :rbracket)
    {state, elements}
  end

  defp parse_tuple(state) do
    {state, lbrace} = State.advance(state)
    meta = Ast.token_meta(lbrace)
    {state, elements} = parse_collection_elements(state, :rbrace)
    {state, _rbrace} = State.expect(state, :rbrace)
    ast = Ast.tuple(elements, meta)
    {state, ast}
  end

  defp parse_map(state) do
    {state, map_open} = State.advance(state)
    meta = Ast.token_meta(map_open)
    # Also consume the lbrace that follows %
    {state, _lbrace} = State.expect(state, :lbrace)
    {state, pairs} = parse_map_pairs(state)
    {state, rbrace} = State.expect(state, :rbrace)
    # Add closing metadata
    meta = if rbrace, do: Ast.with_closing(meta, rbrace), else: meta
    ast = Ast.map(pairs, meta)
    {state, ast}
  end

  defp parse_sigil(state) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = Ast.token_meta(token)

    # Extract sigil data from token value
    %{sigil_name: sigil_name, content: content, modifiers: modifiers, delimiter: delimiter} = token.value

    # Build metadata with delimiter
    meta = [{:delimiter, IO.chardata_to_string([delimiter])} | meta]

    # Build content as binary node
    content_ast = Ast.binary(content, Ast.token_meta(token))

    # Modifiers as charlist (or empty list)
    mods = if modifiers == [], do: [], else: modifiers

    ast = {sigil_name, meta, [content_ast, mods]}
    {state, ast}
  end

  defp parse_struct(state) do
    {state, percent_token} = State.advance(state)
    meta = Ast.token_meta(percent_token)

    # Parse the module - can be alias (Foo.Bar) or identifier (__MODULE__, var)
    {state, module_ast} =
      cond do
        State.at?(state, :alias) ->
          parse_alias(state)

        State.at?(state, :identifier) ->
          # Handle __MODULE__ and variable structs like %module{}
          token = State.current(state)
          {state, _} = State.advance(state)
          {state, Ast.var(token.value, Ast.token_meta(token))}

        true ->
          state = State.add_error(state, "expected module name after %")
          {state, Ast.error(State.current_meta(state))}
      end

    # Parse the map part - use lbrace position for map metadata
    {state, lbrace} = State.expect(state, :lbrace)
    {state, pairs} = parse_map_pairs(state)
    {state, rbrace} = State.expect(state, :rbrace)

    # Build struct AST: {:%, meta, [alias, {:%{}, map_meta, pairs}]}
    map_meta = Ast.token_meta(lbrace)
    map_meta = if rbrace, do: Ast.with_closing(map_meta, rbrace), else: map_meta
    map_ast = Ast.map(pairs, map_meta)
    ast = Ast.struct(module_ast, map_ast, meta)

    {state, ast}
  end

  defp parse_binary(state) do
    {state, langle} = State.advance(state)
    meta = Ast.token_meta(langle)
    {state, elements} = parse_collection_elements(state, :rangle)
    {state, rangle} = State.expect(state, :rangle)
    # Add closing metadata
    meta = if rangle, do: Ast.with_closing(meta, rangle), else: meta
    ast = Ast.binary(elements, meta)
    {state, ast}
  end

  defp parse_collection_elements(state, closing_kind) do
    if State.at?(state, closing_kind) or Recovery.at_recovery?(state, Recovery.collection()) do
      {state, []}
    else
      {state, element} = parse_collection_element(state)
      {state, rest} = parse_collection_elements_rest(state, closing_kind)
      # Only flatten keyword args (marked with :__kw__), not regular lists
      elements =
        case element do
          {:__kw__, pairs} -> pairs ++ rest
          single when not is_nil(single) -> [single | rest]
          nil -> rest
        end

      {state, elements}
    end
  end

  defp parse_collection_elements_rest(state, closing_kind) do
    case State.eat(state, :comma) do
      {:ok, state, _} ->
        if State.at?(state, closing_kind) or Recovery.at_recovery?(state, Recovery.collection()) do
          {state, []}
        else
          {state, element} = parse_collection_element(state)
          {state, rest} = parse_collection_elements_rest(state, closing_kind)
          # Only flatten keyword args (marked with :__kw__), not regular lists
          elements =
            case element do
              {:__kw__, pairs} -> pairs ++ rest
              single when not is_nil(single) -> [single | rest]
              nil -> rest
            end

          {state, elements}
        end

      {:error, state} ->
        {state, []}
    end
  end

  # Parse a single collection element (handles keyword pairs)
  defp parse_collection_element(state) do
    if State.at?(state, :kw_identifier) do
      # Wrap keyword args in marker so we can flatten them correctly
      {state, pairs} = parse_keyword_args(state)
      {state, {:__kw__, pairs}}
    else
      parse_expression(state, 0)
    end
  end

  defp parse_map_pairs(state) do
    if State.at?(state, :rbrace) or Recovery.at_recovery?(state, Recovery.collection()) do
      {state, []}
    else
      {state, pair} = parse_map_pair(state)
      {state, rest} = parse_map_pairs_rest(state)
      pairs = if pair, do: [pair | rest], else: rest
      {state, pairs}
    end
  end

  defp parse_map_pairs_rest(state) do
    case State.eat(state, :comma) do
      {:ok, state, _} ->
        # Comma consumed, now parse next pair
        if State.at?(state, :rbrace) or Recovery.at_recovery?(state, Recovery.collection()) do
          {state, []}
        else
          state = State.advance_push(state)
          {state, pair} = parse_map_pair(state)
          state = State.advance_pop!(state)
          {state, rest} = parse_map_pairs_rest(state)
          pairs = if pair, do: [pair | rest], else: rest
          {state, pairs}
        end

      {:error, state} ->
        {state, []}
    end
  end

  defp parse_map_pair(state) do
    # Check for keyword syntax: key: value
    if State.at?(state, :kw_identifier) do
      token = State.current(state)
      {state, _} = State.advance(state)
      {state, value} = parse_expression(state, 0)
      {state, {token.value, value}}
    else
      # Arrow syntax: key => value
      {state, key} = parse_expression(state, 0)

      if State.at?(state, :"=>") do
        {state, _} = State.advance(state)
        {state, value} = parse_expression(state, 0)
        {state, {key, value}}
      else
        # Just a key (error case)
        {state, {key, nil}}
      end
    end
  end

  ## CAPTURE ARGUMENTS (&1, &2, etc.)

  defp parse_capture_arg(state) do
    {state, capture_token} = State.advance(state)
    meta = Ast.token_meta(capture_token)

    # The next token should be the integer
    if State.at?(state, :integer) do
      int_token = State.current(state)
      {state, _} = State.advance(state)
      ast = {:&, meta, [int_token.value]}
      {state, ast}
    else
      # Error - expected integer after &
      state = State.add_error(state, "expected integer after &")
      {state, Ast.error(meta)}
    end
  end

  ## PARENTHESIZED EXPRESSION

  defp parse_parenthesized(state) do
    {state, lparen} = State.advance(state)
    {state, expr} = parse_expression(state, 0)
    {state, rparen} = State.expect(state, :rparen)

    # Add parens metadata to the expression
    expr = add_parens_meta(expr, lparen, rparen)
    {state, expr}
  end

  defp add_parens_meta({name, meta, args}, lparen, rparen) when is_atom(name) and is_list(meta) do
    parens_meta =
      [line: lparen.line, column: lparen.column] ++
        if rparen, do: [closing: [line: rparen.line, column: rparen.column]], else: []

    meta = Keyword.put(meta, :parens, parens_meta)
    {name, meta, args}
  end

  defp add_parens_meta(expr, _lparen, _rparen), do: expr

  ## ANONYMOUS FUNCTIONS

  defp parse_fn(state) do
    {state, fn_token} = State.advance(state)
    meta = Ast.token_meta(fn_token)

    {state, clauses} = parse_fn_clauses(state)
    {state, end_token} = State.expect(state, :end)

    # Add closing metadata for the end token
    meta = if end_token, do: Ast.with_closing(meta, end_token), else: meta
    ast = Ast.fn_expr(clauses, meta)
    {state, ast}
  end

  defp parse_fn_clauses(state) do
    {state, clause} = parse_fn_clause(state)
    {state, rest} = parse_fn_clauses_rest(state)
    {state, [clause | rest]}
  end

  defp parse_fn_clauses_rest(state) do
    if State.at?(state, :end) or State.at_end?(state) do
      {state, []}
    else
      {state, clause} = parse_fn_clause(state)
      {state, rest} = parse_fn_clauses_rest(state)
      {state, [clause | rest]}
    end
  end

  defp parse_fn_clause(state) do
    # Parse patterns (parameters)
    {state, patterns} = parse_fn_patterns(state)

    # Parse arrow
    {state, arrow_token} = State.expect(state, :->)
    meta = Ast.token_meta(arrow_token)

    # Parse body
    {state, body} = parse_fn_body(state)

    ast = Ast.stab(patterns, body, meta)
    {state, ast}
  end

  defp parse_fn_patterns(state) do
    if State.at?(state, :->) or Recovery.at_recovery?(state, Recovery.stab_clause()) do
      {state, []}
    else
      {state, pattern} = parse_expression(state, 0)
      {state, rest} = parse_fn_patterns_rest(state)
      patterns = if pattern, do: [pattern | rest], else: rest
      {state, patterns}
    end
  end

  defp parse_fn_patterns_rest(state) do
    case State.eat(state, :comma) do
      {:ok, state, _} ->
        if State.at?(state, :->) or Recovery.at_recovery?(state, Recovery.stab_clause()) do
          {state, []}
        else
          {state, pattern} = parse_expression(state, 0)
          {state, rest} = parse_fn_patterns_rest(state)
          patterns = if pattern, do: [pattern | rest], else: rest
          {state, patterns}
        end

      {:error, state} ->
        {state, []}
    end
  end

  defp parse_fn_body(state) do
    # Body continues until next clause or end
    {state, exprs} = parse_fn_body_exprs(state, [])
    ast = Ast.block(Enum.reverse(exprs), [])
    {state, ast}
  end

  defp parse_fn_body_exprs(state, acc) do
    if State.at?(state, :end) or State.at_end?(state) do
      {state, acc}
    else
      state = State.advance_push(state)
      {state, expr} = parse_expression(state, 0)
      state = State.advance_pop!(state)

      acc = if expr, do: [expr | acc], else: acc

      # Check for new clause AFTER parsing, not before
      if looks_like_new_clause?(state) do
        {state, acc}
      else
        parse_fn_body_exprs(state, acc)
      end
    end
  end

  defp looks_like_new_clause?(state) do
    # Heuristic: if we're at an identifier/literal and there's a -> coming up soon
    # This is imperfect but handles common cases
    token = State.current(state)

    if token && token.kind in [:identifier, :atom, :integer, :lbracket, :lbrace, :lparen] do
      # Look for -> in next few tokens
      peek_for_arrow(state, 0, 10)
    else
      false
    end
  end

  defp peek_for_arrow(_state, depth, max) when depth >= max, do: false

  defp peek_for_arrow(state, depth, max) do
    tokens = state.tokens
    pos = state.pos + depth

    case Enum.at(tokens, pos) do
      nil -> false
      %{kind: :->} -> true
      %{kind: :end} -> false
      _ -> peek_for_arrow(state, depth + 1, max)
    end
  end

  ## CALL ARGUMENTS

  defp parse_call_args(state) do
    if State.at?(state, :rparen) do
      {state, []}
    else
      {state, arg} = parse_call_arg(state)
      {state, rest} = parse_call_args_rest(state)
      args = if arg, do: [arg | rest], else: rest
      {state, args}
    end
  end

  defp parse_call_args_rest(state) do
    case State.eat(state, :comma) do
      {:ok, state, _} ->
        # Comma consumed, now parse next arg
        if State.at?(state, :rparen) do
          {state, []}
        else
          state = State.advance_push(state)
          {state, arg} = parse_call_arg(state)
          state = State.advance_pop!(state)
          {state, rest} = parse_call_args_rest(state)
          args = if arg, do: [arg | rest], else: rest
          {state, args}
        end

      {:error, state} ->
        {state, []}
    end
  end

  defp parse_call_arg(state) do
    # Check for keyword argument
    if State.at?(state, :kw_identifier) do
      parse_keyword_args(state)
    else
      parse_expression(state, 0)
    end
  end

  defp parse_keyword_args(state) do
    {state, pairs} = parse_keyword_pairs(state)
    {state, pairs}
  end

  # Parse implicit keyword list starting with kw_identifier (e.g., `only: [from: 2]`)
  # This is used when a keyword appears at expression position
  defp parse_implicit_keyword_list(state) do
    {state, pairs} = parse_keyword_pairs(state)
    {state, pairs}
  end

  defp parse_keyword_pairs(state) do
    if State.at?(state, :kw_identifier) do
      token = State.current(state)
      {state, _} = State.advance(state)
      {state, value} = parse_expression(state, 0)

      case State.eat(state, :comma) do
        {:ok, state, _} ->
          if State.at?(state, :kw_identifier) do
            {state, rest} = parse_keyword_pairs(state)

            case rest do
              pairs when is_list(pairs) -> {state, [{token.value, value} | pairs]}
              _ -> {state, [{token.value, value}]}
            end
          else
            {state, [{token.value, value}]}
          end

        {:error, state} ->
          {state, [{token.value, value}]}
      end
    else
      {state, []}
    end
  end

  ## SPECIAL FORMS

  # case expr do clauses end
  defp parse_case(state) do
    {state, case_token} = State.advance(state)
    meta = Ast.token_meta(case_token)

    # Parse the expression being matched
    # Use allow_do: false because the `do` belongs to case, not the expression
    {state, expr} = parse_expression(state, 0, allow_do: false)

    # Parse do block with stab clauses
    {state, clauses, do_token, end_token} = parse_stab_block(state)

    meta = Ast.with_do_end(meta, do_token, end_token)
    ast = {:case, meta, [expr, [do: clauses]]}
    {state, ast}
  end

  # cond do clauses end
  defp parse_cond(state) do
    {state, cond_token} = State.advance(state)
    meta = Ast.token_meta(cond_token)

    {state, clauses, do_token, end_token} = parse_stab_block(state)

    meta = Ast.with_do_end(meta, do_token, end_token)
    ast = {:cond, meta, [[do: clauses]]}
    {state, ast}
  end

  # if expr do body else else_body end
  defp parse_if(state) do
    {state, if_token} = State.advance(state)
    meta = Ast.token_meta(if_token)

    # Check for parenthesized form: if(cond, do: x, else: y)
    if State.at?(state, :lparen) do
      {state, _} = State.advance(state)
      {state, condition} = parse_expression(state, 0)
      {state, _} = State.expect(state, :comma)
      {state, kw_pairs} = parse_keyword_pairs(state)
      {state, closing} = State.expect(state, :rparen)
      meta = if closing, do: Ast.with_closing(meta, closing), else: meta
      ast = {:if, meta, [condition, kw_pairs]}
      {state, ast}
    else
      # Parse condition - allow_do: false because do belongs to if
      {state, condition} = parse_expression(state, 0, allow_do: false)

      # Check for do block or keyword form
      if State.at?(state, :do) do
        {state, do_token} = State.advance(state)
        {state, body} = parse_block_until(state, [:else, :end])

        {state, else_body, end_token} =
          if State.at?(state, :else) do
            {state, _} = State.advance(state)
            {state, else_body} = parse_block_until(state, [:end])
            {state, end_token} = State.expect(state, :end)
            {state, else_body, end_token}
          else
            {state, end_token} = State.expect(state, :end)
            {state, nil, end_token}
          end

        meta = Ast.with_do_end(meta, do_token, end_token)
        body_kw = if else_body, do: [do: body, else: else_body], else: [do: body]
        ast = {:if, meta, [condition, body_kw]}
        {state, ast}
      else
        # Keyword form: if cond, do: body, else: else_body
        {state, _} = State.expect(state, :comma)
        {state, kw_pairs} = parse_keyword_pairs(state)
        ast = {:if, meta, [condition, kw_pairs]}
        {state, ast}
      end
    end
  end

  defp parse_unless(state) do
    {state, unless_token} = State.advance(state)
    meta = Ast.token_meta(unless_token)

    # allow_do: false because do belongs to unless
    {state, condition} = parse_expression(state, 0, allow_do: false)

    if State.at?(state, :do) do
      {state, do_token} = State.advance(state)
      {state, body} = parse_block_until(state, [:else, :end])

      {state, else_body, end_token} =
        if State.at?(state, :else) do
          {state, _} = State.advance(state)
          {state, else_body} = parse_block_until(state, [:end])
          {state, end_token} = State.expect(state, :end)
          {state, else_body, end_token}
        else
          {state, end_token} = State.expect(state, :end)
          {state, nil, end_token}
        end

      meta = Ast.with_do_end(meta, do_token, end_token)
      body_kw = if else_body, do: [do: body, else: else_body], else: [do: body]
      ast = {:unless, meta, [condition, body_kw]}
      {state, ast}
    else
      {state, _} = State.expect(state, :comma)
      {state, kw_pairs} = parse_keyword_pairs(state)
      ast = {:unless, meta, [condition, kw_pairs]}
      {state, ast}
    end
  end

  # with clauses do body else else_clauses end
  defp parse_with(state) do
    {state, with_token} = State.advance(state)
    meta = Ast.token_meta(with_token)

    # Parse with clauses (pattern <- expr, ...)
    {state, clauses} = parse_with_clauses(state)

    # Parse do block
    {state, do_token} = State.expect(state, :do)
    {state, body} = parse_block_until(state, [:else, :end])

    {state, else_clauses, end_token} =
      if State.at?(state, :else) do
        {state, _} = State.advance(state)
        {state, else_clauses, _, end_token} = parse_stab_block_inner(state)
        {state, else_clauses, end_token}
      else
        {state, end_token} = State.expect(state, :end)
        {state, nil, end_token}
      end

    meta = Ast.with_do_end(meta, do_token, end_token)
    body_kw = if else_clauses, do: [do: body, else: else_clauses], else: [do: body]
    ast = {:with, meta, clauses ++ [body_kw]}
    {state, ast}
  end

  defp parse_with_clauses(state) do
    {state, clause} = parse_with_clause(state)

    case State.eat(state, :comma) do
      {:ok, state, _} ->
        if State.at?(state, :do) or State.at?(state, :kw_identifier) do
          {state, [clause]}
        else
          {state, rest} = parse_with_clauses(state)
          {state, [clause | rest]}
        end

      {:error, state} ->
        {state, [clause]}
    end
  end

  defp parse_with_clause(state) do
    # Can be pattern <- expr or just expr (for guards)
    # allow_do: false because the do belongs to with, not the clause
    {state, expr} = parse_expression(state, 0, allow_do: false)
    {state, expr}
  end

  # try do body rescue/catch/after end
  defp parse_try(state) do
    {state, try_token} = State.advance(state)
    meta = Ast.token_meta(try_token)

    {state, do_token} = State.expect(state, :do)
    {state, body} = parse_block_until(state, [:rescue, :catch, :else, :after, :end])

    # Parse optional sections
    {state, sections} = parse_try_sections(state, do: body)

    {state, end_token} = State.expect(state, :end)

    meta = Ast.with_do_end(meta, do_token, end_token)
    ast = {:try, meta, [sections]}
    {state, ast}
  end

  defp parse_try_sections(state, acc) do
    cond do
      State.at?(state, :rescue) ->
        state = State.advance_push(state)
        {state, _} = State.advance(state)
        # Don't use parse_stab_block_inner - it expects :end
        # parse_stab_clauses stops at :catch/:after/:end
        {state, clauses} = parse_stab_clauses(state, [])
        state = State.advance_pop!(state)
        # Append to end to preserve order: do, rescue, catch, else, after
        parse_try_sections(state, acc ++ [rescue: clauses])

      State.at?(state, :catch) ->
        state = State.advance_push(state)
        {state, _} = State.advance(state)
        {state, clauses} = parse_stab_clauses(state, [])
        state = State.advance_pop!(state)
        parse_try_sections(state, acc ++ [catch: clauses])

      State.at?(state, :else) ->
        state = State.advance_push(state)
        {state, _} = State.advance(state)
        {state, clauses} = parse_stab_clauses(state, [])
        state = State.advance_pop!(state)
        parse_try_sections(state, acc ++ [else: clauses])

      State.at?(state, :after) ->
        state = State.advance_push(state)
        {state, _} = State.advance(state)
        {state, body} = parse_block_until(state, [:end])
        state = State.advance_pop!(state)
        parse_try_sections(state, acc ++ [after: body])

      true ->
        {state, acc}
    end
  end

  # receive do clauses after timeout -> body end
  defp parse_receive(state) do
    {state, receive_token} = State.advance(state)
    meta = Ast.token_meta(receive_token)

    {state, do_token} = State.expect(state, :do)
    # Use parse_stab_clauses directly - it stops at :after/:end
    {state, clauses} = parse_stab_clauses(state, [])

    {state, after_clause, end_token} =
      if State.at?(state, :after) do
        {state, _} = State.advance(state)
        # After section also uses stab clauses (timeout -> body)
        {state, after_clauses} = parse_stab_clauses(state, [])
        {state, end_token} = State.expect(state, :end)
        {state, after_clauses, end_token}
      else
        {state, end_token} = State.expect(state, :end)
        {state, nil, end_token}
      end

    meta = Ast.with_do_end(meta, do_token, end_token)
    body_kw = if after_clause, do: [do: clauses, after: after_clause], else: [do: clauses]
    ast = {:receive, meta, [body_kw]}
    {state, ast}
  end

  # for generators, filters, into: ..., do: body
  defp parse_for(state) do
    {state, for_token} = State.advance(state)
    meta = Ast.token_meta(for_token)

    {state, clauses} = parse_for_clauses(state)

    # Check for do block or keyword
    {state, body_kw, meta} =
      if State.at?(state, :do) do
        {state, do_token} = State.advance(state)
        {state, body} = parse_block_until(state, [:end])
        {state, end_token} = State.expect(state, :end)
        updated_meta = Ast.with_do_end(meta, do_token, end_token)
        # Wrap in list so it stays as single keyword list element when appended
        {state, [[do: body]], updated_meta}
      else
        # Already have keyword pairs in clauses
        {state, [], meta}
      end

    ast = {:for, meta, clauses ++ body_kw}
    {state, ast}
  end

  defp parse_for_clauses(state) do
    # allow_do: false because the do belongs to for, not the clause
    {state, clause} = parse_expression(state, 0, allow_do: false)

    case State.eat(state, :comma) do
      {:ok, state, _} ->
        if State.at?(state, :do) or State.at?(state, :kw_identifier) do
          # Check if it's do: keyword - keep as single keyword list element
          if State.at?(state, :kw_identifier) do
            {state, kw} = parse_keyword_pairs(state)
            # kw is a keyword list like [do: body], keep it as a single arg
            {state, [clause, kw]}
          else
            {state, [clause]}
          end
        else
          {state, rest} = parse_for_clauses(state)
          {state, [clause | rest]}
        end

      {:error, state} ->
        {state, [clause]}
    end
  end

  # quote do body end
  defp parse_quote(state) do
    {state, quote_token} = State.advance(state)
    meta = Ast.token_meta(quote_token)

    # Check for options
    {state, opts} =
      if State.at?(state, :do) do
        {state, []}
      else
        {state, opts} = parse_keyword_pairs(state)
        {state, opts}
      end

    {state, do_token} = State.expect(state, :do)
    {state, body} = parse_block_until(state, [:end])
    {state, end_token} = State.expect(state, :end)

    meta = Ast.with_do_end(meta, do_token, end_token)
    ast = {:quote, meta, opts ++ [[do: body]]}
    {state, ast}
  end

  ## HELPER: PARSE BLOCK WITH STAB CLAUSES

  defp parse_stab_block(state) do
    {state, do_token} = State.expect(state, :do)
    {state, clauses, _, end_token} = parse_stab_block_inner(state)
    {state, clauses, do_token, end_token}
  end

  defp parse_stab_block_inner(state) do
    {state, clauses} = parse_stab_clauses(state, [])
    {state, end_token} = State.expect(state, :end)
    {state, clauses, nil, end_token}
  end

  defp parse_stab_clauses(state, acc) do
    # Stop at block terminators or definition keywords (for recovery)
    if State.at?(state, :end) or State.at?(state, :else) or
         State.at?(state, :rescue) or State.at?(state, :catch) or
         State.at?(state, :after) or State.at_end?(state) or
         State.at?(state, :def) or State.at?(state, :defp) or
         State.at?(state, :defmacro) or State.at?(state, :defmacrop) or
         State.at?(state, :defmodule) do
      {state, Enum.reverse(acc)}
    else
      state = State.advance_push(state)
      {state, clause} = parse_stab_clause(state)
      state = State.advance_pop!(state)

      acc = if clause, do: [clause | acc], else: acc
      parse_stab_clauses(state, acc)
    end
  end

  defp parse_stab_clause(state) do
    # Parse pattern(s)
    {state, patterns} = parse_stab_patterns(state)

    # Expect ->
    {state, arrow_token} = State.expect(state, :->)
    meta = Ast.token_meta(arrow_token)

    # Parse body
    {state, body} = parse_stab_body(state)

    ast = {:->, meta, [patterns, body]}
    {state, ast}
  end

  defp parse_stab_patterns(state) do
    {state, pattern} = parse_expression(state, 0)

    case State.eat(state, :comma) do
      {:ok, state, _} ->
        if State.at?(state, :->) do
          {state, [pattern]}
        else
          {state, rest} = parse_stab_patterns(state)
          {state, [pattern | rest]}
        end

      {:error, state} ->
        {state, [pattern]}
    end
  end

  defp parse_stab_body(state) do
    {state, exprs} = parse_stab_body_exprs(state, [])
    ast = Ast.block(Enum.reverse(exprs), [])
    {state, ast}
  end

  defp parse_stab_body_exprs(state, acc) do
    # Stop at clause/block terminators, definition keywords (for recovery), or stab arrow
    # Note: We also stop at :-> because if we hit an arrow, the previous "expression"
    # was actually a pattern for a new stab clause, not part of this body
    if State.at?(state, :end) or State.at?(state, :else) or
         State.at?(state, :rescue) or State.at?(state, :catch) or
         State.at?(state, :after) or State.at_end?(state) or
         State.at?(state, :->) or
         State.at?(state, :def) or State.at?(state, :defp) or
         State.at?(state, :defmacro) or State.at?(state, :defmacrop) or
         State.at?(state, :defmodule) do
      {state, acc}
    else
      # Check for new stab clause BEFORE parsing the expression
      # If we see what looks like a new clause (pattern -> ...), stop here
      if looks_like_new_stab_clause?(state) do
        {state, acc}
      else
        state = State.advance_push(state)
        {state, expr} = parse_expression(state, 0)
        state = State.advance_pop!(state)

        acc = if expr, do: [expr | acc], else: acc
        parse_stab_body_exprs(state, acc)
      end
    end
  end

  defp looks_like_new_stab_clause?(state) do
    # A new stab clause typically:
    # 1. Starts on a new line (has newline before current token)
    # 2. Has a pattern before the arrow on the same or next line
    #
    # The key challenge is distinguishing:
    #   body_expr           <- end of clause body
    #   pattern -> expr     <- new clause
    # from:
    #   body_expr           <- multi-line expression in body
    #   continuation        <- still same expression
    #
    # The peek_for_arrow_depth function checks that any arrow found
    # is within 1 line of the start position, which handles this well.
    case {State.prev(state), State.current(state)} do
      {%{line: prev_line}, %{line: curr_line}} when curr_line > prev_line ->
        # Search with reasonable depth - the arrow line check will
        # prevent false positives from distant arrows
        peek_for_arrow_simple(state, 0, 30)

      _ ->
        false
    end
  end

  # Look for arrow within a short distance, tracking bracket depth
  # to allow commas inside tuple patterns like {:ok, x} ->
  # Also ensure the arrow is on a nearby line (not across a blank line)
  defp peek_for_arrow_simple(state, depth, max) do
    current = State.current(state)
    start_line = if current, do: current.line, else: 0
    peek_for_arrow_depth(state, depth, max, 0, start_line)
  end

  defp peek_for_arrow_depth(_state, depth, max, _bracket_depth, _start_line) when depth >= max,
    do: false

  defp peek_for_arrow_depth(state, depth, max, bracket_depth, start_line) do
    tokens = state.tokens
    pos = state.pos + depth

    case Enum.at(tokens, pos) do
      nil ->
        false

      # Found arrow at top level (outside any brackets)
      # Also check it's on the same line or adjacent line (no blank line gap)
      %{kind: :->, line: arrow_line} when bracket_depth == 0 ->
        arrow_line - start_line <= 1

      %{kind: :->} ->
        peek_for_arrow_depth(state, depth + 1, max, bracket_depth, start_line)

      # Terminators - stop searching
      %{kind: :end} ->
        false

      %{kind: :else} ->
        false

      %{kind: :rescue} ->
        false

      %{kind: :catch} ->
        false

      %{kind: :after} ->
        false

      # Track bracket depth
      %{kind: :lbrace} ->
        peek_for_arrow_depth(state, depth + 1, max, bracket_depth + 1, start_line)

      %{kind: :rbrace} ->
        peek_for_arrow_depth(state, depth + 1, max, max(0, bracket_depth - 1), start_line)

      %{kind: :lbracket} ->
        peek_for_arrow_depth(state, depth + 1, max, bracket_depth + 1, start_line)

      %{kind: :rbracket} ->
        peek_for_arrow_depth(state, depth + 1, max, max(0, bracket_depth - 1), start_line)

      %{kind: :lparen} ->
        peek_for_arrow_depth(state, depth + 1, max, bracket_depth + 1, start_line)

      %{kind: :rparen} ->
        peek_for_arrow_depth(state, depth + 1, max, max(0, bracket_depth - 1), start_line)

      # Note: We allow comma at top level because catch clauses use :kind, pattern -> body
      # The arrow line check prevents false positives from distant commas

      # Keywords that have their own stab clauses - stop searching
      # The -> inside these belongs to their inner clauses, not outer pattern
      %{kind: :case} ->
        false

      %{kind: :cond} ->
        false

      %{kind: :fn} ->
        false

      %{kind: :receive} ->
        false

      _ ->
        peek_for_arrow_depth(state, depth + 1, max, bracket_depth, start_line)
    end
  end

  ## HELPER: PARSE BLOCK UNTIL TERMINATOR

  defp parse_block_until(state, terminators) do
    {state, exprs} = parse_block_until_exprs(state, terminators, [])
    ast = Ast.block(Enum.reverse(exprs), [])
    {state, ast}
  end

  defp parse_block_until_exprs(state, terminators, acc) do
    if State.at_any?(state, terminators) or State.at_end?(state) do
      {state, acc}
    else
      state = State.advance_push(state)
      {state, expr} = parse_expression(state, 0)
      state = State.advance_pop!(state)

      acc = if expr, do: [expr | acc], else: acc
      parse_block_until_exprs(state, terminators, acc)
    end
  end
end
