defmodule Hurricane.Parser do
  @moduledoc """
  Hybrid Pratt + recursive descent parser.

  ## Entry Points

  - `parse/1` - Parse source code, returns `{:ok, ast}` or `{:ok, ast, errors}`
  - `parse!/1` - Parse source code, returns AST directly

  ## How It Works

  **Top-level:** loops over expressions, dispatching to specialized handlers
  for `defmodule`, `def`, etc., or `parse_expression` for everything else.

  **Expression parsing (Pratt core):**
  `parse_expression/2` -> `parse_prefix/2` -> `parse_infix_loop/3`

  Complex forms (`case`, `fn`, etc.) use recursive descent within `parse_prefix`,
  returning complete AST nodes to the Pratt loop.

  ## Binding Power

  Higher binding power = tighter binding.
  Left-associative: right BP = left BP + 1
  Right-associative: left BP = right BP + 1
  """

  alias Hurricane.Ast
  alias Hurricane.Lexer
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
    # Comprehension, with (left-associative)
    :<- => {16, 17},
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

    # Pipe and arrow operators (left-associative)
    :|> => {29, 30},
    :~>> => {29, 30},
    :<<~ => {29, 30},
    :~> => {29, 30},
    :<~ => {29, 30},
    :<~> => {29, 30},
    :"<|>" => {29, 30},
    :<<< => {29, 30},
    :>>> => {29, 30},

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
    # `!` and `not` have low bp so `!a in b` parses as `!(a in b)`, not `(!a) in b`
    :! => 30,
    :not => 30,
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
  Parse source code into an Elixir AST.

  Returns `{:ok, ast}` on success, `{:ok, ast, errors}` for code with syntax errors.
  """
  def parse(source) when is_binary(source) do
    with {:ok, tokens} <- Lexer.tokenize(source) do
      state = State.new(tokens)
      {state, ast} = parse_top_level(state)

      case State.errors(state) do
        [] -> {:ok, ast}
        errors -> {:ok, ast, errors}
      end
    end
  end

  @doc """
  Parse source code, returning AST directly.

  Raises only on internal parser bugs, not on syntax errors in source.
  """
  def parse!(source) when is_binary(source) do
    case parse(source) do
      {:ok, ast} -> ast
      {:ok, ast, _errors} -> ast
      {:error, reason} -> raise "Parser failed: #{inspect(reason)}"
    end
  end

  # Parse the entire source file as a top-level expression or block.
  defp parse_top_level(state) do
    {state, exprs} = parse_top_level_items(state, [])

    ast =
      case exprs do
        [] -> nil
        [single] -> single
        multiple -> Ast.block(multiple, [])
      end

    {state, ast}
  end

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

  ## TOP LEVEL PARSING

  defp parse_top_level_items(state, acc) do
    # Skip any semicolons (expression separators)
    state = skip_semicolons(state)

    if State.at_end?(state) do
      {state, Enum.reverse(acc)}
    else
      state = State.advance_push(state)
      {state, expr} = parse_top_level_item(state)
      state = State.advance_pop!(state)

      acc = if expr != nil, do: [expr | acc], else: acc
      parse_top_level_items(state, acc)
    end
  end

  defp skip_semicolons(state) do
    if State.at?(state, :semicolon) do
      {state, _} = State.advance(state)
      skip_semicolons(state)
    else
      state
    end
  end

  defp parse_top_level_item(state) do
    # Check if next token is ( - if so, this is desugared call syntax like defmodule(...)
    # which should be parsed as a regular expression, not special form
    next = State.peek(state)
    is_paren_call = next && next.kind == :lparen

    cond do
      State.at?(state, :defmodule) and not is_paren_call ->
        parse_defmodule(state)

      State.at?(state, :def) and not is_paren_call ->
        parse_def(state, :def)

      State.at?(state, :defp) and not is_paren_call ->
        parse_def(state, :defp)

      State.at?(state, :defmacro) and not is_paren_call ->
        parse_def(state, :defmacro)

      State.at?(state, :defmacrop) and not is_paren_call ->
        parse_def(state, :defmacrop)

      State.at?(state, :defguard) and not is_paren_call ->
        parse_def(state, :defguard)

      State.at?(state, :defguardp) and not is_paren_call ->
        parse_def(state, :defguardp)

      State.at?(state, :defdelegate) and not is_paren_call ->
        parse_defdelegate(state)

      # Stray :end tokens from incomplete structures - skip with error
      State.at?(state, :end) ->
        state = State.add_error(state, "unexpected end")
        {state, _} = State.advance(state)
        {state, nil}

      # Stray :-> tokens from incomplete clauses - skip with error
      State.at?(state, :->) ->
        state = State.add_error(state, "unexpected ->")
        {state, _} = State.advance(state)
        {state, nil}

      # Orphan closing delimiters (from Toxic's error recovery) - skip with error
      State.at_any?(state, [:rparen, :rbracket, :rbrace, :rangle]) ->
        token = State.current(state)
        state = State.add_error(state, "unexpected #{inspect(token.kind)}")
        {state, _} = State.advance(state)
        {state, nil}

      # Stray block keywords from incomplete structures - skip with error
      State.at_any?(state, [:do, :rescue, :catch, :else, :after]) ->
        token = State.current(state)
        state = State.add_error(state, "unexpected #{token.kind}")
        {state, _} = State.advance(state)
        {state, nil}

      # Any other token: try to parse as expression
      true ->
        parse_expression(state)
    end
  end

  ## MODULE DEFINITION

  defp parse_defmodule(state) do
    {state, defmodule_token} = State.expect(state, :defmodule)
    meta = Ast.token_meta(defmodule_token)

    # Parse module alias
    {state, alias_ast} = parse_module_alias(state)

    # Parse do block
    {state, body, do_token, end_token} = parse_do_block(state, &parse_module_body/1)

    meta = Ast.with_do_end(meta, do_token, end_token)
    ast = Ast.defmodule(alias_ast, body, meta)

    {state, ast}
  end

  defp parse_module_alias(state) do
    if State.at?(state, :alias) do
      token = State.current(state)
      {state, _} = State.advance(state)
      meta = Ast.token_meta(token)

      # Parse dotted aliases: Foo.Bar.Baz
      {state, segments, last_token} = parse_module_alias_segments(state, [token.value], token)

      ast = Ast.alias_node(segments, meta, last_token)
      {state, ast}
    else
      # Error: expected module name
      state = State.add_error(state, "expected module name")
      {state, Ast.error(State.current_meta(state))}
    end
  end

  defp parse_module_alias_segments(state, acc, last_token) do
    if State.at?(state, :dot) do
      # Peek ahead to see if next is an alias
      next = State.peek(state)

      if next && next.kind == :alias do
        {state, _dot} = State.advance(state)
        {state, alias_token} = State.advance(state)
        parse_module_alias_segments(state, acc ++ [alias_token.value], alias_token)
      else
        {state, acc, last_token}
      end
    else
      {state, acc, last_token}
    end
  end

  ## MODULE BODY

  defp parse_module_body(state) do
    {state, items} = parse_module_body_items(state, [])
    # Empty module bodies must be {:__block__, [], []} not nil
    ast =
      case Enum.reverse(items) do
        [] -> {:__block__, [], []}
        exprs -> Ast.block(exprs, [])
      end

    {state, ast}
  end

  defp parse_module_body_items(state, acc) do
    # Skip any semicolons (expression separators)
    state = skip_semicolons(state)

    cond do
      State.at?(state, :end) or State.at_end?(state) ->
        {state, acc}

      Recovery.at_recovery?(state, Recovery.block_body()) ->
        {state, acc}

      true ->
        state = State.advance_push(state)
        {state, item} = parse_module_body_item(state)
        state = State.advance_pop!(state)

        # Add end_of_expression metadata if followed by newline
        item = add_end_of_expression(state, item)

        acc = if item, do: [item | acc], else: acc
        parse_module_body_items(state, acc)
    end
  end

  defp parse_module_body_item(state) do
    # Check if next token is ( - if so, this is desugared call syntax
    next = State.peek(state)
    is_paren_call = next && next.kind == :lparen

    cond do
      State.at?(state, :def) and not is_paren_call -> parse_def(state, :def)
      State.at?(state, :defp) and not is_paren_call -> parse_def(state, :defp)
      State.at?(state, :defmacro) and not is_paren_call -> parse_def(state, :defmacro)
      State.at?(state, :defmacrop) and not is_paren_call -> parse_def(state, :defmacrop)
      State.at?(state, :defguard) and not is_paren_call -> parse_def(state, :defguard)
      State.at?(state, :defguardp) and not is_paren_call -> parse_def(state, :defguardp)
      State.at?(state, :defdelegate) and not is_paren_call -> parse_defdelegate(state)
      State.at?(state, :defmodule) and not is_paren_call -> parse_defmodule(state)
      # @ goes through parse_expression for proper infix handling (e.g., @foo + 1)
      State.at?(state, :use) and not is_paren_call -> parse_directive(state, :use)
      State.at?(state, :import) and not is_paren_call -> parse_directive(state, :import)
      State.at?(state, :alias_directive) and not is_paren_call -> parse_directive(state, :alias)
      State.at?(state, :require) and not is_paren_call -> parse_directive(state, :require)
      # Module attributes: @doc, @moduledoc, @spec, @type, etc.
      # Parse as expression (@ is a prefix operator) - must come before recovery check
      State.at?(state, :@) -> parse_expression(state)
      Recovery.at_recovery?(state, Recovery.module_body()) -> {state, nil}
      # Any other token: try to parse as expression
      true -> parse_expression(state)
    end
  end

  ## FUNCTION DEFINITION

  defp parse_def(state, kind) do
    {state, def_token} = State.advance(state)
    meta = Ast.token_meta(def_token)

    # Parse function name
    {state, name_ast} = parse_function_name(state)

    # Parse parameters if present
    {state, call_ast} =
      if State.at?(state, :lparen) do
        {state, _lparen} = State.advance(state)
        {state, params} = parse_def_params(state)
        {state, closing_token} = State.expect(state, :rparen)

        call_meta = name_ast_meta(name_ast)

        call_meta =
          if closing_token, do: Ast.with_closing(call_meta, closing_token), else: call_meta

        case name_ast do
          {name, _meta, nil} when is_atom(name) ->
            {state, Ast.call(name, call_meta, params)}

          _ ->
            {state, name_ast}
        end
      else
        {state, name_ast}
      end

    # Parse guard if present
    {state, call_ast} =
      if State.at?(state, :when) do
        {state, when_token} = State.advance(state)
        {state, guard} = parse_guard_expression(state)
        when_meta = Ast.token_meta(when_token)
        guarded = Ast.binary_op(:when, when_meta, call_ast, guard)
        {state, guarded}
      else
        {state, call_ast}
      end

    # defguard/defguardp have no body - just the when clause
    if kind in [:defguard, :defguardp] do
      ast = {kind, meta, [call_ast]}
      {state, ast}
    else
      # Parse body (do block or comma do:)
      cond do
        State.at?(state, :do) ->
          {state, body, do_token, end_token} = parse_do_block(state, &parse_block_body/1)
          meta = Ast.with_do_end(meta, do_token, end_token)
          ast = Ast.def_node(kind, call_ast, body, meta)
          {state, ast}

        State.at?(state, :comma) ->
          {state, _comma} = State.advance(state)
          {state, body, do_token, end_token} = parse_keyword_do(state)
          meta = Ast.with_do_end(meta, do_token, end_token)
          ast = Ast.def_node(kind, call_ast, body, meta)
          {state, ast}

        true ->
          # No body - this is a function head (e.g., declaring default args)
          # Just return {kind, meta, [call_ast]} without body
          ast = {kind, meta, [call_ast]}
          {state, ast}
      end
    end
  end

  # defdelegate name(args), to: Module, as: :name
  defp parse_defdelegate(state) do
    {state, delegate_token} = State.advance(state)
    meta = Ast.token_meta(delegate_token)

    # Parse the call (function name with params)
    {state, call_ast} = parse_expression(state, 0)

    # Parse comma and keyword options
    {state, opts} =
      if State.at?(state, :comma) do
        {state, _} = State.advance(state)
        {state, kw_pairs} = parse_defdelegate_opts(state)
        {state, kw_pairs}
      else
        {state, []}
      end

    ast = {:defdelegate, meta, [call_ast, opts]}
    {state, ast}
  end

  # Parse keyword pairs (to:, as:)
  defp parse_defdelegate_opts(state) do
    if State.at?(state, :kw_identifier) do
      token = State.current(state)
      {state, _} = State.advance(state)
      {state, value} = parse_expression(state, 0)

      case State.eat(state, :comma) do
        {:ok, state, _} ->
          if State.at?(state, :kw_identifier) do
            {state, rest} = parse_defdelegate_opts(state)
            {state, [{token.value, value} | rest]}
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

  defp parse_function_name(state) do
    cond do
      # Plain identifier: def foo, def foo()
      State.at?(state, :identifier) ->
        token = State.current(state)
        {state, _} = State.advance(state)
        {state, Ast.var(token.value, Ast.token_meta(token))}

      # Paren identifier: def foo() - identifier immediately followed by (
      State.at?(state, :paren_identifier) ->
        token = State.current(state)
        {state, _} = State.advance(state)
        {state, Ast.var(token.value, Ast.token_meta(token))}

      # Do identifier: def foo do - identifier followed by do (zero-arg function)
      State.at?(state, :do_identifier) ->
        token = State.current(state)
        {state, _} = State.advance(state)
        {state, Ast.var(token.value, Ast.token_meta(token))}

      true ->
        state = State.add_error(state, "expected function name")
        {state, Ast.error(State.current_meta(state))}
    end
  end

  defp name_ast_meta({_name, meta, _args}) do
    meta
  end

  ## DEFINITION PARAMETERS

  defp parse_def_params(state) do
    if State.at?(state, :rparen) or Recovery.at_recovery?(state, Recovery.params()) do
      {state, []}
    else
      {state, param} = parse_def_param(state)
      {state, rest} = parse_def_params_rest(state)
      {state, [param | rest]}
    end
  end

  defp parse_def_params_rest(state) do
    case State.eat(state, :comma) do
      {:ok, state, _} ->
        if Recovery.at_recovery?(state, Recovery.params()) do
          {state, []}
        else
          {state, param} = parse_def_param(state)
          {state, rest} = parse_def_params_rest(state)
          {state, [param | rest]}
        end

      {:error, state} ->
        {state, []}
    end
  end

  defp parse_def_param(state) do
    # Parameters can be any pattern - use expression parser
    if Recovery.at_recovery?(state, Recovery.params()) do
      {state, Ast.error(State.current_meta(state))}
    else
      parse_expression(state)
    end
  end

  ## GUARDS

  defp parse_guard_expression(state) do
    parse_expression(state)
  end

  ## DO BLOCKS

  defp parse_do_block(state, body_parser) do
    {state, do_token} = State.expect(state, :do)

    {state, body} = body_parser.(state)

    {state, end_token} = State.expect(state, :end)

    {state, Ast.do_block(body), do_token, end_token}
  end

  defp parse_keyword_do(state) do
    # Expect keyword form: `do:`
    if State.at?(state, :kw_identifier) do
      token = State.current(state)

      if token.value == :do do
        {state, _do_token} = State.advance(state)
        # Parse expression after do:
        {state, body} = parse_expression(state)
        # Don't include do: in metadata for keyword style - Elixir doesn't
        {state, Ast.do_block(body), nil, nil}
      else
        state = State.add_error(state, "expected 'do:'")
        {state, Ast.do_block(nil), nil, nil}
      end
    else
      state = State.add_error(state, "expected 'do:'")
      {state, Ast.do_block(nil), nil, nil}
    end
  end

  ## BLOCK BODY

  defp parse_block_body(state) do
    {state, exprs} = parse_block_body_items(state, [])
    ast = Ast.block(Enum.reverse(exprs), [])
    {state, ast}
  end

  defp parse_block_body_items(state, acc) do
    cond do
      State.at?(state, :end) or State.at_end?(state) ->
        {state, acc}

      # Use function_body recovery which includes :def for incomplete body recovery
      Recovery.at_recovery?(state, Recovery.function_body()) ->
        {state, acc}

      true ->
        state = State.advance_push(state)
        {state, expr} = parse_block_body_item(state)
        state = State.advance_pop!(state)

        acc = if expr != nil, do: [expr | acc], else: acc
        parse_block_body_items(state, acc)
    end
  end

  defp parse_block_body_item(state) do
    parse_expression(state)
  end

  ## DIRECTIVES (use, import, alias, require)

  defp parse_directive(state, kind) do
    {state, directive_token} = State.advance(state)
    meta = Ast.token_meta(directive_token)

    # Use expression parser to handle both simple aliases (Foo.Bar)
    # and multi-alias syntax (Foo.{A, B, C})
    {state, alias_ast} = parse_expression(state, 0)

    # Parse options if present (comma followed by keyword list or expressions)
    {state, args} =
      if State.at?(state, :comma) do
        {state, _comma} = State.advance(state)
        {state, opts} = parse_directive_options(state, [])
        {state, [alias_ast | opts]}
      else
        {state, [alias_ast]}
      end

    ast = Ast.call(kind, meta, args)
    {state, ast}
  end

  defp parse_directive_options(state, acc) do
    # Stop at module body tokens or end of expression
    if State.at_any?(state, Recovery.module_body()) or State.at_end?(state) do
      {state, Enum.reverse(acc)}
    else
      {state, expr} = parse_expression(state, 0)

      if State.at?(state, :comma) do
        {state, _comma} = State.advance(state)
        parse_directive_options(state, [expr | acc])
      else
        {state, Enum.reverse([expr | acc])}
      end
    end
  end

  # Add end_of_expression metadata to an expression
  # This tracks where expressions end for formatter purposes
  defp add_end_of_expression(_state, nil), do: nil

  defp add_end_of_expression(state, {name, meta, args}) when is_atom(name) and is_list(meta) do
    prev_token = State.prev(state)
    newlines = State.newlines_before(state)

    if newlines > 0 and prev_token != nil do
      eoe_meta = [
        newlines: newlines,
        line: prev_token.end_line,
        column: prev_token.end_column
      ]

      {name, [{:end_of_expression, eoe_meta} | meta], args}
    else
      {name, meta, args}
    end
  end

  defp add_end_of_expression(_state, expr), do: expr

  ## PREFIX PARSING

  defp parse_prefix(state, allow_do) do
    token = State.current(state)

    cond do
      # Ellipsis operator - can stand alone or take an argument
      State.at?(state, :ellipsis_op) ->
        parse_ellipsis(state)

      # Range operator standalone - just the .. without operands
      State.at?(state, :..) ->
        parse_range_standalone(state)

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

      State.at?(state, :char) ->
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

      State.at?(state, :charlist_heredoc) ->
        parse_charlist_heredoc(state)

      State.at?(state, :charlist) ->
        parse_charlist(state)

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

      # Lexer error token - record error and continue
      State.at?(state, :error_token) ->
        error = token.value

        error_msg =
          if is_struct(error) and Map.has_key?(error, :message),
            do: error.message,
            else: "lexer error"

        state = State.add_error(state, error_msg)
        {state, _} = State.advance(state)
        {state, Ast.error_at(token)}

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

    # Special case: `not a in b` and `!a in b` - use `in`'s position
    meta =
      case {token.kind, operand} do
        {:not, {:in, in_meta, _}} -> in_meta
        {:!, {:in, in_meta, _}} -> in_meta
        _ -> meta
      end

    ast = Ast.unary_op(token.kind, meta, operand)
    {state, ast}
  end

  # Range operator standalone: .. without operands
  # Produces: {:.., meta, []}
  defp parse_range_standalone(state) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = Ast.token_meta(token)
    ast = {:.., meta, []}
    {state, ast}
  end

  # Ellipsis operator: ... can stand alone or take an optional argument
  # Standalone: {:..., meta, []}
  # With arg: {:..., meta, [arg]}
  defp parse_ellipsis(state) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = Ast.token_meta(token)

    # Check if there's an argument (identifier on same line, no newline)
    if not State.newline_before?(state) and State.at?(state, :identifier) do
      arg_token = State.current(state)
      {state, _} = State.advance(state)
      arg_meta = Ast.token_meta(arg_token)
      arg = Ast.var(arg_token.value, arg_meta)
      ast = {:..., meta, [arg]}
      {state, ast}
    else
      # Standalone ellipsis
      ast = {:..., meta, []}
      {state, ast}
    end
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

    # Check for newlines after the operator (before RHS)
    # Elixir records this as `newlines: N` in operator metadata
    # Note: dot operator does not get newlines metadata
    newlines = State.newlines_before(state)
    meta_with_newlines = if newlines > 0, do: [{:newlines, newlines} | meta], else: meta

    cond do
      # Special handling for dot operator (no newlines metadata)
      op_token.kind == :dot ->
        parse_dot_rhs(state, lhs, meta)

      # Special handling for "not in" - produces {:not, _, [{:in, _, [lhs, rhs]}]}
      # Note: "not in" does not get newlines metadata
      op_token.kind == :"not in" ->
        # RHS of binary op shouldn't consume do blocks
        {state, rhs} = parse_expression(state, right_bp, allow_do: false)
        in_ast = {:in, meta, [lhs, rhs]}
        ast = {:not, meta, [in_ast]}
        {state, ast}

      # Special handling for range operator (..) - may become ternary step operator (..//)
      op_token.kind == :.. ->
        {state, rhs} = parse_expression(state, right_bp, allow_do: false)

        # Check if followed by step operator (//)
        if State.at?(state, :"//") do
          {state, _step_token} = State.advance(state)
          # Parse the step value with same binding power
          {state, step} = parse_expression(state, right_bp, allow_do: false)
          # Build ternary step operator: ..// (metadata from ..)
          ast = {:..//, meta, [lhs, rhs, step]}
          {state, ast}
        else
          ast = Ast.binary_op(:.., meta_with_newlines, lhs, rhs)
          {state, ast}
        end

      true ->
        # RHS of binary op shouldn't consume do blocks - they belong to outer constructs
        {state, rhs} = parse_expression(state, right_bp, allow_do: false)
        ast = Ast.binary_op(op_token.kind, meta_with_newlines, lhs, rhs)
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
        cond do
          State.at?(state, :lparen) ->
            {state, _} = State.advance(state)
            {state, args} = parse_call_args(state)
            {state, closing} = State.expect(state, :rparen)

            # Use identifier position for call meta, not dot position
            call_meta = if closing, do: Ast.with_closing(id_meta, closing), else: id_meta
            dot_ast = {:., dot_meta, [lhs, name]}
            ast = {dot_ast, call_meta, args}
            {state, ast}

          # No-parens call: Foo.bar 1 or Foo.bar x: 1
          # Must be on same line (no newline) and next token can start an argument
          not State.newline_before?(state) and starts_no_paren_arg_strict?(state) ->
            dot_ast = {:., dot_meta, [lhs, name]}
            {state, args} = parse_no_paren_args(state, [])
            ast = {dot_ast, id_meta, args}
            {state, ast}

          true ->
            # Field access (no parens, no args) - use identifier position with no_parens flag
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
      :kw_identifier,
      :charlist,
      :heredoc,
      :charlist_heredoc,
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
      :@,
      # NOTE: :+ and :- are NOT here - they're ambiguous with infix
      # The tokenizer tells us via :op_identifier when they should be prefix
      :!,
      :"~~~"
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
  # Supports do/else/rescue/catch/after clauses
  defp maybe_parse_do_block(state, {name, meta, args}, original_meta) when is_list(args) do
    if State.at?(state, :do) do
      {state, do_token} = State.advance(state)
      # Stop at any clause keyword, not just else/end
      {state, body} = parse_block_until(state, [:else, :rescue, :catch, :after, :end])

      # Parse optional clauses in order: rescue, catch, else, after
      {state, clauses} = parse_do_block_clauses(state, do: body)

      {state, end_token} = State.expect(state, :end)

      call_meta = Ast.with_do_end(original_meta, do_token, end_token)
      ast = {name, call_meta, args ++ [clauses]}
      {state, ast}
    else
      {state, {name, meta, args}}
    end
  end

  defp maybe_parse_do_block(state, ast, _original_meta), do: {state, ast}

  # Parse optional do block clauses (rescue, catch, else, after)
  defp parse_do_block_clauses(state, acc) do
    cond do
      State.at?(state, :rescue) ->
        {state, _} = State.advance(state)
        {state, clauses} = parse_stab_clauses(state, [])
        parse_do_block_clauses(state, acc ++ [rescue: clauses])

      State.at?(state, :catch) ->
        {state, _} = State.advance(state)
        {state, clauses} = parse_stab_clauses(state, [])
        parse_do_block_clauses(state, acc ++ [catch: clauses])

      State.at?(state, :else) ->
        {state, _} = State.advance(state)
        {state, body} = parse_block_until(state, [:rescue, :catch, :after, :end])
        parse_do_block_clauses(state, acc ++ [else: body])

      State.at?(state, :after) ->
        {state, _} = State.advance(state)
        {state, body} = parse_block_until(state, [:end])
        parse_do_block_clauses(state, acc ++ [after: body])

      true ->
        {state, acc}
    end
  end

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

    case token.value do
      # New format with indent metadata
      %{indent: indent, content: content} ->
        case content do
          # Simple heredoc - no interpolation
          str when is_binary(str) ->
            {state, str}

          # Heredoc with interpolation - use existing interpolation handling
          parts when is_list(parts) ->
            meta = [
              {:delimiter, "\"\"\""},
              {:indentation, indent}
              | Ast.token_meta(token)
            ]

            ast_parts = build_interpolation_parts(parts)
            ast = {:<<>>, meta, ast_parts}
            {state, ast}
        end

      # Old format - just string content
      content when is_binary(content) ->
        {state, content}

      content when is_list(content) ->
        # Already processed chardata
        {state, IO.chardata_to_string(content)}
    end
  end

  defp parse_charlist_heredoc(state) do
    token = State.current(state)
    {state, _} = State.advance(state)

    case token.value do
      # New format with indent metadata
      %{indent: indent, content: content} ->
        meta = [{:delimiter, "'''"}, {:indentation, indent} | Ast.token_meta(token)]

        case content do
          # Simple charlist heredoc - convert to charlist
          str when is_binary(str) ->
            {state, String.to_charlist(str)}

          # Charlist with list content - already a charlist
          chars when is_list(chars) ->
            # Check for interpolation
            has_interpolation? = Enum.any?(chars, &match?({{_, _, _}, {_, _, _}, _}, &1))

            if has_interpolation? do
              # Build List.to_charlist([parts]) wrapper
              ast_parts = build_charlist_interpolation_parts(chars)
              dot_ast = {:., [line: meta[:line], column: meta[:column]], [List, :to_charlist]}
              call_ast = {dot_ast, meta, [ast_parts]}
              {state, call_ast}
            else
              # Join and convert to charlist
              joined = IO.chardata_to_string(chars)
              {state, String.to_charlist(joined)}
            end
        end

      # Old format - just content
      content when is_binary(content) ->
        {state, String.to_charlist(content)}

      content when is_list(content) ->
        {state, content}
    end
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

  defp parse_charlist(state) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = [{:delimiter, "'"} | Ast.token_meta(token)]

    case token.value do
      # Simple charlist - no interpolation
      charlist when is_list(charlist) and not is_tuple(hd(charlist)) ->
        # Just a regular charlist like 'abc'
        if Enum.all?(charlist, &is_integer/1) do
          {state, charlist}
        else
          # Has interpolation parts
          build_charlist_interpolation(state, charlist, meta)
        end

      parts when is_list(parts) ->
        has_interpolation? = Enum.any?(parts, &match?({{_, _, _}, {_, _, _}, _}, &1))

        if has_interpolation? do
          build_charlist_interpolation(state, parts, meta)
        else
          # Just charlist parts, convert to charlist
          joined =
            Enum.map_join(parts, fn
              str when is_binary(str) -> str
              chars when is_list(chars) -> IO.chardata_to_string(chars)
              _ -> ""
            end)

          {state, String.to_charlist(joined)}
        end

      other when is_list(other) ->
        {state, other}

      other ->
        {state, String.to_charlist(to_string(other))}
    end
  end

  defp build_charlist_interpolation(state, parts, meta) do
    # Build List.to_charlist([parts]) call
    ast_parts = build_charlist_interpolation_parts(parts)
    dot_ast = {:., [line: meta[:line], column: meta[:column]], [List, :to_charlist]}
    call_ast = {dot_ast, meta, [ast_parts]}
    {state, call_ast}
  end

  defp build_charlist_interpolation_parts(parts) do
    Enum.map(parts, fn
      str when is_binary(str) ->
        str

      {{start_line, start_col, _}, {end_line, end_col, _}, tokens} ->
        # Parse the interpolated tokens
        parsed_expr = parse_interpolation_tokens(tokens)

        # Build the Kernel.to_string call for interpolation
        dot_meta = [line: start_line, column: start_col]

        call_meta = [
          from_interpolation: true,
          closing: [line: end_line, column: end_col],
          line: start_line,
          column: start_col
        ]

        dot_ast = {:., dot_meta, [Kernel, :to_string]}
        {dot_ast, call_meta, [parsed_expr]}

      chars when is_list(chars) ->
        IO.chardata_to_string(chars)

      other ->
        to_string(other)
    end)
  end

  defp build_interpolation_parts(parts) do
    Enum.map(parts, fn
      str when is_binary(str) ->
        str

      {{start_line, start_col, _}, {end_line, end_col, _}, tokens} ->
        # Parse the interpolated tokens
        parsed_expr = parse_interpolation_tokens(tokens)

        # Build the interpolation AST structure
        dot_meta = [line: start_line, column: start_col]

        call_meta = [
          from_interpolation: true,
          closing: [line: end_line, column: end_col],
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
    # Convert Toxic ranged tokens to our Token structs and parse
    normalized = Enum.map(tokens, &Hurricane.Token.from_toxic/1)
    normalized = normalized ++ [Hurricane.Token.eof(0, 0)]

    inner_state = %State{
      tokens: normalized,
      pos: 0,
      errors: [],
      checkpoints: []
    }

    # Track first token before skipping - used for empty block position if #{;}
    first_token = State.current(inner_state)

    # Skip leading semicolons/eol - #{;a} should parse as just `a`
    inner_state = skip_leading_separators(inner_state)

    # Check for special cases: empty #{} or just #{;}
    current = State.current(inner_state)

    cond do
      # Empty interpolation #{} or just semicolon #{;}
      current == nil or current.kind == :eof ->
        # Use first token's position if it was a separator (#{;} case)
        if first_token && (first_token.kind == :semicolon or first_token.kind == :eol) do
          {:__block__, [line: first_token.line, column: first_token.column], []}
        else
          {:__block__, [], []}
        end

      true ->
        # Parse all expressions separated by semicolons in interpolation
        {_state, exprs} = parse_interpolation_exprs(inner_state, [])

        case exprs do
          [] -> {:__block__, [], []}
          [single] -> single
          multiple -> {:__block__, [], multiple}
        end
    end
  end

  # Parse all expressions in interpolation, handling semicolon separators
  defp parse_interpolation_exprs(state, acc) do
    if State.at?(state, :eof) or State.at_end?(state) do
      {state, Enum.reverse(acc)}
    else
      {state, ast} = parse_expression(state, 0)

      # Add end_of_expression if followed by semicolon
      ast =
        if ast != nil and State.at?(state, :semicolon) do
          add_end_of_expression_semicolon(state, ast)
        else
          ast
        end

      acc = if ast != nil, do: [ast | acc], else: acc

      # Skip semicolon and continue if there are more expressions
      if State.at?(state, :semicolon) do
        {state, _} = State.advance(state)
        state = skip_leading_separators(state)
        parse_interpolation_exprs(state, acc)
      else
        {state, Enum.reverse(acc)}
      end
    end
  end

  # Add end_of_expression metadata when followed by semicolon (newlines: 0)
  defp add_end_of_expression_semicolon(state, {name, meta, args})
       when is_atom(name) and is_list(meta) do
    prev_token = State.prev(state)

    if prev_token != nil do
      eoe_meta = [
        newlines: 0,
        line: prev_token.end_line,
        column: prev_token.end_column
      ]

      {name, [{:end_of_expression, eoe_meta} | meta], args}
    else
      {name, meta, args}
    end
  end

  defp add_end_of_expression_semicolon(_state, expr), do: expr

  # Skip leading semicolons and eol tokens in interpolation
  defp skip_leading_separators(state) do
    if State.at?(state, :semicolon) or State.at?(state, :eol) do
      {state, _} = State.advance(state)
      skip_leading_separators(state)
    else
      state
    end
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
    {state, rbrace} = State.expect(state, :rbrace)
    # Add closing metadata for tuples with 1 or 3+ elements (2-element tuples don't need it)
    meta =
      if rbrace != nil and length(elements) != 2, do: Ast.with_closing(meta, rbrace), else: meta

    ast = Ast.tuple(elements, meta)
    {state, ast}
  end

  defp parse_map(state) do
    {state, map_open} = State.advance(state)
    meta = Ast.token_meta(map_open)
    # Also consume the lbrace that follows %
    {state, _lbrace} = State.expect(state, :lbrace)

    # Check for map update syntax: %{map | key: value}
    # vs regular map syntax: %{a: 1} or %{"key" => value}
    {state, content} =
      cond do
        State.at?(state, :rbrace) ->
          # Empty map
          {state, []}

        State.at?(state, :kw_identifier) ->
          # Keyword syntax - definitely not update syntax, parse as pairs
          {state, pairs} = parse_map_pairs(state)
          {state, pairs}

        true ->
          # Expression first - could be update syntax or arrow syntax
          # Use binding power 10 so we stop before | (which has bp 9)
          {state, first} = parse_expression(state, 10)

          if State.at?(state, :|) do
            # Map update syntax: %{base | updates}
            {state, pipe_token} = State.advance(state)
            pipe_meta = Ast.token_meta(pipe_token)
            {state, updates} = parse_map_update_pairs(state)
            pipe_expr = {:|, pipe_meta, [first, updates]}
            {state, [pipe_expr]}
          else
            # Regular map with arrow syntax - first was a key
            {state, first_pair} = finish_map_pair(state, first)
            {state, rest} = parse_map_pairs_rest(state)
            pairs = if first_pair, do: [first_pair | rest], else: rest
            {state, pairs}
          end
      end

    {state, rbrace} = State.expect(state, :rbrace)
    # Add closing metadata
    meta = if rbrace, do: Ast.with_closing(meta, rbrace), else: meta
    ast = Ast.map(content, meta)
    {state, ast}
  end

  # Parse update pairs after the | in map update syntax
  defp parse_map_update_pairs(state) do
    {state, pairs} = parse_keyword_or_arrow_pairs(state, [])
    {state, pairs}
  end

  defp parse_keyword_or_arrow_pairs(state, acc) do
    if State.at?(state, :rbrace) or Recovery.at_recovery?(state, Recovery.collection()) do
      {state, Enum.reverse(acc)}
    else
      {state, pair} = parse_single_map_pair(state)
      acc = if pair, do: [pair | acc], else: acc

      case State.eat(state, :comma) do
        {:ok, state, _} ->
          parse_keyword_or_arrow_pairs(state, acc)

        {:error, state} ->
          {state, Enum.reverse(acc)}
      end
    end
  end

  defp parse_single_map_pair(state) do
    if State.at?(state, :kw_identifier) do
      token = State.current(state)
      {state, _} = State.advance(state)
      {state, value} = parse_expression(state, 0)
      {state, {token.value, value}}
    else
      {state, key} = parse_expression(state, 0)

      if State.at?(state, :"=>") do
        {state, _} = State.advance(state)
        {state, value} = parse_expression(state, 0)
        {state, {key, value}}
      else
        {state, {key, nil}}
      end
    end
  end

  # Finish parsing a map pair when we've already parsed the key
  defp finish_map_pair(state, key) do
    cond do
      State.at?(state, :"=>") ->
        {state, _} = State.advance(state)
        {state, value} = parse_expression(state, 0)
        {state, {key, value}}

      State.at?(state, :comma) or State.at?(state, :rbrace) ->
        # Key was actually a kw pair parsed as expression - this shouldn't happen
        # for well-formed code, but handle it
        {state, {key, nil}}

      true ->
        # Just have a key expression (error case or lonely expression)
        {state, {key, nil}}
    end
  end

  defp parse_sigil(state) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = Ast.token_meta(token)

    # Extract sigil data from token value
    %{
      sigil_name: sigil_name,
      content: content,
      modifiers: modifiers,
      indentation: indentation,
      delimiter: delimiter
    } = token.value

    # Build metadata with delimiter
    meta = [{:delimiter, IO.chardata_to_string([delimiter])} | meta]

    # Build content metadata - include indentation for heredoc sigils
    # Heredoc delimiters are """ or '''
    is_heredoc? = delimiter in [~c"\"\"\"", ~c"'''", "\"\"\"", "'''"]

    content_meta =
      if is_heredoc? and is_integer(indentation) do
        [{:indentation, indentation} | Ast.token_meta(token)]
      else
        Ast.token_meta(token)
      end

    # Check for interpolation in content
    has_interpolation? =
      is_list(content) and Enum.any?(content, &match?({{_, _, _}, {_, _, _}, _}, &1))

    # Build content as binary node
    content_ast =
      if has_interpolation? do
        # Process interpolation parts
        ast_parts = build_interpolation_parts(content)
        {:<<>>, content_meta, ast_parts}
      else
        Ast.binary(content, content_meta)
      end

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
    # Handle update syntax: %Foo{s | a: 1}
    {state, lbrace} = State.expect(state, :lbrace)

    {state, content} =
      cond do
        State.at?(state, :rbrace) ->
          # Empty struct
          {state, []}

        State.at?(state, :kw_identifier) ->
          # Keyword syntax - not update syntax
          {state, pairs} = parse_map_pairs(state)
          {state, pairs}

        true ->
          # Expression first - could be update syntax
          {state, first} = parse_expression(state, 10)

          if State.at?(state, :|) do
            # Struct update syntax: %Foo{base | updates}
            {state, pipe_token} = State.advance(state)
            pipe_meta = Ast.token_meta(pipe_token)
            {state, updates} = parse_map_update_pairs(state)
            pipe_expr = {:|, pipe_meta, [first, updates]}
            {state, [pipe_expr]}
          else
            # Regular struct with arrow syntax
            {state, first_pair} = finish_map_pair(state, first)
            {state, rest} = parse_map_pairs_rest(state)
            pairs = if first_pair, do: [first_pair | rest], else: rest
            {state, pairs}
          end
      end

    {state, rbrace} = State.expect(state, :rbrace)

    # Build struct AST: {:%, meta, [alias, {:%{}, map_meta, pairs}]}
    map_meta = Ast.token_meta(lbrace)
    map_meta = if rbrace, do: Ast.with_closing(map_meta, rbrace), else: map_meta
    map_ast = Ast.map(content, map_meta)
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

    # Check for empty parens first
    if State.at?(state, :rparen) do
      {state, rparen} = State.advance(state)

      meta = [
        closing: [line: rparen.line, column: rparen.column],
        line: lparen.line,
        column: lparen.column
      ]

      {state, {:__block__, meta, []}}
    else
      # Check for stab expression: (pattern -> body) or (-> body)
      if State.at?(state, :->) do
        # Bare stab: (-> body)
        parse_paren_stab(state, [], lparen)
      else
        # Parse first expression
        {state, first_expr} = parse_expression(state, 0)

        cond do
          # Check if this is a stab expression
          State.at?(state, :->) ->
            # This is a stab: (expr -> body) or (expr, expr -> body)
            {state, patterns} = parse_more_patterns(state, [first_expr])
            parse_paren_stab(state, patterns, lparen)

          State.at?(state, :comma) ->
            # Could be multi-pattern stab or just grouped expressions
            {state, rest_exprs} = parse_comma_exprs(state)
            all_exprs = [first_expr | rest_exprs]

            if State.at?(state, :->) do
              # It's a stab with multiple patterns
              parse_paren_stab(state, all_exprs, lparen)
            else
              # Regular grouped expression with comma (like tuples, but in parens)
              {state, rparen} = State.expect(state, :rparen)
              expr = add_parens_meta(first_expr, lparen, rparen)
              {state, expr}
            end

          true ->
            # Regular parenthesized expression
            {state, rparen} = State.expect(state, :rparen)
            expr = add_parens_meta(first_expr, lparen, rparen)
            {state, expr}
        end
      end
    end
  end

  defp parse_comma_exprs(state) do
    case State.eat(state, :comma) do
      {:ok, state, _} ->
        if State.at?(state, :->) or State.at?(state, :rparen) do
          {state, []}
        else
          {state, expr} = parse_expression(state, 0)
          {state, rest} = parse_comma_exprs(state)
          exprs = if expr != nil, do: [expr | rest], else: rest
          {state, exprs}
        end

      {:error, state} ->
        {state, []}
    end
  end

  defp parse_more_patterns(state, acc) do
    # Check for comma-separated patterns before ->
    case State.eat(state, :comma) do
      {:ok, state, _} ->
        if State.at?(state, :->) do
          {state, Enum.reverse(acc)}
        else
          {state, pattern} = parse_expression(state, 0)
          pattern_list = if pattern != nil, do: [pattern | acc], else: acc
          parse_more_patterns(state, pattern_list)
        end

      {:error, state} ->
        {state, Enum.reverse(acc)}
    end
  end

  defp parse_paren_stab(state, patterns, _lparen) do
    # Consume -> and parse body/clauses
    {state, clauses} = parse_paren_stab_clauses(state, patterns)
    {state, _rparen} = State.expect(state, :rparen)

    # Elixir's AST for paren stab is just the list of clauses, not wrapped in block
    # e.g., (1 -> 2) becomes [{:->, meta, [[1], 2]}]
    {state, clauses}
  end

  defp parse_paren_stab_clauses(state, initial_patterns) do
    {state, first_clause} = parse_single_stab_clause(state, initial_patterns)
    {state, rest} = parse_more_paren_stab_clauses(state)
    {state, [first_clause | rest]}
  end

  defp parse_single_stab_clause(state, patterns) do
    {state, arrow} = State.expect(state, :->)
    arrow_meta = Ast.token_meta(arrow)

    # Check if patterns is a single empty block (from parsing `()`)
    # In that case, it represents empty parens, not a block pattern
    {actual_patterns, arrow_meta} =
      case patterns do
        [{:__block__, block_meta, []}] ->
          # Empty parens - extract parens metadata and use [] as patterns
          parens_meta =
            [
              line: block_meta[:line],
              column: block_meta[:column]
            ] ++ if block_meta[:closing], do: [closing: block_meta[:closing]], else: []

          {[], [{:parens, parens_meta} | arrow_meta]}

        _ ->
          {patterns, arrow_meta}
      end

    # Parse body until ) or another clause pattern
    {state, body_exprs} = parse_paren_stab_body(state, [])
    body = Ast.block(Enum.reverse(body_exprs), [])

    ast = Ast.stab(actual_patterns, body, arrow_meta)
    {state, ast}
  end

  defp parse_paren_stab_body(state, acc) do
    if State.at?(state, :rparen) or State.at_end?(state) or
         looks_like_new_paren_stab_clause?(state) do
      {state, acc}
    else
      state = State.advance_push(state)
      {state, expr} = parse_expression(state, 0)
      state = State.advance_pop!(state)

      acc = if expr != nil, do: [expr | acc], else: acc
      parse_paren_stab_body(state, acc)
    end
  end

  defp looks_like_new_paren_stab_clause?(state) do
    # Check if we're at the start of a new stab clause
    # This typically happens after a semicolon with a -> coming up
    token = State.current(state)
    next = State.peek(state)

    # Pattern: identifier/literal followed by ->
    # or just -> for empty pattern
    cond do
      token && token.kind == :-> -> true
      token && next && next.kind == :-> -> true
      true -> false
    end
  end

  defp parse_more_paren_stab_clauses(state) do
    if State.at?(state, :rparen) or State.at_end?(state) do
      {state, []}
    else
      # Check for semicolon separating clauses
      state =
        case State.eat(state, :semicolon) do
          {:ok, state, _} -> state
          {:error, state} -> state
        end

      if State.at?(state, :rparen) or State.at_end?(state) do
        {state, []}
      else
        # Parse patterns for next clause
        {state, patterns} = parse_paren_stab_patterns(state)

        if State.at?(state, :->) do
          {state, clause} = parse_single_stab_clause(state, patterns)
          {state, rest} = parse_more_paren_stab_clauses(state)
          {state, [clause | rest]}
        else
          {state, []}
        end
      end
    end
  end

  defp parse_paren_stab_patterns(state) do
    if State.at?(state, :->) do
      {state, []}
    else
      {state, pattern} = parse_expression(state, 0)
      {state, rest} = parse_more_patterns(state, [])
      patterns = if pattern != nil, do: [pattern | rest], else: rest
      {state, patterns}
    end
  end

  defp add_parens_meta({name, meta, args}, lparen, rparen) when is_atom(name) and is_list(meta) do
    parens_meta =
      [line: lparen.line, column: lparen.column] ++
        if rparen, do: [closing: [line: rparen.line, column: rparen.column]], else: []

    # Prepend to allow multiple parens entries for nested parens
    meta = [{:parens, parens_meta} | meta]
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
    # Multiple clauses are separated by semicolons OR newlines
    cond do
      # Explicit semicolon separator
      State.at?(state, :semicolon) ->
        {state, _} = State.advance(state)

        if State.at?(state, :end) or State.at_end?(state) do
          {state, []}
        else
          {state, clause} = parse_fn_clause(state)
          {state, rest} = parse_fn_clauses_rest(state)
          {state, [clause | rest]}
        end

      # Newline before current token and not at end - try another clause
      # But only if there's a -> ahead (indicating a stab pattern)
      State.newline_before?(state) and not State.at?(state, :end) and not State.at_end?(state) and
          looks_like_fn_clause?(state) ->
        {state, clause} = parse_fn_clause(state)
        {state, rest} = parse_fn_clauses_rest(state)
        {state, [clause | rest]}

      true ->
        {state, []}
    end
  end

  # Check if we're at what looks like an fn clause pattern (has -> ahead)
  defp looks_like_fn_clause?(state) do
    # Scan ahead looking for -> before we hit end, =, or other clause terminators
    scan_for_arrow(state, 0)
  end

  defp scan_for_arrow(state, depth) do
    # Limit lookahead depth to avoid scanning too far
    if depth > 50 do
      false
    else
      case State.current_kind(state) do
        # Found the arrow - this is likely a clause
        :-> ->
          true

        # Hit end of fn or file
        :end ->
          false

        :eof ->
          false

        # Hit :do - we're entering a block (case/if/etc), arrows inside are not fn clauses
        :do ->
          false

        # Hit assignment operator - this is body code, not a pattern
        := ->
          false

        # Hit a definition keyword - definitely not a pattern
        k when k in [:def, :defp, :defmacro, :defmacrop, :defmodule] ->
          false

        # Continue scanning
        _ ->
          {state, _} = State.advance(state)
          scan_for_arrow(state, depth + 1)
      end
    end
  end

  defp parse_fn_clause(state) do
    # Parse patterns (parameters)
    # Check for explicit parens: fn () -> or fn (x) ->
    {state, patterns, parens_meta} =
      if State.at?(state, :lparen) do
        lparen = State.current(state)
        {state, _} = State.advance(state)

        if State.at?(state, :rparen) do
          # Empty parens: fn () ->
          rparen = State.current(state)
          {state, _} = State.advance(state)

          parens = [
            line: lparen.line,
            column: lparen.column,
            closing: [line: rparen.line, column: rparen.column]
          ]

          {state, [], parens}
        else
          # Parens with args: fn (x) ->
          {state, inner_patterns} = parse_fn_patterns_inner(state)
          {state, rparen} = State.expect(state, :rparen)

          parens =
            if rparen do
              [
                line: lparen.line,
                column: lparen.column,
                closing: [line: rparen.line, column: rparen.column]
              ]
            else
              [line: lparen.line, column: lparen.column]
            end

          {state, inner_patterns, parens}
        end
      else
        # No parens - regular patterns
        {state, patterns} = parse_fn_patterns(state)
        {state, patterns, nil}
      end

    # Parse arrow
    {state, arrow_token} = State.expect(state, :->)
    meta = Ast.token_meta(arrow_token)
    # Add parens metadata if we had explicit parens
    meta = if parens_meta, do: [{:parens, parens_meta} | meta], else: meta

    # Parse body
    {state, body} = parse_fn_body(state)

    ast = Ast.stab(patterns, body, meta)
    {state, ast}
  end

  defp parse_fn_patterns_inner(state) do
    if State.at?(state, :rparen) or State.at?(state, :->) or
         Recovery.at_recovery?(state, Recovery.stab_clause()) do
      {state, []}
    else
      {state, pattern} = parse_expression(state, 0)
      {state, rest} = parse_fn_patterns_inner_rest(state)
      patterns = if pattern, do: [pattern | rest], else: rest
      {state, patterns}
    end
  end

  defp parse_fn_patterns_inner_rest(state) do
    case State.eat(state, :comma) do
      {:ok, state, _} ->
        if State.at?(state, :rparen) or Recovery.at_recovery?(state, Recovery.stab_clause()) do
          {state, []}
        else
          {state, pattern} = parse_expression(state, 0)
          {state, rest} = parse_fn_patterns_inner_rest(state)
          patterns = if pattern, do: [pattern | rest], else: rest
          {state, patterns}
        end

      {:error, state} ->
        {state, []}
    end
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
    # Stop at end, semicolon (clause separator), or eof
    # Also stop if there's a newline and the next tokens look like a new clause pattern
    cond do
      State.at?(state, :end) or State.at?(state, :semicolon) or State.at_end?(state) ->
        {state, acc}

      # Newline before next token and it looks like a new clause - stop here
      State.newline_before?(state) and looks_like_fn_clause?(state) ->
        {state, acc}

      true ->
        state = State.advance_push(state)
        {state, expr} = parse_expression(state, 0)
        state = State.advance_pop!(state)

        acc = if expr != nil, do: [expr | acc], else: acc
        parse_fn_body_exprs(state, acc)
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
          # Trailing comma - add error for strict conformance
          # Format matches Elixir: message and token as separate parts
          state = State.add_error(state, {"syntax error before: ", "')'"})
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

  # quote do body end  OR  quote do: expr
  defp parse_quote(state) do
    {state, quote_token} = State.advance(state)
    meta = Ast.token_meta(quote_token)

    # Check if next is kw_identifier with value :do (shorthand form: quote do: expr)
    token = State.current(state)
    is_shorthand_do = State.at?(state, :kw_identifier) and token != nil and token.value == :do

    cond do
      # Block form: quote do ... end
      State.at?(state, :do) ->
        {state, do_token} = State.advance(state)
        {state, body} = parse_block_until(state, [:end])
        {state, end_token} = State.expect(state, :end)
        meta = Ast.with_do_end(meta, do_token, end_token)
        ast = {:quote, meta, [[do: body]]}
        {state, ast}

      # Shorthand form: quote do: expr (kw_identifier with value :do)
      is_shorthand_do ->
        {state, kwargs} = parse_keyword_pairs(state)
        ast = {:quote, meta, [kwargs]}
        {state, ast}

      # Block form with options: quote opts do ... end
      State.at?(state, :kw_identifier) ->
        # Parse options before do block
        {state, opts} = parse_keyword_pairs(state)
        {state, do_token} = State.expect(state, :do)
        {state, body} = parse_block_until(state, [:end])
        {state, end_token} = State.expect(state, :end)
        meta = Ast.with_do_end(meta, do_token, end_token)
        # Options are wrapped in a list
        ast = {:quote, meta, [opts, [do: body]]}
        {state, ast}

      true ->
        # Fallback - try to parse as options then do block
        {state, opts} = parse_keyword_pairs(state)
        {state, do_token} = State.expect(state, :do)
        {state, body} = parse_block_until(state, [:end])
        {state, end_token} = State.expect(state, :end)
        meta = Ast.with_do_end(meta, do_token, end_token)
        # Options are wrapped in a list
        ast = {:quote, meta, [opts, [do: body]]}
        {state, ast}
    end
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
    # Stop at block terminators, definition keywords (for recovery), or orphan delimiters
    if State.at?(state, :end) or State.at?(state, :else) or
         State.at?(state, :rescue) or State.at?(state, :catch) or
         State.at?(state, :after) or State.at_end?(state) or
         State.at?(state, :def) or State.at?(state, :defp) or
         State.at?(state, :defmacro) or State.at?(state, :defmacrop) or
         State.at?(state, :defmodule) or
         State.at_any?(state, [:rparen, :rbracket, :rbrace, :rangle]) do
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
    # Stop at clause/block terminators, stab arrow, or orphan delimiters
    # Note: We also stop at :-> because if we hit an arrow, the previous "expression"
    # was actually a pattern for a new stab clause, not part of this body
    #
    # Definition keywords (def, defp, etc.) can validly appear in stab bodies
    # for compile-time conditional definitions like:
    #   case Mix.env() do
    #     :prod -> def hello, do: "prod"
    #   end
    # So we only treat them as recovery points if on a new line (indicating
    # they're probably a new top-level item from incomplete code).
    if State.at?(state, :end) or State.at?(state, :else) or
         State.at?(state, :rescue) or State.at?(state, :catch) or
         State.at?(state, :after) or State.at_end?(state) or
         State.at?(state, :->) or
         State.at_any?(state, [:rparen, :rbracket, :rbrace, :rangle]) or
         (State.newline_before?(state) and
            State.at_any?(state, [:def, :defp, :defmacro, :defmacrop, :defmodule])) do
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

        # Add end_of_expression metadata if followed by newline
        expr = add_end_of_expression(state, expr)

        acc = if expr != nil, do: [expr | acc], else: acc
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

      # Add end_of_expression metadata if followed by newline or terminator
      expr = add_end_of_expression(state, expr)

      acc = if expr != nil, do: [expr | acc], else: acc
      parse_block_until_exprs(state, terminators, acc)
    end
  end
end
