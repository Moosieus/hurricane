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

  # ============================================================================
  # Binding Power Tables
  # ============================================================================

  # Infix operators: {left_bp, right_bp}
  # Listed from lowest to highest precedence
  @infix_bp %{
    # Right-associative (left > right)
    :\\     => {5, 4},      # Default argument
    :|      => {9, 8},      # Cons
    # NOTE: :-> is NOT an infix operator - it's handled explicitly by stab clause parsing
    :when   => {11, 10},    # Guard
    :"::"   => {13, 12},    # Type annotation
    :<-     => {17, 16},    # Comprehension, with
    :=      => {19, 18},    # Match

    # Left-associative (right > left)
    :||     => {21, 22},
    :|||    => {21, 22},
    :or     => {21, 22},
    :&&     => {23, 24},
    :&&&    => {23, 24},
    :and    => {23, 24},

    # Comparison (left-associative)
    :==     => {25, 26},
    :!=     => {25, 26},
    :=~     => {25, 26},
    :===    => {25, 26},
    :!==    => {25, 26},

    # Relational (left-associative)
    :<      => {27, 28},
    :>      => {27, 28},
    :<=     => {27, 28},
    :>=     => {27, 28},

    # Pipe (left-associative)
    :|>     => {29, 30},

    # Membership
    :in     => {31, 32},

    # Bitwise xor
    :^^^    => {33, 34},

    # Concat (right-associative!)
    :++     => {35, 34},
    :--     => {35, 34},
    :+++    => {35, 34},
    :---    => {35, 34},
    :<>     => {35, 34},

    # Range
    :..     => {37, 36},
    :"../"  => {37, 36},

    # Arithmetic (left-associative)
    :+      => {39, 40},
    :-      => {39, 40},

    # Multiply/divide (left-associative)
    :*      => {41, 42},
    :/      => {41, 42},

    # Power (right-associative)
    :**     => {43, 42},

    # Dot (highest infix precedence)
    :dot    => {61, 62}
  }

  # Prefix operators: right binding power only
  @prefix_bp %{
    :!      => 55,
    :not    => 55,
    :~~~    => 55,
    :^      => 57,      # Pin
    :&      => 59,      # Capture
    :-      => 53,      # Unary minus
    :+      => 53,      # Unary plus
    :@      => 63       # Module attribute
  }

  # Postfix binding power (for calls and access)
  @call_bp 60
  @access_bp 60

  # ============================================================================
  # Public API
  # ============================================================================

  @doc """
  Parse an expression with given minimum binding power.
  """
  def parse_expression(state, min_bp \\ 0) do
    # 1. Parse prefix (atom, literal, unary op, parenthesized expr)
    {state, lhs} = parse_prefix(state)

    # 2. Loop: while next op binds tighter than min_bp
    parse_infix_loop(state, lhs, min_bp)
  end

  # ============================================================================
  # Prefix Parsing
  # ============================================================================

  defp parse_prefix(state) do
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

      State.at?(state, :string) ->
        parse_string(state)

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
      State.at?(state, :case) -> parse_case(state)
      State.at?(state, :cond) -> parse_cond(state)
      State.at?(state, :if) -> parse_if(state)
      State.at?(state, :unless) -> parse_unless(state)
      State.at?(state, :with) -> parse_with(state)
      State.at?(state, :try) -> parse_try(state)
      State.at?(state, :receive) -> parse_receive(state)
      State.at?(state, :for) -> parse_for(state)
      State.at?(state, :quote) -> parse_quote(state)

      # Identifiers and calls
      State.at?(state, :identifier) ->
        parse_identifier_or_call(state)

      # Special keywords that work like function calls
      State.at?(state, :raise) -> parse_keyword_call(state, :raise)
      State.at?(state, :reraise) -> parse_keyword_call(state, :reraise)
      State.at?(state, :throw) -> parse_keyword_call(state, :throw)
      State.at?(state, :unquote) -> parse_keyword_call(state, :unquote)
      State.at?(state, :unquote_splicing) -> parse_keyword_call(state, :unquote_splicing)

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

      # Binary/bitstring
      State.at?(state, :langle) ->
        parse_binary(state)

      # Anonymous function
      State.at?(state, :fn) ->
        parse_fn(state)

      # Capture argument placeholder (&1, &2, etc.)
      State.at?(state, :capture_int) ->
        parse_capture_arg(state)

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

    {state, operand} = parse_expression(state, bp)
    ast = Ast.unary_op(token.kind, meta, operand)
    {state, ast}
  end

  # ============================================================================
  # Infix Loop
  # ============================================================================

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
          {state, lhs} = parse_infix_op(state, lhs, token, right_bp)
          parse_infix_loop(state, lhs, min_bp)

        _ ->
          # Check for postfix (call, access)
          {state, lhs} = maybe_parse_postfix(state, lhs, min_bp)
          {state, lhs}
      end
    end
  end

  defp infix_bp(nil), do: nil
  defp infix_bp(%{kind: kind}), do: Map.get(@infix_bp, kind)

  defp parse_infix_op(state, lhs, op_token, right_bp) do
    {state, _} = State.advance(state)
    meta = Ast.token_meta(op_token)

    # Special handling for dot operator
    if op_token.kind == :dot do
      parse_dot_rhs(state, lhs, meta)
    else
      {state, rhs} = parse_expression(state, right_bp)
      ast = Ast.binary_op(op_token.kind, meta, lhs, rhs)
      {state, ast}
    end
  end

  # ============================================================================
  # Dot Access
  # ============================================================================

  defp parse_dot_rhs(state, lhs, dot_meta) do
    token = State.current(state)

    cond do
      # Remote call: Foo.bar or foo.bar
      State.at?(state, :identifier) ->
        {state, _} = State.advance(state)
        name = token.value

        # Check for call with parens
        if State.at?(state, :lparen) do
          {state, _} = State.advance(state)
          {state, args} = parse_call_args(state)
          {state, closing} = State.expect(state, :rparen)

          call_meta = Ast.with_closing(dot_meta, closing)
          dot_ast = {:., dot_meta, [lhs, name]}
          ast = {dot_ast, call_meta, args}
          {state, ast}
        else
          # Field access
          dot_ast = {:., dot_meta, [lhs, name]}
          ast = {dot_ast, dot_meta, []}
          {state, ast}
        end

      # Tuple access: foo.{a, b}
      State.at?(state, :lbrace) ->
        {state, tuple} = parse_tuple(state)
        dot_ast = {:., dot_meta, [lhs, :{}]}
        ast = {dot_ast, dot_meta, [tuple]}
        {state, ast}

      true ->
        state = State.add_error(state, "expected identifier after '.'")
        {state, lhs}
    end
  end

  # ============================================================================
  # Postfix (Calls and Access)
  # ============================================================================

  defp maybe_parse_postfix(state, lhs, min_bp) do
    cond do
      # Function call with parens: foo(...)
      # NOT if there's a newline before ( - that's a separate expression
      State.at?(state, :lparen) and min_bp < @call_bp and not State.newline_before?(state) ->
        parse_call(state, lhs)

      # Bracket access: foo[...]
      # NOT if there's a newline before [ - that's a separate expression
      State.at?(state, :lbracket) and min_bp < @access_bp and not State.newline_before?(state) ->
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
    {state, _rbracket} = State.expect(state, :rbracket)

    # Access is {{:., _, [Access, :get]}, _, [lhs, key]}
    access_ast = {{:., meta, [Access, :get]}, meta, [lhs, key]}
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

  # ============================================================================
  # Atoms and Identifiers
  # ============================================================================

  defp parse_identifier_or_call(state) do
    token = State.current(state)
    {state, _} = State.advance(state)
    meta = Ast.token_meta(token)

    # Check for call with parens
    if State.at?(state, :lparen) do
      {state, _} = State.advance(state)
      {state, args} = parse_call_args(state)
      {state, closing} = State.expect(state, :rparen)

      call_meta = if closing, do: Ast.with_closing(meta, closing), else: meta
      ast = Ast.call(token.value, call_meta, args)
      {state, ast}
    else
      # Plain variable
      ast = Ast.var(token.value, meta)
      {state, ast}
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
      # No parens - parse one argument
      {state, arg} = parse_expression(state, 0)
      args = if arg, do: [arg], else: []
      ast = Ast.call(name, meta, args)
      {state, ast}
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

  # ============================================================================
  # Strings
  # ============================================================================

  defp parse_string(state) do
    token = State.current(state)
    {state, _} = State.advance(state)

    content =
      case token.value do
        [str] when is_binary(str) -> str
        parts when is_list(parts) -> interpolated_string(parts)
        other -> to_string(other)
      end

    {state, content}
  end

  defp interpolated_string(parts) do
    # For now, just join string parts, ignoring interpolation
    # TODO: Handle interpolation properly
    parts
    |> Enum.map(fn
      str when is_binary(str) -> str
      _ -> ""
    end)
    |> Enum.join()
  end

  # ============================================================================
  # Collections
  # ============================================================================

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
      {state, element} = parse_expression(state, 0)
      {state, rest} = parse_collection_elements_rest(state, closing_kind)
      elements = if element, do: [element | rest], else: rest
      {state, elements}
    end
  end

  defp parse_collection_elements_rest(state, closing_kind) do
    case State.eat(state, :comma) do
      {:ok, state, _} ->
        if State.at?(state, closing_kind) or Recovery.at_recovery?(state, Recovery.collection()) do
          {state, []}
        else
          {state, element} = parse_expression(state, 0)
          {state, rest} = parse_collection_elements_rest(state, closing_kind)
          elements = if element, do: [element | rest], else: rest
          {state, elements}
        end

      {:error, state} ->
        {state, []}
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
        if State.at?(state, :rbrace) or Recovery.at_recovery?(state, Recovery.collection()) do
          {state, []}
        else
          {state, pair} = parse_map_pair(state)
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

  # ============================================================================
  # Capture Arguments (&1, &2, etc.)
  # ============================================================================

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

  # ============================================================================
  # Parenthesized Expression
  # ============================================================================

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

  # ============================================================================
  # Anonymous Functions
  # ============================================================================

  defp parse_fn(state) do
    {state, fn_token} = State.advance(state)
    meta = Ast.token_meta(fn_token)

    {state, clauses} = parse_fn_clauses(state)
    {state, _end_token} = State.expect(state, :end)

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

  # ============================================================================
  # Call Arguments
  # ============================================================================

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
        if State.at?(state, :rparen) do
          {state, []}
        else
          {state, arg} = parse_call_arg(state)
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

  # ============================================================================
  # Special Forms
  # ============================================================================

  # case expr do clauses end
  defp parse_case(state) do
    {state, case_token} = State.advance(state)
    meta = Ast.token_meta(case_token)

    # Parse the expression being matched
    {state, expr} = parse_expression(state, 0)

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

    # Parse condition
    {state, condition} = parse_expression(state, 0)

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

  defp parse_unless(state) do
    {state, unless_token} = State.advance(state)
    meta = Ast.token_meta(unless_token)

    {state, condition} = parse_expression(state, 0)

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
    {state, expr} = parse_expression(state, 0)
    {state, expr}
  end

  # try do body rescue/catch/after end
  defp parse_try(state) do
    {state, try_token} = State.advance(state)
    meta = Ast.token_meta(try_token)

    {state, do_token} = State.expect(state, :do)
    {state, body} = parse_block_until(state, [:rescue, :catch, :else, :after, :end])

    # Parse optional sections
    {state, sections} = parse_try_sections(state, [do: body])

    {state, end_token} = State.expect(state, :end)

    meta = Ast.with_do_end(meta, do_token, end_token)
    ast = {:try, meta, [sections]}
    {state, ast}
  end

  defp parse_try_sections(state, acc) do
    cond do
      State.at?(state, :rescue) ->
        {state, _} = State.advance(state)
        # Don't use parse_stab_block_inner - it expects :end
        # parse_stab_clauses stops at :catch/:after/:end
        {state, clauses} = parse_stab_clauses(state, [])
        parse_try_sections(state, Keyword.put(acc, :rescue, clauses))

      State.at?(state, :catch) ->
        {state, _} = State.advance(state)
        {state, clauses} = parse_stab_clauses(state, [])
        parse_try_sections(state, Keyword.put(acc, :catch, clauses))

      State.at?(state, :else) ->
        {state, _} = State.advance(state)
        {state, clauses} = parse_stab_clauses(state, [])
        parse_try_sections(state, Keyword.put(acc, :else, clauses))

      State.at?(state, :after) ->
        {state, _} = State.advance(state)
        {state, body} = parse_block_until(state, [:end])
        parse_try_sections(state, Keyword.put(acc, :after, body))

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
        {state, [do: body], updated_meta}
      else
        # Already have keyword pairs in clauses
        {state, [], meta}
      end

    ast = {:for, meta, clauses ++ body_kw}
    {state, ast}
  end

  defp parse_for_clauses(state) do
    {state, clause} = parse_expression(state, 0)

    case State.eat(state, :comma) do
      {:ok, state, _} ->
        if State.at?(state, :do) or State.at?(state, :kw_identifier) do
          # Check if it's do: keyword
          if State.at?(state, :kw_identifier) do
            {state, kw} = parse_keyword_pairs(state)
            {state, [clause | kw]}
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

  # ============================================================================
  # Helper: Parse block with stab clauses
  # ============================================================================

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
    # Stop at clause/block terminators or definition keywords (for recovery)
    if State.at?(state, :end) or State.at?(state, :else) or
         State.at?(state, :rescue) or State.at?(state, :catch) or
         State.at?(state, :after) or State.at_end?(state) or
         State.at?(state, :def) or State.at?(state, :defp) or
         State.at?(state, :defmacro) or State.at?(state, :defmacrop) or
         State.at?(state, :defmodule) do
      {state, acc}
    else
      state = State.advance_push(state)
      {state, expr} = parse_expression(state, 0)
      state = State.advance_pop!(state)

      acc = if expr, do: [expr | acc], else: acc

      # Check for new stab clause AFTER parsing, not before
      if looks_like_new_stab_clause?(state) do
        {state, acc}
      else
        parse_stab_body_exprs(state, acc)
      end
    end
  end

  defp looks_like_new_stab_clause?(state) do
    # Check if current position looks like start of a new clause
    peek_for_arrow(state, 0, 20)
  end

  # ============================================================================
  # Helper: Parse block until terminator
  # ============================================================================

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
