defmodule Hurricane.Parser.Structure do
  @moduledoc """
  Recursive descent parser for Elixir structure.

  Handles top-level forms like defmodule, def, and module body items.
  Delegates to Expression parser for expression parsing.
  """

  alias Hurricane.Ast
  alias Hurricane.Parser.{State, Recovery, Expression}

  ## TOP LEVEL

  @doc """
  Parse the entire source file as a top-level expression or block.
  """
  def parse_top_level(state) do
    {state, exprs} = parse_top_level_items(state, [])

    ast =
      case exprs do
        [] -> nil
        [single] -> single
        multiple -> Ast.block(multiple, [])
      end

    {state, ast}
  end

  defp parse_top_level_items(state, acc) do
    if State.at_end?(state) do
      {state, Enum.reverse(acc)}
    else
      state = State.advance_push(state)
      {state, expr} = parse_top_level_item(state)
      state = State.advance_pop!(state)

      acc = if expr, do: [expr | acc], else: acc
      parse_top_level_items(state, acc)
    end
  end

  defp parse_top_level_item(state) do
    cond do
      State.at?(state, :defmodule) ->
        parse_defmodule(state)

      State.at?(state, :def) ->
        parse_def(state, :def)

      State.at?(state, :defp) ->
        parse_def(state, :defp)

      State.at?(state, :defmacro) ->
        parse_def(state, :defmacro)

      State.at?(state, :defmacrop) ->
        parse_def(state, :defmacrop)

      State.at?(state, :@) ->
        parse_attribute(state)

      # Stray :end tokens from incomplete structures - skip with error
      State.at?(state, :end) ->
        state = State.add_error(state, "unexpected end")
        {state, _} = State.advance(state)
        {state, nil}

      # Any other token: try to parse as expression
      true ->
        Expression.parse_expression(state)
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
    ast = Ast.block(Enum.reverse(items), [])
    {state, ast}
  end

  defp parse_module_body_items(state, acc) do
    cond do
      State.at?(state, :end) or State.at_end?(state) ->
        {state, acc}

      Recovery.at_recovery?(state, Recovery.block_body()) ->
        {state, acc}

      true ->
        state = State.advance_push(state)
        {state, item} = parse_module_body_item(state)
        state = State.advance_pop!(state)

        acc = if item, do: [item | acc], else: acc
        parse_module_body_items(state, acc)
    end
  end

  defp parse_module_body_item(state) do
    cond do
      State.at?(state, :def) -> parse_def(state, :def)
      State.at?(state, :defp) -> parse_def(state, :defp)
      State.at?(state, :defmacro) -> parse_def(state, :defmacro)
      State.at?(state, :defmacrop) -> parse_def(state, :defmacrop)
      State.at?(state, :defmodule) -> parse_defmodule(state)
      State.at?(state, :@) -> parse_attribute(state)
      State.at?(state, :use) -> parse_directive(state, :use)
      State.at?(state, :import) -> parse_directive(state, :import)
      State.at?(state, :alias_directive) -> parse_directive(state, :alias)
      State.at?(state, :require) -> parse_directive(state, :require)
      Recovery.at_recovery?(state, Recovery.module_body()) -> {state, nil}
      # Any other token: try to parse as expression
      true -> Expression.parse_expression(state)
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
        {state, params} = parse_params(state)
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

    # Parse body (do block or comma do:)
    {state, body, do_token, end_token} =
      cond do
        State.at?(state, :do) ->
          parse_do_block(state, &parse_block_body/1)

        State.at?(state, :comma) ->
          {state, _comma} = State.advance(state)
          parse_keyword_do(state)

        true ->
          # No body - incomplete function
          state = State.add_error(state, "expected 'do' block or ', do:'")
          {state, Ast.do_block(nil), nil, nil}
      end

    meta = Ast.with_do_end(meta, do_token, end_token)
    ast = Ast.def_node(kind, call_ast, body, meta)

    {state, ast}
  end

  defp parse_function_name(state) do
    cond do
      State.at?(state, :identifier) ->
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

  ## PARAMETERS

  defp parse_params(state) do
    if State.at?(state, :rparen) or Recovery.at_recovery?(state, Recovery.params()) do
      {state, []}
    else
      {state, param} = parse_param(state)
      {state, rest} = parse_params_rest(state)
      {state, [param | rest]}
    end
  end

  defp parse_params_rest(state) do
    case State.eat(state, :comma) do
      {:ok, state, _} ->
        if Recovery.at_recovery?(state, Recovery.params()) do
          {state, []}
        else
          {state, param} = parse_param(state)
          {state, rest} = parse_params_rest(state)
          {state, [param | rest]}
        end

      {:error, state} ->
        {state, []}
    end
  end

  defp parse_param(state) do
    # Parameters can be any pattern - use expression parser
    # The expression parser handles atoms, tuples, variables, etc.
    if Recovery.at_recovery?(state, Recovery.params()) do
      {state, Ast.error(State.current_meta(state))}
    else
      Expression.parse_expression(state)
    end
  end

  ## GUARDS

  defp parse_guard_expression(state) do
    Expression.parse_expression(state)
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
        {state, body} = Expression.parse_expression(state)
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

        acc = if expr, do: [expr | acc], else: acc
        parse_block_body_items(state, acc)
    end
  end

  defp parse_block_body_item(state) do
    Expression.parse_expression(state)
  end

  ## MODULE ATTRIBUTES

  defp parse_attribute(state) do
    {state, at_token} = State.expect(state, :@)
    meta = Ast.token_meta(at_token)

    # Parse attribute name
    {state, name_ast} =
      if State.at?(state, :identifier) do
        token = State.current(state)
        {state, _} = State.advance(state)
        name_meta = Ast.token_meta(token)

        # Check if there's a value
        if State.at_any?(state, [
             :string,
             :integer,
             :atom,
             :identifier,
             :alias,
             :lbracket,
             :lbrace,
             true,
             false,
             nil
           ]) or
             State.at?(state, :lparen) do
          # Has value - parse as call
          {state, value} = Expression.parse_expression(state)
          {state, Ast.call(token.value, name_meta, [value])}
        else
          # No value - reference
          {state, Ast.var(token.value, name_meta)}
        end
      else
        state = State.add_error(state, "expected attribute name")
        {state, Ast.error(State.current_meta(state))}
      end

    ast = Ast.attribute(name_ast, meta)
    {state, ast}
  end

  ## DIRECTIVES (use, import, alias, require)

  defp parse_directive(state, kind) do
    {state, directive_token} = State.advance(state)
    meta = Ast.token_meta(directive_token)

    {state, alias_ast} = parse_module_alias(state)

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
      {state, expr} = Expression.parse_expression(state, 0)

      if State.at?(state, :comma) do
        {state, _comma} = State.advance(state)
        parse_directive_options(state, [expr | acc])
      else
        {state, Enum.reverse([expr | acc])}
      end
    end
  end
end
