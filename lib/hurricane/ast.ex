defmodule Hurricane.Ast do
  @moduledoc """
  AST construction helpers.

  Builds standard Elixir AST nodes that match `Code.string_to_quoted/2`
  with `columns: true, token_metadata: true`.
  """

  # ============================================================================
  # Standard AST Nodes
  # ============================================================================

  @doc """
  Build a function/macro call node.

  ## Examples

      call(:foo, meta, [arg1, arg2])
      #=> {:foo, meta, [arg1, arg2]}
  """
  def call(name, meta, args) when is_atom(name) and is_list(meta) and is_list(args) do
    {name, meta, args}
  end

  @doc """
  Build a variable reference.

  Variables have `nil` as their third element, not an empty list.
  """
  def var(name, meta) when is_atom(name) and is_list(meta) do
    {name, meta, nil}
  end

  @doc """
  Build a binary operator node.
  """
  def binary_op(op, meta, left, right) when is_atom(op) do
    {op, meta, [left, right]}
  end

  @doc """
  Build a unary operator node.
  """
  def unary_op(op, meta, operand) when is_atom(op) do
    {op, meta, [operand]}
  end

  @doc """
  Build a block node (multiple expressions).

  Single expressions are returned unwrapped.
  """
  def block([], _meta), do: nil

  def block([single], _meta), do: single

  def block(exprs, meta) when is_list(exprs) do
    {:__block__, meta, exprs}
  end

  @doc """
  Build a module alias node.

  ## Examples

      alias_node([:Foo, :Bar], meta, last_token)
      #=> {:__aliases__, [last: [...], line: ..., column: ...], [:Foo, :Bar]}
  """
  def alias_node(segments, meta, last_token \\ nil) when is_list(segments) do
    # Elixir includes 'last' metadata for the last segment position
    meta = if last_token do
      last_meta = token_meta(last_token)
      [{:last, last_meta} | meta]
    else
      meta
    end

    {:__aliases__, meta, segments}
  end

  @doc """
  Build a module definition.
  """
  def defmodule(alias_ast, body, meta) do
    {:defmodule, meta, [alias_ast, body]}
  end

  @doc """
  Build a function definition.
  """
  def def_node(kind, call_ast, body, meta) when kind in [:def, :defp, :defmacro, :defmacrop] do
    {kind, meta, [call_ast, body]}
  end

  @doc """
  Build a do block as keyword list.
  """
  def do_block(body) do
    [do: body]
  end

  @doc """
  Build a keyword list entry.
  """
  def keyword_pair(key, value) when is_atom(key) do
    {key, value}
  end

  # ============================================================================
  # Collections
  # ============================================================================

  @doc """
  Build a tuple node.

  2-element tuples are literal, 3+ use `:{}`
  """
  def tuple([a, b], _meta), do: {a, b}

  def tuple(elements, meta) when is_list(elements) do
    {:{}, meta, elements}
  end

  @doc """
  Build a map node.
  """
  def map(pairs, meta) do
    {:%{}, meta, pairs}
  end

  @doc """
  Build a struct node.
  """
  def struct(alias_ast, map_ast, meta) do
    {:%, meta, [alias_ast, map_ast]}
  end

  @doc """
  Build a binary/bitstring node.
  """
  def binary(elements, meta) do
    {:<<>>, meta, elements}
  end

  # ============================================================================
  # Special Forms
  # ============================================================================

  @doc """
  Build a stab clause (-> clause in case/cond/fn).
  """
  def stab(patterns, body, meta) do
    {:->, meta, [patterns, body]}
  end

  @doc """
  Build a case expression.
  """
  def case_expr(expr, clauses, meta) do
    {:case, meta, [expr, [do: clauses]]}
  end

  @doc """
  Build a cond expression.
  """
  def cond_expr(clauses, meta) do
    {:cond, meta, [[do: clauses]]}
  end

  @doc """
  Build an anonymous function.
  """
  def fn_expr(clauses, meta) do
    {:fn, meta, clauses}
  end

  @doc """
  Build a with expression.
  """
  def with_expr(clauses, body, meta) do
    {:with, meta, clauses ++ [body]}
  end

  @doc """
  Build a module attribute reference or definition.
  """
  def attribute(name_ast, meta) do
    {:@, meta, [name_ast]}
  end

  # ============================================================================
  # Error Nodes
  # ============================================================================

  @doc """
  Build an error node.

  Error nodes are `{:__block__, [error: true | meta], []}`.
  They are valid AST nodes that tooling can skip.
  """
  def error(meta) do
    {:__block__, [error: true] ++ meta, []}
  end

  @doc """
  Build an error node at a token's position.
  """
  def error_at(token) do
    meta = token_meta(token)
    error(meta)
  end

  # ============================================================================
  # Metadata Helpers
  # ============================================================================

  @doc """
  Build metadata from a token.
  """
  def token_meta(nil), do: [line: 1, column: 1]

  def token_meta(%{line: line, column: column}) do
    [line: line, column: column]
  end

  @doc """
  Build metadata with line and column.
  """
  def meta(line, column) do
    [line: line, column: column]
  end

  @doc """
  Add closing delimiter info to metadata.
  """
  def with_closing(meta, token) do
    closing_meta = token_meta(token)
    Keyword.put(meta, :closing, closing_meta)
  end

  @doc """
  Add do/end location info to metadata.
  Elixir expects: [do: ..., end: ..., line: ..., column: ...]
  """
  def with_do_end(meta, do_token, end_token) do
    # Build in correct order: do, end, then original keys
    base = Keyword.drop(meta, [:do, :end])

    result = []
    result = if do_token, do: [{:do, token_meta(do_token)} | result], else: result
    result = if end_token, do: [{:end, token_meta(end_token)} | result], else: result

    # Reverse so do comes before end, then append base
    Enum.reverse(result) ++ base
  end
end
