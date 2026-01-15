defmodule Hurricane do
  @moduledoc """
  Hurricane: A resilient Elixir parser for IDE/LSP use.

  Hurricane produces standard Elixir AST that matches `Code.string_to_quoted/2`,
  but never crashes on malformed input. Instead, errors become AST nodes that
  can be pattern matched and skipped by downstream tooling.

  ## Usage

      {:ok, ast} = Hurricane.parse("defmodule Foo do def bar, do: :ok end")

      # For broken code, still returns an AST with error nodes
      {:ok, ast, errors} = Hurricane.parse("def foo(")

  ## Features

  - **Resilient**: Always returns an AST, even for broken code
  - **Compatible**: Output matches `Code.string_to_quoted` for valid input
  - **Predictable**: Uses explicit recovery sets, not ad-hoc heuristics
  - **Debuggable**: Stuck parser = immediate crash with exact location

  ## Architecture

  Hurricane uses a hybrid LL (recursive descent) + Pratt parsing architecture:

  **Level 1: Structure vs Expression**
  - `Hurricane.Parser.Structure` uses recursive descent for module-level constructs
    (defmodule, def, module body)
  - `Hurricane.Parser.Expression` handles everything inside expression contexts

  **Level 2: Within Expression**
  - **Pratt parsing** for the outer expression loop - handles operator precedence,
    infix/prefix operators, and combines sub-expressions
  - **Recursive descent** for complex forms like `case`, `cond`, `fn`, `with`, `try`

  This hybrid approach gives us the best of both worlds: clean LL parsing for
  structure with clear error recovery, and Pratt parsing for expressions where
  operator precedence matters.

  See individual module docs for implementation details.
  """

  alias Hurricane.Parser

  @doc """
  Parse source code into an Elixir AST.

  Returns:
  - `{:ok, ast}` for valid code
  - `{:ok, ast, errors}` for code with syntax errors (AST contains error nodes)

  ## Options

  Currently no options are supported. Future options may include:
  - `:file` - filename for error messages

  ## Examples

      iex> Hurricane.parse("1 + 2")
      {:ok, {:+, [line: 1, column: 3], [1, 2]}}

      iex> {:ok, ast} = Hurricane.parse("defmodule Foo do end")
      iex> match?({:defmodule, _, _}, ast)
      true
  """
  defdelegate parse(source), to: Parser

  @doc """
  Parse source code, returning AST directly.

  Raises only on internal parser bugs, NOT on syntax errors in the source.
  Syntax errors become error nodes in the returned AST.

  ## Examples

      iex> Hurricane.parse!("1 + 2")
      {:+, [line: 1, column: 3], [1, 2]}
  """
  defdelegate parse!(source), to: Parser
end
