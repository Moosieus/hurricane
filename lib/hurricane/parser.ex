defmodule Hurricane.Parser do
  @moduledoc """
  Main parser entry point.

  Coordinates tokenization and parsing to produce Elixir AST.
  """

  alias Hurricane.Lexer
  alias Hurricane.Parser.{State, Structure}

  @doc """
  Parse source code into an Elixir AST.

  Returns `{:ok, ast}` on success (even with errors - errors are AST nodes).
  Returns `{:error, reason}` only for catastrophic failures.
  """
  def parse(source) when is_binary(source) do
    with {:ok, tokens} <- Lexer.tokenize(source) do
      state = State.new(tokens)
      {state, ast} = Structure.parse_top_level(state)

      errors = State.errors(state)

      if errors == [] do
        {:ok, ast}
      else
        {:ok, ast, errors}
      end
    end
  end

  @doc """
  Parse source code, raising on complete failure.

  Note: This will NOT raise on syntax errors in the source code.
  Syntax errors become error nodes in the AST.
  It only raises on bugs in the parser itself.
  """
  def parse!(source) when is_binary(source) do
    case parse(source) do
      {:ok, ast} -> ast
      {:ok, ast, _errors} -> ast
      {:error, reason} -> raise "Parser failed: #{inspect(reason)}"
    end
  end
end
