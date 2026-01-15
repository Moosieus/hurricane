code = ~S|defmodule(:"Elixir.Wibble", [{:do, [def(wobble(input), [{:do, :"Elixir.IO".inspect(input)}])]}])|

case Hurricane.parse(code) do
  {:ok, ast} ->
    elixir_ast = Code.string_to_quoted!(code, columns: true, token_metadata: true)
    if ast == elixir_ast do
      IO.puts("✓ Desugared Elixir: EXACT MATCH")
    else
      IO.puts("✗ Desugared Elixir: AST mismatch")
      IO.puts("\nOur AST:")
      IO.inspect(ast, pretty: true, limit: :infinity)
      IO.puts("\nElixir AST:")
      IO.inspect(elixir_ast, pretty: true, limit: :infinity)
    end
  {:ok, _, errors} ->
    IO.puts("✗ Desugared Elixir: #{length(errors)} errors")
    IO.inspect(errors, pretty: true)
end
