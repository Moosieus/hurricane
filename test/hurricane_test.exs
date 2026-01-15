defmodule HurricaneTest do
  use ExUnit.Case
  doctest Hurricane

  describe "parse/1" do
    test "parses simple expression" do
      assert {:ok, ast} = Hurricane.parse("1 + 2")
      assert {:+, _, [1, 2]} = ast
    end

    test "parses module definition" do
      code = "defmodule Foo do def bar, do: 1 end"
      assert {:ok, ast} = Hurricane.parse(code)
      assert {:defmodule, _, [{:__aliases__, _, [:Foo]}, _]} = ast
    end

    test "returns errors for incomplete code" do
      code = "defmodule Foo do def bar("
      assert {:ok, _ast, errors} = Hurricane.parse(code)
      assert length(errors) > 0
    end

    test "never crashes on malformed input" do
      malformed_codes = [
        "(((",
        "def def def",
        "end end end",
        "][}{",
        String.duplicate("[", 50)
      ]

      for code <- malformed_codes do
        result = Hurricane.parse(code)
        assert match?({:ok, _}, result) or match?({:ok, _, _}, result),
               "Parser crashed on: #{inspect(code)}"
      end
    end
  end

  describe "AST matching" do
    test "matches Code.string_to_quoted for simple expressions" do
      codes = [
        "1 + 2",
        "a = b",
        "foo(1, 2)",
        ":atom",
        "[1, 2, 3]",
        "{:ok, value}"
      ]

      for code <- codes do
        {:ok, our_ast} = Hurricane.parse(code)
        {:ok, elixir_ast} = Code.string_to_quoted(code, columns: true, token_metadata: true)
        # Strip end_of_expression which we don't track
        elixir_ast = strip_metadata(elixir_ast, [:end_of_expression])
        assert our_ast == elixir_ast, "Mismatch for: #{code}"
      end
    end

    test "matches Code.string_to_quoted for basic module" do
      code = """
      defmodule Foo do
        def bar, do: 1
      end
      """

      {:ok, our_ast} = Hurricane.parse(code)
      {:ok, elixir_ast} = Code.string_to_quoted(code, columns: true, token_metadata: true)
      elixir_ast = strip_metadata(elixir_ast, [:end_of_expression, :newlines])
      assert our_ast == elixir_ast
    end
  end

  # Helper to strip specific metadata keys from AST
  defp strip_metadata(ast, keys) do
    Macro.postwalk(ast, fn
      {name, meta, args} when is_list(meta) ->
        meta = Enum.reduce(keys, meta, &Keyword.delete(&2, &1))
        {name, meta, args}

      other ->
        other
    end)
  end
end
