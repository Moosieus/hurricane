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
      # Strip metadata that varies between implementations
      our_ast = strip_metadata(our_ast, [:end_of_expression, :newlines])
      elixir_ast = strip_metadata(elixir_ast, [:end_of_expression, :newlines])
      assert our_ast == elixir_ast
    end

    test "matches Code.string_to_quoted for struct literals" do
      codes = [
        "%Foo{}",
        "%Foo{bar: 1}",
        "%Foo.Bar{a: 1, b: 2}"
      ]

      for code <- codes do
        {:ok, our_ast} = Hurricane.parse(code)
        {:ok, elixir_ast} = Code.string_to_quoted(code, columns: true, token_metadata: true)
        assert our_ast == elixir_ast, "Mismatch for: #{code}"
      end
    end

    test "matches Code.string_to_quoted for sigils" do
      codes = [
        "~r/test/",
        "~s(hello)",
        "~w[one two three]",
        "~S{raw string}",
        "~r/test/i"
      ]

      for code <- codes do
        {:ok, our_ast} = Hurricane.parse(code)
        {:ok, elixir_ast} = Code.string_to_quoted(code, columns: true, token_metadata: true)
        assert our_ast == elixir_ast, "Mismatch for: #{code}"
      end
    end

    test "matches Code.string_to_quoted for heredocs" do
      code = ~S|"""
hello
world
"""|
      {:ok, our_ast} = Hurricane.parse(code)
      {:ok, elixir_ast} = Code.string_to_quoted(code, columns: true, token_metadata: true)
      assert our_ast == elixir_ast
    end
  end

  describe "multi-clause anonymous functions" do
    test "parses fn with newline-separated clauses" do
      code = """
      fn
        x -> x + 1
        y -> y * 2
      end
      """

      {:ok, ast} = Hurricane.parse(code)
      {:fn, _meta, clauses} = ast
      assert length(clauses) == 2
    end

    test "matches Elixir for multi-clause fn in pipe" do
      code = """
      Enum.map(fn
        v when is_atom(v) -> Atom.to_string(v)
        v -> to_string(v)
      end)
      """

      {:ok, our_ast} = Hurricane.parse(code)
      {:ok, elixir_ast} = Code.string_to_quoted(code, columns: true, token_metadata: true)
      our_ast = strip_metadata(our_ast, [:end_of_expression, :newlines])
      elixir_ast = strip_metadata(elixir_ast, [:end_of_expression, :newlines])
      assert our_ast == elixir_ast
    end

    test "parses fn with semicolon-separated clauses" do
      code = "fn x -> x; y -> y end"

      {:ok, ast} = Hurricane.parse(code)
      {:fn, _meta, clauses} = ast
      assert length(clauses) == 2
    end

    test "parses fn with guards in multiple clauses" do
      code = """
      fn
        x when is_integer(x) -> :int
        x when is_binary(x) -> :string
        _ -> :other
      end
      """

      {:ok, ast} = Hurricane.parse(code)
      {:fn, _meta, clauses} = ast
      assert length(clauses) == 3
    end
  end

  describe "parser recovery" do
    test "recovers from orphan closing delimiters" do
      codes = [
        "defmodule Foo do ) end",
        "defmodule Foo do ] end",
        "defmodule Foo do } end"
      ]

      for code <- codes do
        result = Hurricane.parse(code)
        assert match?({:ok, _, _}, result), "Parser crashed on: #{inspect(code)}"

        {:ok, _ast, errors} = result
        assert length(errors) > 0, "Expected errors for: #{inspect(code)}"
      end
    end

    test "recovers from stray block keywords" do
      codes = [
        "1 + 2\ndo\n3",
        "foo()\nrescue\nbar()",
        "x\ncatch\ny"
      ]

      for code <- codes do
        result = Hurricane.parse(code)

        assert match?({:ok, _}, result) or match?({:ok, _, _}, result),
               "Parser crashed on: #{inspect(code)}"
      end
    end

    test "recovers from stray -> tokens" do
      codes = [
        "1 + 2\n-> 3",
        "defmodule Foo do\n->\ndef bar, do: 1\nend"
      ]

      for code <- codes do
        result = Hurricane.parse(code)

        assert match?({:ok, _}, result) or match?({:ok, _, _}, result),
               "Parser crashed on: #{inspect(code)}"
      end
    end

    test "recovers from incomplete case and continues parsing" do
      code = """
      defmodule Foo do
        def broken do
          case x do
            :a ->
          end
        end

        def working, do: :ok
      end
      """

      result = Hurricane.parse(code)

      ast =
        case result do
          {:ok, ast} -> ast
          {:ok, ast, _errors} -> ast
        end

      # Should still parse the working function
      {:defmodule, _, [_, [do: body]]} = ast

      # Find def nodes in the body
      defs =
        case body do
          {:__block__, _, items} -> items
          item -> [item]
        end
        |> Enum.filter(&match?({:def, _, _}, &1))

      assert length(defs) >= 1, "Should parse at least the working function"
    end

    test "recovers from incomplete fn inside expression" do
      # This pattern appears in production code: fn inside case/with
      code = """
      case Repo.transaction(fn ->
        user
      end) do
        {:ok, user} -> user
      end
      """

      result = Hurricane.parse(code)

      assert match?({:ok, _}, result) or match?({:ok, _, _}, result),
             "Parser crashed on fn inside case"
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
