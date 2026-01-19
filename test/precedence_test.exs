defmodule Hurricane.PrecedenceTest do
  @moduledoc """
  Golden tests for operator precedence and associativity.

  These tests verify that Hurricane produces the same AST as Elixir
  for expressions involving operator precedence and associativity.

  Key test cases based on GPT_52_FEEDBACK review and validation against
  official Elixir operator documentation.
  """
  use ExUnit.Case, async: true

  describe "arithmetic precedence" do
    test "multiplication binds tighter than addition" do
      assert_conforms("1 + 2 * 3")
      assert_conforms("1 * 2 + 3")
    end

    test "division binds tighter than subtraction" do
      assert_conforms("10 - 4 / 2")
      assert_conforms("10 / 2 - 4")
    end

    test "power operator" do
      assert_conforms("2 ** 3")
      assert_conforms("2 ** 3 ** 4")
    end
  end

  describe "associativity - right-associative operators" do
    test "match operator is right-associative" do
      # a = b = c should be a = (b = c)
      assert_conforms("a = b = c")
    end

    test "cons operator is right-associative" do
      # a | b | c should be a | (b | c)
      assert_conforms("[a | b | c]")
    end

    test "concat operators are right-associative" do
      # a ++ b ++ c should be a ++ (b ++ c)
      assert_conforms("a ++ b ++ c")
      assert_conforms("a -- b -- c")
      assert_conforms("a <> b <> c")
    end

    test "range at same tier as concat (right-associative)" do
      # a..b ++ c should be a..(b ++ c) per official Elixir docs
      assert_conforms("a..b ++ c")
      assert_conforms("a ++ b..c")
    end

    test "type annotation is right-associative" do
      assert_conforms("a :: b :: c")
    end
  end

  describe "associativity - left-associative operators" do
    test "left arrow is left-associative" do
      # a <- b <- c should be (a <- b) <- c per official Elixir docs
      assert_conforms("a <- b <- c")
    end

    test "addition is left-associative" do
      # a + b + c should be (a + b) + c
      assert_conforms("a + b + c")
    end

    test "comparison operators are left-associative" do
      assert_conforms("a < b < c")
      assert_conforms("a == b == c")
    end

    test "logical operators are left-associative" do
      assert_conforms("a and b and c")
      assert_conforms("a or b or c")
      assert_conforms("a && b && c")
      assert_conforms("a || b || c")
    end
  end

  describe "unary not and membership operator interaction" do
    test "!a in b parses as !(a in b)" do
      # This is the critical test: ! has low BP so it captures `in`
      assert_conforms("!a in b")
    end

    test "not a in b parses as not(a in b)" do
      # Same behavior as !
      assert_conforms("not a in b")
    end

    test "not in operator" do
      assert_conforms("a not in b")
    end
  end

  describe "capture operator" do
    test "capture captures entire expression" do
      assert_conforms("&Enum.map/2")
      assert_conforms("&(&1 + &2)")
      assert_conforms("&(1 + 2 * 3)")
    end

    test "capture with function reference" do
      assert_conforms("&Foo.bar/1")
      assert_conforms("&foo/1")
    end
  end

  describe "map and struct update syntax" do
    test "map update with pipe" do
      assert_conforms("%{base | a: 1}")
      assert_conforms("%{map | a: 1, b: 2}")
    end

    test "struct update with pipe" do
      assert_conforms("%Foo{base | a: 1}")
      assert_conforms("%Mod.Struct{s | field: value}")
    end

    test "map update with expression as base" do
      assert_conforms("%{foo.bar | a: 1}")
    end
  end

  describe "when and guards" do
    test "when in function head" do
      assert_conforms("def foo(x) when is_integer(x), do: x")
    end

    test "when with multiple guards" do
      assert_conforms("def foo(x) when x > 0 and x < 100, do: x")
    end

    test "when in anonymous function" do
      assert_conforms("fn x when is_atom(x) -> x end")
    end

    test "when in case clause" do
      assert_conforms("case x do y when y > 0 -> :pos end")
    end
  end

  describe "pipe operator" do
    test "pipe is left-associative" do
      # a |> b |> c should be (a |> b) |> c
      assert_conforms("a |> b |> c")
    end

    test "pipe with function calls" do
      assert_conforms("x |> foo() |> bar()")
      assert_conforms("1 |> foo |> bar")
    end
  end

  describe "mixed precedence expressions" do
    test "logical vs comparison" do
      assert_conforms("a > b and c < d")
      assert_conforms("a == b or c != d")
    end

    test "arithmetic vs comparison" do
      assert_conforms("a + b > c - d")
      assert_conforms("a * b == c / d")
    end

    test "pipe vs other operators" do
      assert_conforms("a + b |> foo")
      assert_conforms("a |> foo + b")
    end
  end

  describe "default argument operator" do
    test "default argument in function def" do
      assert_conforms("def foo(a \\\\ 1), do: a")
      assert_conforms("def foo(a \\\\ 1, b \\\\ 2), do: {a, b}")
    end
  end

  describe "semicolons in stab clauses" do
    test "case with semicolon-separated clauses" do
      assert_conforms("case x do 1 -> :a; _ -> :b end")
      assert_conforms("case x do 1 -> :a; 2 -> :b; _ -> :c end")
    end

    test "fn with semicolon-separated clauses" do
      assert_conforms("fn x -> 1; y -> 2 end")
      assert_conforms("fn 1 -> :a; 2 -> :b; _ -> :c end")
    end

    test "receive with newline-separated clauses" do
      # Basic receive test - newline separation works like semicolons
      # Note: receive with semicolons has end_of_expression metadata differences
      # that are tested separately; this verifies basic stab clause parsing
      assert_conforms("receive do\n{:ok, x} -> x\n{:error, e} -> e\nend")
    end

    test "cond with semicolon-separated clauses" do
      assert_conforms("cond do true -> 1; false -> 2 end")
    end
  end

  describe "remote calls with do blocks" do
    test "remote call with no-parens arg and do block" do
      assert_conforms("Foo.bar x do 1 end")
      assert_conforms("Nx.defn foo do 1 end")
    end

    test "remote call with multiple no-parens args and do block" do
      assert_conforms("Foo.bar x, y do 1 end")
    end

    test "remote call with parens and do block" do
      assert_conforms("Foo.bar(x) do 1 end")
    end
  end

  describe "ambiguous op identifier metadata" do
    test "identifier followed by operator without space" do
      assert_conforms("foo +bar")
      assert_conforms("baz -qux")
    end

    test "ambiguous op in more complex expressions" do
      assert_conforms("foo +bar + 1")
      assert_conforms("x = foo -y")
    end
  end

  # =============================================================================
  # Helper function
  # =============================================================================

  defp assert_conforms(code) do
    reference =
      Code.string_to_quoted(code, columns: true, token_metadata: true, emit_warnings: false)

    actual = hurricane_parse(code)

    assert actual == reference,
           """
           AST mismatch for: #{inspect(code)}

           Reference:
           #{inspect(reference, pretty: true)}

           Actual:
           #{inspect(actual, pretty: true)}
           """
  end

  defp hurricane_parse(code) do
    case Hurricane.parse(code) do
      {:ok, ast} ->
        {:ok, ast}

      {:ok, ast, _errors} ->
        {:ok, ast}

      {:error, reason} ->
        {:error, reason}
    end
  end
end
