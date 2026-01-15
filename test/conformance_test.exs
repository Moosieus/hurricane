defmodule Hurricane.ConformanceTest do
  @moduledoc """
  Conformance tests comparing Hurricane output against `Code.string_to_quoted/2`.

  These tests verify that the parser produces identical AST to the reference Elixir parser
  for valid inputs. The test structure mirrors `elixir_parser.yrl` nonterminals.

  Adapted from toxic_parser's comprehensive test suite.
  """
  use ExUnit.Case, async: true

  # =============================================================================
  # TERMINALS - Basic building blocks that are valid as standalone expressions
  # =============================================================================

  describe "terminals - literals" do
    test "true" do
      assert_conforms("true")
    end

    test "false" do
      assert_conforms("false")
    end

    test "nil" do
      assert_conforms("nil")
    end
  end

  describe "terminals - integers (int)" do
    test "decimal integer" do
      assert_conforms("1")
      assert_conforms("42")
      assert_conforms("1_000_000")
    end

    test "negative integer" do
      assert_conforms("-1")
      assert_conforms("-42")
    end

    test "binary integer" do
      assert_conforms("0b101")
      assert_conforms("0b1010_1010")
    end

    test "octal integer" do
      assert_conforms("0o777")
      assert_conforms("0o12_34")
    end

    test "hexadecimal integer" do
      assert_conforms("0xDEAD")
      assert_conforms("0xBEEF")
      assert_conforms("0xdead_beef")
      assert_conforms("0xFF")
    end
  end

  describe "terminals - floats (flt)" do
    test "simple float" do
      assert_conforms("1.0")
      assert_conforms("3.14")
      assert_conforms("0.5")
    end

    test "float with underscores" do
      assert_conforms("1_000.000_001")
    end

    test "float with exponent" do
      assert_conforms("1.0e10")
      assert_conforms("1.0E10")
      assert_conforms("1.0e-10")
      assert_conforms("1.0e+10")
    end

    test "negative float" do
      assert_conforms("-1.0")
      assert_conforms("-3.14e-10")
    end
  end

  describe "terminals - character literals (char)" do
    test "simple character" do
      assert_conforms("?a")
      assert_conforms("?Z")
      assert_conforms("?0")
    end

    test "escaped character" do
      assert_conforms("?\\n")
      assert_conforms("?\\t")
      assert_conforms("?\\r")
      assert_conforms("?\\s")
      assert_conforms("?\\\\")
    end

    test "special characters" do
      assert_conforms("? ")
      assert_conforms("?!")
      assert_conforms("??")
    end
  end

  describe "terminals - atoms (atom)" do
    test "simple atom" do
      assert_conforms(":foo")
      assert_conforms(":bar")
      assert_conforms(":baz")
    end

    test "atom with underscore" do
      assert_conforms(":foo_bar")
      assert_conforms(":_private")
    end

    test "atom with numbers" do
      assert_conforms(":foo123")
      assert_conforms(":v1")
    end

    test "atom ending with ? or !" do
      assert_conforms(":foo?")
      assert_conforms(":bar!")
    end

    test "atom with @" do
      assert_conforms(":foo@bar")
    end

    test "operator atoms" do
      assert_conforms(":<<>>")
      assert_conforms(":%{}")
      assert_conforms(":%")
      assert_conforms(":{}")
      assert_conforms(":..//")
    end

    test "operators as atoms" do
      # 3 char
      assert_conforms(":~~~")
      assert_conforms(":===")
      assert_conforms(":!==")
      assert_conforms(":&&&")
      assert_conforms(":|||")
      assert_conforms(":<<<")
      assert_conforms(":>>>")
      assert_conforms(":~>>")
      assert_conforms(":<<~")
      assert_conforms(":<~>")
      assert_conforms(":<|>")
      assert_conforms(":^^^")
      assert_conforms(":+++")
      assert_conforms(":---")
      assert_conforms(":...")

      # 2 char
      assert_conforms(":::")
      assert_conforms(":==")
      assert_conforms(":!=")
      assert_conforms(":=~")
      assert_conforms(":>=")
      assert_conforms(":<=")
      assert_conforms(":&&")
      assert_conforms(":||")
      assert_conforms(":|>")
      assert_conforms(":~>")
      assert_conforms(":<~")
      assert_conforms(":<-")
      assert_conforms(":\\\\")
      assert_conforms(":++")
      assert_conforms(":--")
      assert_conforms(":**")
      assert_conforms(":->")
      assert_conforms(":..")

      # 1 char
      assert_conforms(":@")
      assert_conforms(":!")
      assert_conforms(":^")
      assert_conforms(":&")
      assert_conforms(":+")
      assert_conforms(":-")
      assert_conforms(":*")
      assert_conforms(":/")
      assert_conforms(":<")
      assert_conforms(":>")
      assert_conforms(":=")
      assert_conforms(":|")
      assert_conforms(":.")
    end

    test "special atoms" do
      assert_conforms(":true")
      assert_conforms(":false")
      assert_conforms(":nil")
    end
  end

  describe "terminals - quoted atoms (atom_quoted)" do
    test "quoted atom with spaces" do
      assert_conforms(~s(:"foo bar"))
    end

    test "quoted atom with special characters" do
      assert_conforms(~s(:"foo-bar"))
      assert_conforms(~s(:"foo.bar"))
    end

    test "quoted atom with escapes" do
      assert_conforms(~s(:"foo\\nbar"))
      assert_conforms(~s(:"foo\\tbar"))
    end

    test "empty quoted atom" do
      assert_conforms(~s(:""))
    end

    test "quoted atom with unicode" do
      assert_conforms(~s(:"hello\\u0041"))
    end

    test "single-quoted atom" do
      assert_conforms(~s(:'foo bar'))
      assert_conforms(~s(:'hello world'))
    end

    test "quoted atom interpolated" do
      assert_conforms(~s(:"hello\#{abc}foo"))
      assert_conforms(":\"foo\#{}\"")
      assert_conforms(":\"foo\#{''}\"")
    end
  end

  describe "terminals - strings" do
    test "empty bin string" do
      assert_conforms(~s(""))
    end

    test "empty list string" do
      assert_conforms(~s(''))
    end

    test "bin string" do
      assert_conforms(~s("foo"))
    end

    test "list string" do
      assert_conforms(~s('foo'))
    end

    test "bin string with nl" do
      assert_conforms(~s("fo\\no"))
    end

    test "list string with nl" do
      assert_conforms(~s('fo\\no'))
    end

    test "bin string interpolated" do
      assert_conforms(~s("fo\#{bar}o"))
    end

    test "list string interpolated" do
      assert_conforms(~s('fo\#{bar}o'))
    end
  end

  describe "terminals - heredocs" do
    test "empty bin heredocs" do
      assert_conforms(~s("""\n\\\n"""))
    end

    test "empty list heredocs" do
      assert_conforms(~s('''\n\\\n'''))
    end

    test "bin heredocs" do
      assert_conforms(~s("""\nfoo\n"""))
    end

    test "list heredocs" do
      assert_conforms(~s('''\nfoo\n'''))
    end

    test "bin heredocs with indent" do
      assert_conforms(~s("""\n  foo\n  """))
    end

    test "list heredocs with indent" do
      assert_conforms(~s('''\n  foo\n  '''))
    end

    test "bin heredocs with nl" do
      assert_conforms(~s("""\nfo\\no\n"""))
    end

    test "list heredocs with nl" do
      assert_conforms(~s('''\nfo\\no\n'''))
    end

    test "bin heredocs interpolated" do
      assert_conforms(~s("""\nfo\#{bar}o\n"""))
    end

    test "list heredocs interpolated" do
      assert_conforms(~s('''\nfo\#{bar}o\n'''))
    end
  end

  describe "terminals - sigils" do
    test "empty bin sigils" do
      assert_conforms(~s(~x""))
    end

    test "bin sigils" do
      assert_conforms(~s(~x"foo"))
    end

    test "bin sigils with modifiers" do
      assert_conforms(~s(~x"foo"abc))
    end

    test "bin sigils interpolated" do
      assert_conforms(~s(~x"fo\#{bar}o"))
    end

    test "bin heredoc sigils" do
      assert_conforms(~s(~x"""\nfoo\n"""))
    end

    test "bin heredoc sigils with modifiers" do
      assert_conforms(~s(~x"""\nfoo\n"""abc))
    end

    test "bin heredoc sigils with indent" do
      assert_conforms(~s(~x"""\n  foo\n  """))
    end

    test "bin heredoc sigils interpolated" do
      assert_conforms(~s(~x"""\nfo\#{bar}o\n"""))
    end
  end

  describe "terminals - identifiers (identifier)" do
    test "simple identifier" do
      assert_conforms("foo")
      assert_conforms("bar")
      assert_conforms("baz")
    end

    test "identifier with underscore" do
      assert_conforms("foo_bar")
      assert_conforms("_private")
      assert_conforms("__special__")
    end

    test "identifier with numbers" do
      assert_conforms("foo123")
      assert_conforms("v1")
      assert_conforms("a1b2c3")
    end

    test "identifier ending with ? or !" do
      assert_conforms("foo?")
      assert_conforms("bar!")
    end

    test "underscore identifier" do
      assert_conforms("_")
      assert_conforms("_foo")
    end

    test "reserved words used as identifiers" do
      assert_conforms("do_something")
      assert_conforms("end_time")
      assert_conforms("after_hook")
    end
  end

  describe "terminals - aliases (alias)" do
    test "simple alias" do
      assert_conforms("Foo")
      assert_conforms("Bar")
      assert_conforms("MyModule")
    end

    test "nested alias" do
      assert_conforms("Foo.Bar")
      assert_conforms("Foo.Bar.Baz")
      assert_conforms("My.Deeply.Nested.Module")
    end

    test "alias with numbers" do
      assert_conforms("Foo123")
      assert_conforms("V1")
      assert_conforms("MyModule2")
    end

    test "Elixir prefix" do
      assert_conforms("Elixir.Foo")
      assert_conforms("Elixir.Foo.Bar")
    end
  end

  describe "terminals - standalone operators" do
    test "concat" do
      assert_conforms("..")
    end

    test "ellipsis" do
      assert_conforms("...")
    end
  end

  # =============================================================================
  # BINARY OPERATORS - Full precedence coverage
  # =============================================================================

  describe "binary operators - match_op (=)" do
    test "simple match" do
      assert_conforms("a = b")
      assert_conforms("1 = 2")
      assert_conforms("x = 1 = 2")
    end

    test "match with newline" do
      assert_conforms("a =\nb")
    end
  end

  describe "binary operators - dual_op (+, -)" do
    test "addition" do
      assert_conforms("1 + 2")
      assert_conforms("1 + 2 + 3")
    end

    test "subtraction" do
      assert_conforms("1 - 2")
      assert_conforms("1 - 2 - 3")
    end

    test "with newline" do
      assert_conforms("1 +\n2")
      assert_conforms("1 -\n2")
    end
  end

  describe "binary operators - mult_op (*, /)" do
    test "multiplication" do
      assert_conforms("1 * 2")
      assert_conforms("1 * 2 * 3")
    end

    test "division" do
      assert_conforms("1 / 2")
      assert_conforms("1 / 2 / 3")
    end

    test "with newline" do
      assert_conforms("1 *\n2")
    end
  end

  describe "binary operators - power_op (**)" do
    test "power" do
      assert_conforms("2 ** 3")
      assert_conforms("2 ** 3 ** 4")
    end

    test "with newline" do
      assert_conforms("2 **\n3")
    end
  end

  describe "binary operators - concat_op (<>, ++, --)" do
    test "string concat" do
      assert_conforms("a <> b")
    end

    test "list concat" do
      assert_conforms("a ++ b")
      assert_conforms("a ++ b ++ c")
    end

    test "list subtract" do
      assert_conforms("a -- b")
      assert_conforms("a -- b -- c")
    end

    test "custom concat ops" do
      assert_conforms("a +++ b")
      assert_conforms("a --- b")
    end

    test "with newline" do
      assert_conforms("a <>\nb")
    end
  end

  describe "binary operators - range_op (..)" do
    test "simple range" do
      assert_conforms("1 .. 10")
    end

    test "chained range" do
      assert_conforms("a .. b .. c")
    end

    test "with newline" do
      assert_conforms("1 ..\n10")
    end
  end

  describe "binary operators - ternary_op (//)" do
    test "default operator" do
      assert_conforms("1..a // b")
      assert_conforms("1..nil // :default")
    end

    test "with newline" do
      assert_conforms("1..a //\nb")
    end
  end

  describe "binary operators - xor_op (^^^)" do
    test "xor" do
      assert_conforms("1 ^^^ 2")
      assert_conforms("a ^^^ b ^^^ c")
    end

    test "with newline" do
      assert_conforms("1 ^^^\n2")
    end
  end

  describe "binary operators - and_op (&&, &&&, and)" do
    test "short-circuit and" do
      assert_conforms("true && false")
      assert_conforms("a && b && c")
    end

    test "bitwise and" do
      assert_conforms("a &&& b &&& c")
    end

    test "keyword and" do
      assert_conforms("true and false")
    end

    test "with newline" do
      assert_conforms("a &&\nb")
    end
  end

  describe "binary operators - or_op (||, |||, or)" do
    test "short-circuit or" do
      assert_conforms("true || false")
      assert_conforms("a || b || c")
    end

    test "bitwise or" do
      assert_conforms("a ||| b ||| c")
    end

    test "keyword or" do
      assert_conforms("true or false")
    end

    test "with newline" do
      assert_conforms("a ||\nb")
    end
  end

  describe "binary operators - in_op (in, not in)" do
    test "in operator" do
      assert_conforms("a in b")
      assert_conforms("a in b in c")
    end

    test "not in operator" do
      assert_conforms("a not in b")
      assert_conforms("a not in b not in c")
    end

    test "with newline" do
      assert_conforms("a in\n b")
      assert_conforms("a not in\n b")
    end

    test "not in rewrite" do
      assert_conforms("not a in b")
      assert_conforms("!a in b")
    end
  end

  describe "binary operators - in_match_op (<-, \\\\)" do
    test "left arrow" do
      assert_conforms("a <- b")
      assert_conforms("-a <- -b")
      assert_conforms("a <- b <- c")
    end

    test "default backslash" do
      assert_conforms("a \\\\ b")
    end

    test "with newline" do
      assert_conforms("a <-\nb")
    end
  end

  describe "binary operators - type_op (::)" do
    test "type annotation" do
      assert_conforms("a :: integer")
      assert_conforms("foo :: atom")
      assert_conforms("foo :: atom :: bar")
    end

    test "with newline" do
      assert_conforms("a ::\ninteger")
    end
  end

  describe "binary operators - when_op (when)" do
    test "guard" do
      assert_conforms("a when is_atom(a)")
      assert_conforms("x when y")
      assert_conforms("x when y when z")
    end

    test "with newline" do
      assert_conforms("a when\nb")
    end
  end

  describe "binary operators - pipe_op (|)" do
    test "pipe" do
      assert_conforms("a | b")
      assert_conforms("a | b | c")
    end

    test "with newline" do
      assert_conforms("a |\nb")
    end
  end

  describe "binary operators - comp_op (==, !=, =~, ===, !==)" do
    test "equality" do
      assert_conforms("1 == 2")
      assert_conforms("1 != 2")
      assert_conforms("1 === 2")
      assert_conforms("1 !== 2")
    end

    test "match" do
      assert_conforms("a =~ b")
    end

    test "chained" do
      assert_conforms("1 === 2 === 3")
    end

    test "with newline" do
      assert_conforms("1 ==\n2")
    end
  end

  describe "binary operators - rel_op (<, >, <=, >=)" do
    test "comparison" do
      assert_conforms("1 < 2")
      assert_conforms("1 > 2")
      assert_conforms("1 <= 2")
      assert_conforms("1 >= 2")
    end

    test "chained" do
      assert_conforms("1 <= 2 <= 3")
    end

    test "with newline" do
      assert_conforms("1 <\n2")
    end
  end

  describe "binary operators - arrow_op (|>, ~>, <~, etc.)" do
    test "pipe operator" do
      assert_conforms("a |> b")
      assert_conforms("a |> b |> c")
    end

    test "sigil arrows" do
      assert_conforms("a ~> b")
      assert_conforms("a <~ b")
      assert_conforms("a <~> b")
      assert_conforms("a <<~ b")
      assert_conforms("a ~>> b")
    end

    test "bitshift arrows" do
      assert_conforms("a <<< b")
      assert_conforms("a >>> b")
    end

    test "pipeline join" do
      assert_conforms("a <|> b")
    end

    test "with newline" do
      assert_conforms("a |>\nb")
    end
  end

  # =============================================================================
  # UNARY OPERATORS
  # =============================================================================

  describe "unary operators - ! (not)" do
    test "boolean not" do
      assert_conforms("!true")
      assert_conforms("!!true")
      assert_conforms("!foo")
    end

    test "precedence" do
      assert_conforms("!a && b")
      assert_conforms("!a == b")
    end
  end

  describe "unary operators - not" do
    test "keyword not" do
      assert_conforms("not true")
      assert_conforms("not foo")
    end

    test "precedence" do
      assert_conforms("not a and b")
      assert_conforms("not a or b")
    end
  end

  describe "unary operators - ^ (pin)" do
    test "pin operator" do
      assert_conforms("^foo")
    end

    test "pin in pattern match" do
      assert_conforms("^foo = bar")
    end

    test "pin with access" do
      assert_conforms("^foo[0]")
    end

    test "pin with parens" do
      assert_conforms("^foo(0)")
    end
  end

  describe "unary operators - @ (attribute)" do
    test "module attribute" do
      assert_conforms("@foo")
    end

    test "module attribute with value" do
      assert_conforms("@foo 1")
    end

    test "nested module attributes" do
      assert_conforms("@foo @bar")
    end

    test "precedence" do
      assert_conforms("@foo + 1")
    end

    test "with dot access" do
      assert_conforms("@foo.bar")
    end
  end

  describe "unary operators - & (capture)" do
    test "capture" do
      assert_conforms("&foo")
      assert_conforms("&Mod.fun/1")
    end

    test "capture int" do
      assert_conforms("&1")
      assert_conforms("&2")
      assert_conforms("&42")
    end
  end

  describe "unary operators - +/- as unary" do
    test "unary plus" do
      assert_conforms("+1")
      assert_conforms("+foo")
    end

    test "unary minus" do
      assert_conforms("-1")
      assert_conforms("-foo")
    end

    test "double unary" do
      assert_conforms("- -1")
    end

    test "with binary ops" do
      assert_conforms("1 - -2")
      assert_conforms("1 + +2")
    end
  end

  describe "unary operators - ~~~" do
    test "bitwise not" do
      assert_conforms("~~~1")
      assert_conforms("~~~foo")
    end
  end

  describe "unary operators - ..." do
    test "ellipsis" do
      assert_conforms("...foo")
    end
  end

  # =============================================================================
  # COLLECTIONS
  # =============================================================================

  describe "collections - lists" do
    test "empty list" do
      assert_conforms("[]")
    end

    test "simple list" do
      assert_conforms("[1]")
      assert_conforms("[1, 2]")
      assert_conforms("[1, 2, 3]")
    end

    test "list with trailing comma" do
      assert_conforms("[1,]")
      assert_conforms("[1, 2,]")
    end

    test "nested list" do
      assert_conforms("[[1, 2], [3, 4]]")
    end

    test "list with expressions" do
      assert_conforms("[1 + 2, 3 * 4]")
    end

    test "cons operator" do
      assert_conforms("[head | tail]")
      assert_conforms("[1 | rest]")
      assert_conforms("[1, 2 | rest]")
    end

    test "keyword list" do
      assert_conforms("[a: 1]")
      assert_conforms("[a: 1, b: 2]")
    end

    test "mixed keyword list" do
      assert_conforms("[1, a: 2]")
      assert_conforms("[1, 2, a: 3, b: 4]")
    end
  end

  describe "collections - tuples" do
    test "empty tuple" do
      assert_conforms("{}")
    end

    test "simple tuple" do
      assert_conforms("{1}")
      assert_conforms("{1, 2}")
      assert_conforms("{1, 2, 3}")
    end

    test "tuple with trailing comma" do
      assert_conforms("{1,}")
      assert_conforms("{1, 2,}")
    end

    test "nested tuple" do
      assert_conforms("{{1, 2}, {3, 4}}")
    end

    test "common patterns" do
      assert_conforms("{:ok, value}")
      assert_conforms("{:error, reason}")
    end
  end

  describe "collections - maps" do
    test "empty map" do
      assert_conforms("%{}")
    end

    test "simple map" do
      assert_conforms("%{a: 1}")
      assert_conforms("%{a: 1, b: 2}")
    end

    test "map with arrow keys" do
      assert_conforms("%{:a => 1}")
      assert_conforms("%{\"key\" => value}")
    end

    test "map with mixed keys" do
      assert_conforms("%{:a => 1, b: 2}")
      assert_conforms("%{1 => :one, 2 => :two}")
    end

    test "map update" do
      assert_conforms("%{map | a: 1}")
      assert_conforms("%{map | a: 1, b: 2}")
    end

    test "nested map" do
      assert_conforms("%{a: %{b: 1}}")
    end
  end

  describe "collections - structs" do
    test "empty struct" do
      assert_conforms("%Foo{}")
    end

    test "struct with fields" do
      assert_conforms("%Foo{bar: 1}")
      assert_conforms("%Foo{bar: 1, baz: 2}")
    end

    test "nested alias struct" do
      assert_conforms("%Foo.Bar{}")
      assert_conforms("%Foo.Bar.Baz{a: 1}")
    end

    test "struct update" do
      assert_conforms("%Foo{s | a: 1}")
    end

    test "__MODULE__ struct" do
      assert_conforms("%__MODULE__{}")
      assert_conforms("%__MODULE__{a: 1}")
    end
  end

  describe "collections - binaries" do
    test "empty binary" do
      assert_conforms("<<>>")
    end

    test "simple binary" do
      assert_conforms("<<1>>")
      assert_conforms("<<1, 2>>")
      assert_conforms("<<1, 2, 3>>")
    end

    test "binary with size" do
      assert_conforms("<<x::8>>")
      assert_conforms("<<x::size(8)>>")
    end

    test "binary with type" do
      assert_conforms("<<x::binary>>")
      assert_conforms("<<x::integer>>")
      assert_conforms("<<x::float>>")
    end

    test "binary with multiple modifiers" do
      assert_conforms("<<x::size(8)-integer-unsigned>>")
      assert_conforms("<<x::binary-size(10)>>")
    end

    test "string in binary" do
      assert_conforms("<<\"hello\">>")
      assert_conforms("<<\"hello\", 0>>")
    end
  end

  # =============================================================================
  # FUNCTION CALLS
  # =============================================================================

  describe "function calls - with parens" do
    test "zero arity" do
      assert_conforms("foo()")
    end

    test "single arg" do
      assert_conforms("foo(1)")
      assert_conforms("foo(x)")
    end

    test "multiple args" do
      assert_conforms("foo(1, 2)")
      assert_conforms("foo(1, 2, 3)")
    end

    test "trailing comma" do
      assert_conforms("foo(1,)")
      assert_conforms("foo(1, 2,)")
    end

    test "keyword args" do
      assert_conforms("foo(a: 1)")
      assert_conforms("foo(1, a: 2)")
      assert_conforms("foo(1, 2, a: 3, b: 4)")
    end

    test "nested calls" do
      assert_conforms("foo(bar())")
      assert_conforms("foo(bar(baz()))")
    end
  end

  describe "function calls - without parens" do
    test "single arg" do
      assert_conforms("foo 1")
      assert_conforms("bar :atom")
    end

    test "multiple args" do
      assert_conforms("foo 1, 2")
      assert_conforms("bar :a, :b, :c")
    end

    test "keyword args" do
      assert_conforms("foo x: 1")
      assert_conforms("bar a: 1, b: 2")
    end

    test "mixed args" do
      assert_conforms("foo 1, x: 2")
      assert_conforms("bar 1, 2, a: 3, b: 4")
    end
  end

  describe "function calls - remote calls" do
    test "module call" do
      assert_conforms("Foo.bar()")
      assert_conforms("Foo.bar(1)")
    end

    test "chained module" do
      assert_conforms("Foo.Bar.baz()")
    end

    test "variable module" do
      assert_conforms("foo.bar()")
      assert_conforms("foo.bar.baz()")
    end

    test "no parens remote" do
      assert_conforms("Foo.bar 1")
      assert_conforms("foo.bar 1, 2")
    end
  end

  describe "function calls - anonymous calls" do
    test "variable call" do
      assert_conforms("foo.()")
      assert_conforms("foo.(1)")
      assert_conforms("foo.(1, 2)")
    end

    test "chained anonymous" do
      assert_conforms("foo.().()")
    end
  end

  describe "function calls - access syntax" do
    test "bracket access" do
      assert_conforms("foo[:bar]")
      assert_conforms("foo[0]")
      assert_conforms("foo[a]")
    end

    test "chained access" do
      assert_conforms("foo[:a][:b]")
      assert_conforms("foo.bar[0]")
    end

    test "attribute access" do
      assert_conforms("@foo[1]")
      assert_conforms("@foo.bar[:key]")
    end
  end

  # =============================================================================
  # CONTROL FLOW
  # =============================================================================

  describe "control flow - if/unless" do
    test "simple if" do
      assert_conforms("if true do\n:ok\nend")
    end

    test "if with else" do
      assert_conforms("if true do\n:ok\nelse\n:error\nend")
    end

    test "unless" do
      assert_conforms("unless false do\n:ok\nend")
    end

    test "keyword form" do
      assert_conforms("if true, do: :ok")
      assert_conforms("if true, do: :ok, else: :error")
    end
  end

  describe "control flow - case" do
    test "simple case" do
      assert_conforms("case x do\n1 -> :one\n_ -> :other\nend")
    end

    test "multiple clauses" do
      assert_conforms("case x do\n1 -> :one\n2 -> :two\n_ -> :other\nend")
    end

    test "with guards" do
      assert_conforms("case x do\nn when n > 0 -> :positive\n_ -> :other\nend")
    end

    test "pattern matching" do
      assert_conforms("case x do\n{:ok, v} -> v\n{:error, _} -> nil\nend")
    end
  end

  describe "control flow - cond" do
    test "simple cond" do
      assert_conforms("cond do\ntrue -> :ok\nend")
    end

    test "multiple conditions" do
      assert_conforms("cond do\nx > 0 -> :positive\nx < 0 -> :negative\ntrue -> :zero\nend")
    end
  end

  describe "control flow - with" do
    test "simple with" do
      assert_conforms("with {:ok, x} <- foo() do\nx\nend")
    end

    test "multiple clauses" do
      assert_conforms("with {:ok, x} <- foo(),\n{:ok, y} <- bar(x) do\n{x, y}\nend")
    end

    test "with else" do
      assert_conforms("with {:ok, x} <- foo() do\nx\nelse\n_ -> :error\nend")
    end
  end

  describe "control flow - try/rescue/catch/after" do
    test "try with rescue" do
      assert_conforms("try do\nfoo()\nrescue\ne -> e\nend")
    end

    test "try with catch" do
      assert_conforms("try do\nfoo()\ncatch\n:exit, _ -> :caught\nend")
    end

    test "try with after" do
      assert_conforms("try do\nfoo()\nafter\ncleanup()\nend")
    end

    test "full try" do
      assert_conforms(
        "try do\nfoo()\nrescue\ne -> e\ncatch\n_, _ -> :caught\nafter\ncleanup()\nend"
      )
    end
  end

  describe "control flow - receive" do
    test "simple receive" do
      assert_conforms("receive do\n{:msg, x} -> x\nend")
    end

    test "receive with after" do
      assert_conforms("receive do\n{:msg, x} -> x\nafter\n1000 -> :timeout\nend")
    end
  end

  describe "control flow - for comprehension" do
    test "simple for" do
      assert_conforms("for x <- [1, 2, 3], do: x * 2")
    end

    test "for with filter" do
      assert_conforms("for x <- [1, 2, 3], x > 1, do: x")
    end

    test "multiple generators" do
      assert_conforms("for x <- [1, 2], y <- [3, 4], do: {x, y}")
    end

    test "for with into" do
      assert_conforms("for x <- [1, 2, 3], into: %{}, do: {x, x}")
    end

    test "block form" do
      assert_conforms("for x <- list do\nx * 2\nend")
    end
  end

  # =============================================================================
  # ANONYMOUS FUNCTIONS
  # =============================================================================

  describe "anonymous functions - fn" do
    test "zero arity" do
      assert_conforms("fn -> :ok end")
    end

    test "single arg" do
      assert_conforms("fn x -> x end")
    end

    test "multiple args" do
      assert_conforms("fn x, y -> x + y end")
    end

    test "pattern matching" do
      assert_conforms("fn {:ok, x} -> x end")
    end

    test "multiple clauses" do
      assert_conforms("fn 1 -> :one; 2 -> :two; _ -> :other end")
    end

    test "with guards" do
      assert_conforms("fn x when is_integer(x) -> x end")
    end

    test "empty paren" do
      assert_conforms("fn () -> :ok end")
    end
  end

  describe "anonymous functions - capture" do
    test "named function" do
      assert_conforms("&foo/1")
      assert_conforms("&Mod.fun/2")
    end

    test "capture with placeholder" do
      assert_conforms("&(&1 + 1)")
      assert_conforms("&(&1 + &2)")
    end

    test "capture expression" do
      assert_conforms("&foo(&1)")
      assert_conforms("&Mod.fun(&1, &2)")
    end
  end

  # =============================================================================
  # MODULE DEFINITIONS
  # =============================================================================

  describe "module definitions - defmodule" do
    test "empty module" do
      assert_conforms("defmodule Foo do\nend")
    end

    test "module with function" do
      assert_conforms("defmodule Foo do\ndef bar, do: :ok\nend")
    end

    test "nested module" do
      assert_conforms("defmodule Foo.Bar do\nend")
    end
  end

  describe "module definitions - def/defp" do
    test "zero arity" do
      assert_conforms("def foo, do: :ok")
      assert_conforms("def foo do\n:ok\nend")
    end

    test "with args" do
      assert_conforms("def foo(x), do: x")
      assert_conforms("def foo(x, y), do: x + y")
    end

    test "with guards" do
      assert_conforms("def foo(x) when is_integer(x), do: x")
    end

    test "pattern matching" do
      assert_conforms("def foo({:ok, x}), do: x")
      assert_conforms("def foo(%{key: value}), do: value")
    end

    test "private function" do
      assert_conforms("defp foo, do: :ok")
      assert_conforms("defp foo(x), do: x")
    end

    test "default arguments" do
      assert_conforms("def foo(x \\\\ 1), do: x")
      assert_conforms("def foo(x, y \\\\ 2), do: x + y")
    end
  end

  describe "module definitions - defmacro" do
    test "simple macro" do
      assert_conforms("defmacro foo, do: :ok")
      assert_conforms("defmacro foo(x), do: quote do: unquote(x)")
    end
  end

  describe "module definitions - attributes" do
    test "simple attribute" do
      assert_conforms("@moduledoc false")
    end

    test "attribute with value" do
      assert_conforms("@my_attr :value")
      assert_conforms("@my_attr 123")
    end

    test "doc attribute" do
      assert_conforms("@doc \"my doc\"")
    end
  end

  # =============================================================================
  # SPECIAL FORMS
  # =============================================================================

  describe "special forms - quote/unquote" do
    test "simple quote" do
      assert_conforms("quote do: :ok")
      assert_conforms("quote do\n:ok\nend")
    end

    test "quote with options" do
      assert_conforms("quote bind_quoted: [x: x] do\nx\nend")
    end

    test "unquote" do
      assert_conforms("quote do\nunquote(x)\nend")
    end

    test "unquote splicing" do
      assert_conforms("quote do\nunquote_splicing(list)\nend")
    end
  end

  describe "special forms - alias/import/require/use" do
    test "alias" do
      assert_conforms("alias Foo.Bar")
      assert_conforms("alias Foo.Bar, as: B")
    end

    test "import" do
      assert_conforms("import Foo")
      assert_conforms("import Foo, only: [bar: 1]")
    end

    test "require" do
      assert_conforms("require Logger")
    end

    test "use" do
      assert_conforms("use GenServer")
      assert_conforms("use GenServer, restart: :temporary")
    end
  end

  # =============================================================================
  # EXPRESSION LISTS / BLOCKS
  # =============================================================================

  describe "expression lists" do
    test "single expression" do
      assert_conforms("1")
      assert_conforms("foo")
      assert_conforms(":atom")
    end

    test "multiple expressions separated by semicolon" do
      assert_conforms("1;2")
      assert_conforms("1;2;3")
    end

    test "multiple expressions separated by newline" do
      assert_conforms("1\n2")
      assert_conforms("1\n2\n3")
    end

    test "multiple expressions with mixed separators" do
      assert_conforms("1\n;2")
      assert_conforms("1\n;2\n;3")
    end

    test "leading eoe" do
      assert_conforms(";1")
      assert_conforms(";1;2")
      assert_conforms("\n1")
    end

    test "trailing eoe" do
      assert_conforms("1;")
      assert_conforms("1;2;")
      assert_conforms("1\n")
    end
  end

  describe "parenthesized expressions" do
    test "simple paren" do
      assert_conforms("(1)")
      assert_conforms("(foo)")
    end

    test "paren with ops" do
      assert_conforms("(1 + 2)")
      assert_conforms("(1 + 2) * 3")
    end

    test "nested parens" do
      assert_conforms("((1))")
      assert_conforms("((1 + 2))")
    end

    test "stab in parens" do
      assert_conforms("(1 -> 2)")
      assert_conforms("(-> :ok)")
      assert_conforms("(() -> :ok)")
    end
  end

  # =============================================================================
  # DOT ACCESS
  # =============================================================================

  describe "dot access" do
    test "simple dot" do
      assert_conforms("foo.bar")
    end

    test "chained dot" do
      assert_conforms("foo.bar.baz")
      assert_conforms("a.b.c.d.e")
    end

    test "dot on literals" do
      assert_conforms("2.b")
      assert_conforms("1.2.b")
      assert_conforms(":asd.b")
    end

    test "dot with call" do
      assert_conforms("foo.bar()")
      assert_conforms("foo.bar().baz()")
    end

    test "dot with newline" do
      assert_conforms("foo.\nbar")
    end
  end

  # =============================================================================
  # MISCELLANEOUS
  # =============================================================================

  describe "miscellaneous - keyword arguments as implicit list" do
    test "in function call" do
      assert_conforms("foo(a: 1, b: 2)")
    end

    test "in no parens call" do
      assert_conforms("foo a: 1, b: 2")
    end

    test "quoted keys" do
      assert_conforms("foo('a': 1)")
      assert_conforms("foo(\"a\": 1)")
    end
  end

  describe "miscellaneous - do blocks" do
    test "simple do block" do
      assert_conforms("foo do\n:ok\nend")
    end

    test "do with keyword form" do
      assert_conforms("foo do: :ok")
    end

    test "do with rescue/else" do
      assert_conforms("foo do\n:ok\nrescue\ne -> e\nend")
    end
  end

  describe "interpolation in grammar" do
    test "nested grammar in interpolation" do
      assert_conforms("'asd\#{}ppp'")
      assert_conforms("'asd\#{;}ppp'")
      assert_conforms("'asd\#{\n}ppp'")
      assert_conforms("'asd\#{\n;}ppp'")
      assert_conforms("'asd\#{a;}ppp'")
      assert_conforms("'asd\#{;a}ppp'")
      assert_conforms("'asd\#{a;b}ppp'")
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

      # When Hurricane has errors, convert to Elixir's error format for comparison
      {:ok, _ast, [{%{line: line, column: col}, {message, token}} | _]} ->
        {:error, {[line: line, column: col], message, token}}

      {:ok, _ast, [{%{line: line, column: col}, message} | _]} ->
        {:error, {[line: line, column: col], message, ""}}

      {:error, reason} ->
        {:error, reason}
    end
  end
end
