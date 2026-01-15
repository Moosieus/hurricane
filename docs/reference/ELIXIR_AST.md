# Elixir AST Format Reference

Hurricane must produce AST matching `Code.string_to_quoted/2` with these options:
```elixir
Code.string_to_quoted(code, columns: true, token_metadata: true)
```

## AST Node Structure

All AST nodes are one of:
1. **Atoms**: `:foo`, `true`, `false`, `nil`
2. **Numbers**: `42`, `3.14`
3. **Strings**: `"hello"` (binaries)
4. **Lists**: `[1, 2, 3]` (literal lists)
5. **Tuples (2-element)**: `{:ok, value}` (literal tuples)
6. **Calls**: `{form, metadata, arguments}`

## The Call Tuple

Most AST nodes are 3-tuples:
```elixir
{form, metadata, arguments}
```

- **form**: atom (operator/name) or nested AST (for dot calls)
- **metadata**: keyword list with at least `line:` and `column:`
- **arguments**: list of AST nodes, or `nil` for variables

## Metadata Fields

### Always Present
```elixir
[line: 1, column: 5]
```

### Optional (Context-Dependent)

```elixir
# Closing delimiter location
[closing: [line: 1, column: 10]]

# Do/end block locations
[do: [line: 1, column: 8], end: [line: 3, column: 1]]

# For identifiers - the context
[context: Elixir]

# For strings - the delimiter used
[delimiter: "\""]

# For heredocs
[delimiter: "\"\"\"", indentation: 2]

# For interpolated strings
[delimiter: "\"", indentation: 0]
```

## Common AST Patterns

### Literals

```elixir
# Integer
42
# AST: 42

# Float
3.14
# AST: 3.14

# Atom
:foo
# AST: :foo

# String
"hello"
# AST: "hello"

# Charlist
'hello'
# AST: {{:., [], [:erlang, :binary_to_list]}, [], ["hello"]}
# Or with literal_encoder: 'hello'
```

### Variables

```elixir
foo
# AST: {:foo, [line: 1, column: 1], nil}
# Note: third element is nil (not []) for variables
```

### Function Calls

```elixir
# No args
foo()
# AST: {:foo, [closing: [...], line: 1, column: 1], []}

# With args
foo(1, 2)
# AST: {:foo, [closing: [...], line: 1, column: 1], [1, 2]}

# No parens
foo 1, 2
# AST: {:foo, [line: 1, column: 1], [1, 2]}
```

### Remote Calls (Module.function)

```elixir
Foo.bar(x)
# AST:
{{:., [line: 1, column: 4], [{:__aliases__, [line: 1, column: 1], [:Foo]}, :bar]},
 [closing: [...], line: 1, column: 4],
 [{:x, [line: 1, column: 9], nil}]}
```

### Operators

```elixir
# Binary
1 + 2
# AST: {:+, [line: 1, column: 3], [1, 2]}

# Unary
-x
# AST: {:-, [line: 1, column: 1], [{:x, [line: 1, column: 2], nil}]}

# Pipe
x |> foo()
# AST: {:|>, [line: 1, column: 3], [
#   {:x, [line: 1, column: 1], nil},
#   {:foo, [closing: [...], line: 1, column: 6], []}
# ]}
```

### Blocks

```elixir
# Multiple expressions become __block__
(
  a
  b
)
# AST: {:__block__, [], [{:a, [...], nil}, {:b, [...], nil}]}

# Single expression - no block wrapper
(a)
# AST: {:a, [...], nil}
```

### Module Definition

```elixir
defmodule Foo do
  def bar, do: :ok
end

# AST:
{:defmodule, [do: [...], end: [...], line: 1, column: 1],
 [{:__aliases__, [line: 1, column: 11], [:Foo]},
  [do: {:def, [line: 2, column: 3],
    [{:bar, [line: 2, column: 7], nil},
     [do: :ok]]}]]}
```

### Function Definition

```elixir
def foo(x, y) do
  x + y
end

# AST:
{:def, [do: [...], end: [...], line: 1, column: 1],
 [{:foo, [closing: [...], line: 1, column: 5],
   [{:x, [...], nil}, {:y, [...], nil}]},
  [do: {:+, [...], [{:x, [...], nil}, {:y, [...], nil}]}]]}
```

### Pattern Matching

```elixir
{a, b} = tuple

# AST:
{:=, [line: 1, column: 8],
 [{:{}, [line: 1, column: 1], [{:a, [...], nil}, {:b, [...], nil}]},
  {:tuple, [...], nil}]}
```

### Lists

```elixir
[1, 2, 3]
# AST: [1, 2, 3]  (literal list, no tuple wrapper)

# With cons
[h | t]
# AST: [{:|, [...], [{:h, [...], nil}, {:t, [...], nil}]}]
```

### Tuples

```elixir
# 2-element tuples are literal
{:ok, value}
# AST: {:ok, {:value, [...], nil}}

# 3+ element tuples use :{}
{1, 2, 3}
# AST: {:{}, [line: 1, column: 1], [1, 2, 3]}
```

### Maps

```elixir
%{a: 1, b: 2}
# AST: {:%{}, [...], [a: 1, b: 2]}

%{x => y}
# AST: {:%{}, [...], [{:x, [...], nil}, {:y, [...], nil}]}
```

### Structs

```elixir
%Foo{a: 1}
# AST: {:%, [...], [{:__aliases__, [...], [:Foo]}, {:%{}, [...], [a: 1]}]}
```

### Anonymous Functions

```elixir
fn x -> x + 1 end
# AST: {:fn, [...], [{:->, [...], [[{:x, [...], nil}], {:+, [...], [...]}]}]}

# Multiple clauses
fn
  :a -> 1
  :b -> 2
end
# AST: {:fn, [...], [
#   {:->, [...], [[:a], 1]},
#   {:->, [...], [[:b], 2]}
# ]}
```

### Case

```elixir
case x do
  :a -> 1
  :b -> 2
end

# AST:
{:case, [do: [...], end: [...], line: 1, column: 1],
 [{:x, [...], nil},
  [do: [
    {:->, [...], [[:a], 1]},
    {:->, [...], [[:b], 2]}
  ]]]}
```

### With

```elixir
with {:ok, a} <- foo(),
     {:ok, b} <- bar(a) do
  a + b
end

# AST:
{:with, [do: [...], end: [...], line: 1, column: 1],
 [{:<-, [...], [{:ok, {:a, [...], nil}}, {:foo, [...], []}]},
  {:<-, [...], [{:ok, {:b, [...], nil}}, {:bar, [...], [{:a, [...], nil}]}]},
  [do: {:+, [...], [{:a, [...], nil}, {:b, [...], nil}]}]]}
```

### Comprehensions

```elixir
for x <- list, x > 0, do: x * 2

# AST:
{:for, [...],
 [{:<-, [...], [{:x, [...], nil}, {:list, [...], nil}]},
  {:>, [...], [{:x, [...], nil}, 0]},
  [do: {:*, [...], [{:x, [...], nil}, 2]}]]}
```

### Module Attributes

```elixir
@doc "Hello"
# AST: {:@, [...], [{:doc, [...], ["Hello"]}]}

@foo
# AST: {:@, [...], [{:foo, [...], nil}]}
```

### Sigils

```elixir
~r/foo/i
# AST: {:sigil_r, [delimiter: "/", line: 1, column: 1], [{:<<>>, [...], ["foo"]}, 'i']}

~w(a b c)
# AST: {:sigil_w, [delimiter: "(", ...], [{:<<>>, [...], ["a b c"]}, []]}
```

## Error Node Format

For Hurricane, errors are represented as:
```elixir
{:__block__, [error: true, line: n, column: m], []}
```

This is a valid AST node that tooling can pattern match and skip.

## Verification Strategy

For any valid Elixir code:
```elixir
{:ok, hurricane_ast} = Hurricane.parse(code)
{:ok, reference_ast} = Code.string_to_quoted(code, columns: true, token_metadata: true)
assert hurricane_ast == reference_ast
```

Metadata order may vary — normalize before comparison if needed.
