# Hurricane Architecture

## Overview

Hurricane is a hand-written recursive descent parser with Pratt parsing for expressions.
It produces standard Elixir AST and is designed for resilience over strictness.

```
┌─────────────────────────────────────────────────────────────┐
│                         Source Code                          │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                           Lexer                              │
│  ─────────────────────────────────────────────────────────  │
│  • Hand-written or wraps :elixir_tokenizer                  │
│  • Produces tokens with {line, column} spans                │
│  • Handles string interpolation, sigils, heredocs           │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                      Parser State                            │
│  ─────────────────────────────────────────────────────────  │
│  • Token stream (remaining tokens)                          │
│  • Position (for advance assertions)                        │
│  • Checkpoint stack (for advance tracking)                  │
│  • Error accumulator                                        │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│               Recursive Descent (Structure)                  │
│  ─────────────────────────────────────────────────────────  │
│  • defmodule, def, defp, defmacro, defstruct, defprotocol   │
│  • do/end, fn/end blocks                                    │
│  • case, cond, with, try, receive                           │
│  • if, unless, for, quote, unquote                          │
│  • @attributes, use, import, alias, require                 │
│  • Recovery sets at every loop                              │
└─────────────────────────────────────────────────────────────┘
                              │
                    (delegates to)
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                  Pratt Parser (Expressions)                  │
│  ─────────────────────────────────────────────────────────  │
│  • Binary operators with precedence/associativity           │
│  • Unary operators (prefix: !, not, ^, &, -, +)            │
│  • Postfix: function calls, bracket access, dot access      │
│  • Handles 27 precedence levels via binding power           │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                       Elixir AST                             │
│  ─────────────────────────────────────────────────────────  │
│  • Standard {form, metadata, args} tuples                   │
│  • Error nodes: {:__block__, [error: true | meta], []}     │
│  • Matches Code.string_to_quoted for valid input            │
└─────────────────────────────────────────────────────────────┘
```

## Module Structure

```
lib/hurricane/
├── hurricane.ex              # Public API
├── lexer.ex                  # Tokenization
├── token.ex                  # Token struct
├── parser.ex                 # Main parser entry
├── parser/
│   ├── state.ex              # Parser state management
│   ├── recovery.ex           # Recovery set definitions
│   ├── structure.ex          # Recursive descent (top-level)
│   ├── expression.ex         # Pratt expression parser
│   ├── collection.ex         # List, tuple, map, binary
│   └── special.ex            # case, cond, with, try, etc.
└── ast.ex                    # AST construction helpers
```

## Parser State

```elixir
defmodule Hurricane.Parser.State do
  defstruct [
    :tokens,        # List of remaining tokens
    :pos,           # Current position (token index)
    :checkpoints,   # Stack of positions for advance assertions
    :errors         # Accumulated errors [{meta, message}]
  ]
end
```

### Core Operations

```elixir
# Peek at current token without consuming
def current(state)

# Check if current token matches
def at?(state, kind)
def at_any?(state, kinds)

# Consume current token, advance to next
def advance(state)

# Consume if matches, otherwise no-op
def eat(state, kind) -> {:ok, state} | {:error, state}

# Consume if matches, otherwise emit error
def expect(state, kind)

# Emit error, consume token to make progress
def advance_with_error(state, message)
```

### Advance Assertions

```elixir
# Mark position before loop iteration
def advance_push(state) do
  %{state | checkpoints: [state.pos | state.checkpoints]}
end

# Assert progress was made (crashes if not)
def advance_pop!(state) do
  [start | rest] = state.checkpoints
  if state.pos == start do
    raise "Parser stuck at position #{start}, token: #{inspect(current(state))}"
  end
  %{state | checkpoints: rest}
end
```

## Recovery Sets

Defined in `Hurricane.Parser.Recovery`:

```elixir
defmodule Hurricane.Parser.Recovery do
  # Module body: what ends a module-level item?
  @module_body [:def, :defp, :defmacro, :defmacrop, :defmodule,
                :defstruct, :defprotocol, :defimpl, :defdelegate,
                :@, :end, :eof]

  # Block body: what ends statements inside do/end?
  @block_body [:end, :rescue, :catch, :else, :after, :eof]

  # Parameters: what ends a parameter list?
  @params [:rparen, :arrow, :do, :when, :def, :defp, :defmacro, :end, :eof]

  # Stab clauses: what ends a clause in case/cond/fn?
  @stab_clause [:arrow, :end, :else, :rescue, :catch, :after, :eof]

  # Collections: what ends list/tuple/map contents?
  @collection [:rbracket, :rbrace, :rparen, :rangle, :end, :eof]

  def module_body, do: @module_body
  def block_body, do: @block_body
  def params, do: @params
  def stab_clause, do: @stab_clause
  def collection, do: @collection

  def at_recovery?(state, set) do
    current_kind(state) in set
  end
end
```

## Pratt Parsing

### Binding Power Table

Operators have two binding powers: left and right. For left-associative operators,
right BP > left BP. For right-associative, left BP > right BP.

```elixir
defmodule Hurricane.Parser.Expression do
  # {left_bp, right_bp}
  # Higher number = binds tighter

  @precedence %{
    # Right-associative (left > right conceptually, but we subtract 1)
    :\\     => {5, 4},      # default arg
    :|      => {9, 8},      # cons
    :when   => {13, 12},    # guard
    :::     => {21, 20},    # type
    :<-     => {27, 26},    # match in comprehension
    :=      => {27, 26},    # match

    # Left-associative (right > left)
    :or     => {29, 30},
    :||     => {29, 30},
    :and    => {31, 32},
    :&&     => {31, 32},
    :==     => {33, 34},
    :!=     => {33, 34},
    :=~     => {33, 34},
    :===    => {33, 34},
    :!==    => {33, 34},
    :<      => {35, 36},
    :>      => {35, 36},
    :<=     => {35, 36},
    :>=     => {35, 36},
    :|>     => {37, 38},    # pipe
    :in     => {39, 40},
    :^^^    => {41, 42},    # xor
    :++     => {43, 44},    # right-assoc actually, special case
    :--     => {43, 44},
    :<>     => {43, 44},
    :..     => {45, 46},    # range
    :+      => {47, 48},
    :-      => {47, 48},
    :*      => {49, 50},
    :/      => {49, 50},
    :**     => {51, 52},    # power
    :.      => {61, 62},    # dot (highest)
  }

  # Prefix operators (only right BP)
  @prefix %{
    :!      => 55,
    :not    => 55,
    :^      => 57,    # pin
    :&      => 59,    # capture
    :-      => 53,    # unary minus
    :+      => 53,    # unary plus
    :~~~    => 55,    # bitwise not
    :@      => 63,    # module attribute
  }
end
```

### Pratt Algorithm

```elixir
def parse_expression(state, min_bp \\ 0) do
  # 1. Parse prefix/atom
  state = parse_prefix(state)

  # 2. Loop: while next op binds tighter than min_bp
  parse_infix_loop(state, min_bp)
end

defp parse_infix_loop(state, min_bp) do
  case infix_bp(current_kind(state)) do
    {left_bp, right_bp} when left_bp >= min_bp ->
      op = current(state)
      state = advance(state)
      state = parse_expression(state, right_bp)
      # Build AST node for binary op
      parse_infix_loop(state, min_bp)

    _ ->
      # Check for postfix (call, access, dot)
      maybe_parse_postfix(state, min_bp)
  end
end
```

## AST Construction

### Standard Nodes

```elixir
# Function call
{:foo, meta, [arg1, arg2]}

# Binary operator
{:+, meta, [left, right]}

# Module definition
{:defmodule, meta, [alias, [do: body]]}

# Function definition
{:def, meta, [call, [do: body]]}

# Block
{:__block__, meta, [expr1, expr2, ...]}
```

### Error Nodes

```elixir
# Error placeholder
{:__block__, [error: true, line: n, column: m], []}
```

### Metadata

Always include:
- `line: integer`
- `column: integer`

Optionally include (when applicable):
- `closing: [line: n, column: m]` — for delimited constructs
- `do: [line: n, column: m]` — do block location
- `end: [line: n, column: m]` — end keyword location
- `delimiter: "\"" | "'"` — string delimiter used

## Parsing Patterns

### Top-Level Loop

```elixir
defp parse_module_body(state) do
  if at?(state, :end) or at?(state, :eof) do
    state
  else
    state = advance_push(state)
    state = parse_module_item(state)
    state = advance_pop!(state)
    parse_module_body(state)
  end
end

defp parse_module_item(state) do
  cond do
    at?(state, :def) -> parse_def(state)
    at?(state, :defp) -> parse_def(state)
    at?(state, :defmacro) -> parse_def(state)
    at?(state, :@) -> parse_attribute(state)
    at?(state, :defmodule) -> parse_defmodule(state)
    at_recovery?(state, Recovery.module_body()) -> state
    true ->
      # Unknown token: emit error, consume, continue
      advance_with_error(state, "unexpected token in module body")
  end
end
```

### Recovery Pattern

```elixir
defp parse_params(state) do
  state = expect(state, :lparen)
  state = parse_param_list(state)
  state = expect(state, :rparen)
  state
end

defp parse_param_list(state) do
  if at?(state, :rparen) or at_recovery?(state, Recovery.params()) do
    state
  else
    state = advance_push(state)
    state = parse_param(state)
    state = advance_pop!(state)

    case eat(state, :comma) do
      {:ok, state} -> parse_param_list(state)
      {:error, state} -> state
    end
  end
end
```

### Sync After Error

```elixir
defp sync_to(state, recovery_set) do
  if at_any?(state, recovery_set) or at?(state, :eof) do
    state
  else
    state
    |> advance()
    |> sync_to(recovery_set)
  end
end
```

## Testing Strategy

### Valid Code Tests

For every test case:
```elixir
test "parses X correctly" do
  code = "..."
  {:ok, hurricane_ast} = Hurricane.parse(code)
  {:ok, reference_ast} = Code.string_to_quoted(code, columns: true, token_metadata: true)
  assert hurricane_ast == reference_ast
end
```

### Broken Code Tests

```elixir
test "recovers from incomplete def" do
  code = """
  defmodule Foo do
    def bar(x,

    def baz(y), do: y
  end
  """

  {:ok, ast} = Hurricane.parse(code)

  # Should still find both functions
  assert has_def?(ast, :bar)
  assert has_def?(ast, :baz)

  # baz should be complete
  assert def_complete?(ast, :baz)
end
```

### Adversarial Tests

```elixir
test "never hangs on pathological input" do
  # Deeply nested unclosed brackets
  code = String.duplicate("[", 100)

  # Should return quickly with errors, not hang
  assert {:ok, _ast} = Hurricane.parse(code)
end
```
