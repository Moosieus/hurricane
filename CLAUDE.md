# Hurricane Implementation Prompt

You are implementing Hurricane, a resilient Elixir parser for IDE/LSP use.

## Context

Read these documents in `docs/` first:
1. `docs/EXECUTIVE_SUMMARY.md` — Goals and constraints
2. `docs/ARCHITECTURE.md` — Detailed design
3. `docs/reference/MATKLAD_PRATT.md` — Pratt parsing technique
4. `docs/reference/MATKLAD_RESILIENT.md` — Resilience patterns
5. `docs/reference/PRECEDENCE_TABLE.md` — Elixir operator precedence
6. `docs/reference/ELIXIR_AST.md` — Target AST format

## Original Sources (for deep dives)

- https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
- https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html
- https://matklad.github.io/2025/12/28/parsing-advances.html

## Goal

Build a parser that:
1. Outputs standard Elixir AST (matches `Code.string_to_quoted`)
2. Never crashes on malformed input
3. Recovers gracefully from errors to parse subsequent valid code
4. Is maintainable and debuggable

## Constraints

- **Pure Elixir** — No NIFs
- **AST format is fixed** — Must match Elixir's AST exactly for valid code
- **Resilience over strictness** — Always return a tree, mark errors in-band

## Key Decisions

### Lexer: Toxic (error-tolerant)

We use the Toxic lexer which provides:
- **Error recovery**: Continues tokenizing after errors, emitting error tokens inline
- **Ranged positions**: Both start AND end positions for every token
- **IDE-ready**: Enables "cursor in token" queries for completion, hover, etc.

```elixir
# Via Hurricane.Lexer.ToxicAdapter
stream = Toxic.new(source, 1, 1, error_mode: :tolerant)
tokens = stream |> Toxic.to_stream() |> Enum.to_list() |> Toxic.Legacy.collapse_linear_ranges()
```

This replaced the original `:elixir_tokenizer` approach once lexer-level error recovery
became necessary for incomplete strings/sigils mid-edit.

### AST Precision: Full Metadata

Match `Code.string_to_quoted(code, columns: true, token_metadata: true)` **exactly**,
including `closing`, `delimiter`, `do`/`end` locations. This metadata is valuable for
IDE features (bracket matching, formatting hints).

### Implementation Approach: Hybrid

1. Do Phase 1 properly (foundation, state, recovery sets, advance assertions)
2. Get minimal end-to-end working: `defmodule` → `def` → basic expressions → `do/end`
3. Test recovery against the incomplete corpus early
4. Then expand systematically

Having something testable early catches design issues before you've built the whole thing.

### Reference Code

Both are available and should be used:
- `../spitfire/` — Precedence table is correct, study the Pratt loop
- `../elixir/` — Authoritative for AST format questions

## Architecture

```
lib/hurricane/
├── hurricane.ex              # Public API: parse/1, parse!/1
├── lexer.ex                  # Tokenization (delegates to ToxicAdapter)
├── lexer/
│   └── toxic_adapter.ex      # Bridge to Toxic error-tolerant lexer
├── token.ex                  # Token struct with full range info
├── ast.ex                    # AST construction helpers
├── parser.ex                 # Main parser (monolithic: structure + Pratt + special forms)
└── parser/
    ├── state.ex              # Parser state + advance assertions
    └── recovery.ex           # Recovery set definitions
```

## Non-Negotiables

### 1. Recovery Sets

Defined in `recovery.ex`. Each set defines "sync tokens" - when lost, skip to the next token in the recovery set:
```elixir
@closing_delimiters [:rparen, :rbracket, :rbrace, :rangle]

def module_body do
  [:def, :defp, :defmacro, :defmacrop, :defmodule, :defstruct, :defprotocol,
   :defimpl, :defdelegate, :defguard, :defguardp, :defexception, :defoverridable,
   :@, :use, :import, :alias_directive, :require, :end, :eof, :->]
end

def block_body, do: [:end, :rescue, :catch, :else, :after, :-> | @closing_delimiters ++ [:eof]]
def function_body, do: [:end, :rescue, :catch, :else, :after, :->, :def, :defp, :defmacro, :defmacrop, :defmodule | @closing_delimiters ++ [:eof]]
def params, do: [:rparen, :do, :when, :def, :defp, :defmacro, :defmacrop, :end, :eof, :->]
def stab_clause, do: [:->, :end, :else, :rescue, :catch, :after, :eof]
def collection, do: @closing_delimiters ++ [:end, :eof]
def expression, do: [:comma, :do, :end, :rescue, :catch, :else, :after, :->, :def, :defp, :defmacro, :defmacrop, :defmodule | @closing_delimiters ++ [:eof]]
```

Use at every loop boundary.

### 2. Advance Assertions

In `state.ex`:
```elixir
def advance_push(state), do: %{state | checkpoints: [state.pos | state.checkpoints]}

def advance_pop!(state) do
  [start | rest] = state.checkpoints
  if state.pos == start do
    raise "Parser stuck at #{start}: #{inspect(current(state))}"
  end
  %{state | checkpoints: rest}
end
```

Use in every loop:
```elixir
while not at_end?(state) do
  state = advance_push(state)
  state = parse_item(state)
  state = advance_pop!(state)
end
```

### 3. Error Nodes

Errors are AST nodes:
```elixir
{:__block__, [error: true, line: n, column: m], []}
```

## Implementation Order

### Phase 1: Foundation
1. Token struct and tokenization (or wrap `:elixir_tokenizer`)
2. Parser state with core operations (at?, advance, eat, expect)
3. Recovery set infrastructure
4. Advance assertion infrastructure

### Phase 2: Structure (Recursive Descent)
5. Top-level: defmodule
6. Top-level: def/defp/defmacro with params and guards
7. Do/end blocks
8. Module attributes (@doc, @spec, @attr)

### Phase 3: Expressions (Pratt)
9. Pratt parser core (parse_expression, infix loop)
10. Binary operators with full precedence table
11. Unary/prefix operators
12. Postfix: function calls, bracket access, dot access

### Phase 4: Collections
13. Lists (including cons patterns)
14. Tuples
15. Maps and structs
16. Binaries/bitstrings

### Phase 5: Special Forms
17. case/cond with stab clauses
18. with expressions
19. try/rescue/catch/after
20. Anonymous functions (fn)
21. Comprehensions (for)
22. quote/unquote

### Phase 6: Polish
23. String interpolation
24. Sigils
25. Heredocs
26. Comments (if needed for metadata)
27. Full test suite against corpus

## Testing Strategy

### Valid Code
```elixir
test "matches Code.string_to_quoted" do
  code = ~S|defmodule Foo do def bar(x), do: x end end|
  assert Hurricane.parse!(code) == Code.string_to_quoted!(code, columns: true, token_metadata: true)
end
```

### Broken Code
```elixir
test "recovers from incomplete function" do
  code = """
  defmodule Foo do
    def broken(x,

    def working(y), do: y
  end
  """
  {:ok, ast} = Hurricane.parse(code)
  assert has_function?(ast, :working)
end
```

### Adversarial Code
```elixir
test "handles pathological nesting" do
  code = String.duplicate("[", 100)
  assert {:ok, _} = Hurricane.parse(code)  # Returns, doesn't hang
end
```

## Test Corpus

See `test_corpus/` for examples:
- `valid/` — Should match Code.string_to_quoted exactly
- `incomplete/` — Mid-edit states, should recover
- `malformed/` — Syntax errors, should not crash
- `adversarial/` — Worst-case inputs, should not hang

## Existing References

- `../spitfire/` — Reference for precedence table (correct), patterns to avoid (fuel, ad-hoc recovery)
- `../elixir/` — The language itself, authoritative AST examples

## Success Criteria

1. For valid code: `Hurricane.parse!(code) == Code.string_to_quoted!(code, ...)`
2. For broken code: Returns tree with error nodes, complete constructs intact
3. For adversarial code: Returns in bounded time, crashes only on actual bugs

## What Not To Do

1. **Don't use fuel** — Use advance assertions instead
2. **Don't recover ad-hoc** — Use explicit recovery sets
3. **Don't over-engineer** — No CST, no event layer, just emit AST
4. **Don't guess** — When unsure about AST format, test with `Code.string_to_quoted`
