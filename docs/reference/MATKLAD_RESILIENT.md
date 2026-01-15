# Resilient LL Parsing: Distilled

Source: https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html

## Core Principle

> "Resilient parsing means recovering as much syntactic structure from erroneous
> code as possible."

This is fundamentally different from error recovery in compilers. We accept
incomplete code as **ground truth**, not as something to be fixed.

## Why LL (Top-Down) for Resilience

> "Top-down (LL) parsing makes it harder to recognize valid small fragments, but
> **naturally allows for incomplete large nodes.**"

When a user writes:
```elixir
def foo(x,

def bar(y) do
```

An LL parser naturally:
1. Starts parsing `foo`, hits trouble
2. Can recognize the structure is incomplete
3. Moves on to `bar` which parses fine

LR/GLR parsers work bottom-up, which fights this pattern.

## The Key Technique: Recovery Sets

Every parsing loop needs to know when to stop trying. A **recovery set** is the
set of tokens that mean "this construct is over, move on."

```elixir
# Parsing function parameters
@param_recovery [:rparen, :arrow, :do, :when, :def, :end, :eof]

def parse_params(state) do
  expect(state, :lparen)

  while not at?(state, :rparen) and not at_any?(state, @param_recovery) do
    parse_param(state)
    eat(state, :comma)
  end

  expect(state, :rparen)
end
```

If we see `:def` while parsing params, we know the param list is broken but we
can sync to the next function.

## Recovery Set Design

For each construct, ask: "What tokens definitely mean this construct is over?"

| Construct | Recovery Tokens | Why |
|-----------|-----------------|-----|
| Module body | `def`, `defp`, `end`, `@` | Next item or module end |
| Function body | `end`, `rescue`, `catch` | Block terminators |
| Param list | `)`, `->`, `do`, `when` | Expected delimiters |
| Case clause | `->`, `end` | Next clause or case end |
| List items | `]`, `end` | List end or structural end |

## The Critical Rule

> "In any case, if a loop tries to parse an item, item parsing **must** consume
> at least one token (if only to report an error)."

This prevents infinite loops. Every loop iteration makes progress.

## Advance Assertions (from 2025 update)

Source: https://matklad.github.io/2025/12/28/parsing-advances.html

The 2025 update introduces explicit assertions for progress:

```elixir
def advance_push(state) do
  %{state | checkpoints: [state.pos | state.checkpoints]}
end

def advance_pop!(state) do
  [start | rest] = state.checkpoints
  if state.pos == start do
    raise "Parser stuck at #{start}: #{inspect(current_token(state))}"
  end
  %{state | checkpoints: rest}
end
```

Use in every loop:
```elixir
while not at_end?(state) do
  state = advance_push(state)
  state = parse_item(state)
  state = advance_pop!(state)  # Crashes if stuck
end
```

This transforms silent infinite loops into immediate, actionable crashes.

## Why Not Fuel?

Fuel (a decrementing counter) has problems:
1. **Imprecise errors**: "Ran out of fuel" tells you nothing
2. **False positives**: Deep valid nesting can exhaust fuel
3. **Masks bugs**: Parser gets stuck, burns fuel, eventually fails elsewhere

Advance assertions crash **immediately** at the **exact location** of the bug.

## Error Representation

Don't use exceptions or special error types. Errors are **nodes in the tree**:

```elixir
{:__block__, [error: true, line: 5, column: 3], []}
```

The tree is always structurally valid. Downstream code doesn't need special
error handling — it just sees a weird node it can skip.

## Handling Unexpected Tokens

When you see something unexpected:
1. Check if it's in the recovery set → break out of loop
2. Otherwise → emit error, consume token, continue

```elixir
def parse_statement(state) do
  cond do
    at?(state, :def) -> parse_def(state)
    at?(state, :if) -> parse_if(state)
    at_recovery?(state, @block_recovery) ->
      # Don't consume — let parent handle
      state
    true ->
      # Unknown token: error + consume + continue
      state
      |> emit_error("unexpected token")
      |> advance()
  end
end
```

## Sync Function

When recovery is needed, skip to the next sync point:

```elixir
def sync_to(state, recovery_set) do
  if at_any?(state, recovery_set) or at?(state, :eof) do
    state
  else
    state |> advance() |> sync_to(recovery_set)
  end
end
```

## Testing Resilience

For each error scenario, verify:
1. Parser doesn't crash or hang
2. Complete constructs after the error are intact
3. Error is localized to the broken region

```elixir
test "recovers from broken function" do
  code = """
  def broken(x,

  def working(y), do: y
  """

  {:ok, ast} = parse(code)
  assert find_function(ast, :working) != nil
  assert function_body(ast, :working) == quote(do: y)
end
```

## Summary for Hurricane

1. **Use recovery sets** at every loop — explicit sync points
2. **Use advance assertions** — catch stuck parsers immediately
3. **Errors are nodes** — tree is always valid
4. **LL for structure** — natural incomplete-node handling
5. **Test with broken code** — verify recovery, not just happy path
