# Hurricane: Resilient Elixir Parser for LSP

## Decision

**Clean-sheet implementation.** A resilient Elixir parser using proven techniques from
rust-analyzer and modern parsing research. Outputs standard Elixir AST for compatibility
with existing tooling.

## Why Hurricane Exists

Elixir's built-in parser (`Code.string_to_quoted`) fails on the first syntax error.
This is correct for compilation but unusable for IDE tooling, which must handle
incomplete, mid-edit code gracefully.

Hurricane provides:
- **Resilient parsing**: Always returns a tree, even for broken code
- **Predictable recovery**: Explicit synchronization points, not ad-hoc heuristics
- **Debuggable internals**: Stuck parser = immediate crash with exact location
- **AST compatibility**: Output matches `Code.string_to_quoted` for valid code

## Output Format

**Elixir AST with metadata.** Identical to:
```elixir
Code.string_to_quoted(code, columns: true, token_metadata: true)
```

This format has been stable for 10+ years. All existing Elixir tooling works unchanged.

## Architecture

```
Source → Lexer → Tokens → Parser → Elixir AST
                            ↓
                   LL (structure) + Pratt (expressions)
                   Recovery sets at every loop
                   Advance assertions for safety
```

### Component Responsibilities

| Component | Approach | Responsibility |
|-----------|----------|----------------|
| **Lexer** | Toxic (error-tolerant) | Tokens with full ranges, continues past errors |
| **Structure Parser** | Recursive descent | `defmodule`, `def`, `do/end`, `case`, etc. |
| **Expression Parser** | Pratt (operator precedence) | Operators, precedence, associativity |
| **Output** | Direct emission | Standard Elixir AST tuples |

## Non-Negotiables

### 1. Recovery Sets

Every parsing loop has explicit "sync tokens" — when lost, skip to known-good boundary.

| Construct | Sync Tokens |
|-----------|-------------|
| Module body | `def`, `defp`, `defmacro`, `defmodule`, `@`, `end`, `:eof` |
| Function body | `end`, `rescue`, `catch`, `else`, `after` |
| Parameters | `)`, `->`, `do`, `when`, `def*`, `end` |
| Case/cond clauses | `->`, `end`, `def*` |
| Collections | `]`, `}`, `>>`, `end`, `def*` |

### 2. Advance Assertions

Every loop iteration **must** consume at least one token. Violation = immediate crash
with exact location. No fuel counters. No silent hangs.

```elixir
# In every loop:
state = advance_push(state)
state = parse_item(state)
state = advance_pop!(state)  # Crashes if no progress
```

### 3. LL + Pratt Hybrid

- **Recursive descent** for structure (knows when to give up and sync)
- **Pratt parsing** for expressions (handles precedence elegantly)
- Not Pratt for everything — that's the mistake to avoid

## Error Representation

Errors are AST nodes:
```elixir
{:__block__, [error: true, line: n, column: m], []}
```

The tree is always structurally valid. Tooling sees complete constructs plus marked
error regions. No special error handling required downstream.

## Success Criteria

| Scenario | Requirement |
|----------|-------------|
| **Valid code** | AST identical to `Code.string_to_quoted` with metadata |
| **Broken code** | All complete constructs intact; incomplete ones have name/arity when possible |
| **Adversarial code** | Returns in bounded time; never hangs; crash = bug with exact location |

## What This Enables

- **Code indexing** works on broken files
- **Document outlines** show structure mid-edit
- **Go-to-definition** works even when current function is incomplete
- **Compiler provides diagnostics** — parser just provides the tree

## Relationship to Spitfire

Hurricane learns from Spitfire's precedence table (which is correct) but replaces:
- Ad-hoc recovery → Explicit recovery sets
- Fuel counter → Advance assertions
- Implicit sync points → Declared sync tokens

Same goal, more principled implementation.

## Key Insight

From matklad (rust-analyzer author):

> "Top-down (LL) parsing makes it harder to recognize valid small fragments, but
> **naturally allows for incomplete large nodes.**"

This is exactly what an LSP needs. When a user writes:

```elixir
defmodule Foo do
  def bar(x,        # incomplete!

  def baz(y) do     # complete
    y + 1
  end
end
```

The parser should:
1. Recognize `bar` is broken → emit error node, sync to next `def`
2. Parse `baz` perfectly
3. Close the module properly

Recovery sets make this explicit and predictable.
