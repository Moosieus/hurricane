# Hurricane

An experimental resilient Elixir parser for IDE/LSP tooling. Produces standard Elixir AST and always returns a tree, even for broken or incomplete code.

## Motivation

Elixir's built-in parser (`Code.string_to_quoted`) fails on the first syntax error—correct for compilation, but unusable for IDE tooling that must handle mid-edit code gracefully.

Existing solutions like [Spitfire](https://github.com/elixir-tools/spitfire) use pure Pratt parsing. Hurricane takes a different approach inspired by [matklad's writings on resilient parsing](https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html) (the techniques behind rust-analyzer):

- **LL + Pratt hybrid**: Recursive descent for structure (`defmodule`, `case`, `do/end`), Pratt parsing for expressions
- **Explicit recovery sets**: Every parsing loop knows its synchronization points—when lost, skip to a known-good boundary
- **Advance assertions**: Every loop iteration must consume at least one token, or the parser crashes with the exact stuck location. No fuel counters, no silent hangs.

## Status

Successfully parses 10,000+ lines of production Phoenix/Ecto/LiveView code including contexts, schemas, routers, LiveView modules, GenServers, ExUnit tests, and config files.

## Design

```
Source → Lexer → Tokens → Parser → Elixir AST
                            ↓
                   LL (structure) + Pratt (expressions)
                   Recovery sets at every loop
                   Advance assertions for safety
```

| Component | Approach | Responsibility |
|-----------|----------|----------------|
| **Lexer** | Toxic (error-tolerant) | Tokens with full ranges, continues past errors |
| **Structure Parser** | Recursive descent | `defmodule`, `def`, `do/end`, `case`, etc. |
| **Expression Parser** | Pratt (binding power) | Operators, precedence, associativity |
| **Output** | Direct emission | Standard Elixir AST tuples |

For valid input, output matches `Code.string_to_quoted(code, columns: true)`. For invalid input, it returns partial AST with accumulated errors.

## Acknowledgments

This parser was largely implemented by Claude (Opus 4.5) based on design documents I wrote after reading matklad's blog posts. I don't know how to write parsers—I just knew what I wanted and let the AI do the legwork.

## Installation

If [available in Hex](https://hex.pm/docs/publish), the package can be installed
by adding `hurricane` to your list of dependencies in `mix.exs`:

```elixir
def deps do
  [
    {:hurricane, "~> 0.1.0"}
  ]
end
```

Documentation can be generated with [ExDoc](https://github.com/elixir-lang/ex_doc)
and published on [HexDocs](https://hexdocs.pm). Once published, the docs can
be found at <https://hexdocs.pm/hurricane>.

