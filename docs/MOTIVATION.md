# Motivations for Hurricane

* A unified parser is a non-goal. maklad indicated he wanted rustc and rust_analyzer to share a parser in 2020, but progress was slow and eventually halted in 2023. A unified tokenizer would be more doable if anything.

* Emit AST directly for now - it's comparable against Code.string_to_quoted, making correctness easy to verify. CST could be layered on later if needed for IDE features (formatting, refactoring).

* LL + Pratt parsing pair very well for resilient parsing, and is allegedly a successful pattern for language server parsers. LL parsing works well for statement-like syntax (defmodule, fn, etc) and Pratt works well for expression-like syntax (pipes, infix arithmetic, etc) They cover each other’s weak spots well.
  * Elixir has both block-structured syntax (defmodule, do...end, fn, etc.) and operator-driven syntax (pipes, arithmetic, dot-access, etc.). LL parsing is a natural fit for block structure; Pratt is a natural fit for operators. Everything is an expression at the AST-level, but that's a technicality as far as syntax is concerned.

* I've tried my best to make Hurricane debuggable. This is done through the following means:
  * Used 'advance assertions' instead of fuel as suggested by matklad. That is, assert when tokens should be consumed and exit if they aren’t. Many parsers have historically used “fuel” to guard against infinite recursion, but tracking the root cause of fuel exhaustion can be difficult.
  * Try keeping recovery sets to a centralized module, and count the number of recoveries that are actually invoked. The actual parser unto itself concerns itself with what's right and wrong, and delegates the work of getting back on track. 
