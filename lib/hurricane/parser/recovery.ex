defmodule Hurricane.Parser.Recovery do
  @moduledoc """
  Recovery set definitions for resilient parsing.

  ## Philosophy: Pattern-Based Definition Detection

  Like Elixir's actual parser (elixir_parser.yrl), we don't treat `def`, `defmodule`,
  etc. as special keywords at the syntax level. They're all just regular calls with
  do blocks. This means `def`, `defn`, `defmemo`, and any custom definition macro
  are handled uniformly.

  Definition forms are detected by pattern: `identifier` followed by
  `identifier|paren_identifier|do_identifier|alias`. This catches:
  - `def foo(x)` - def is identifier, foo is paren_identifier
  - `defmodule Foo` - defmodule is identifier, Foo is alias
  - `defn softmax(t)` - defn is identifier, softmax is paren_identifier

  ## Recovery Sets

  Recovery sets define "sync tokens" - structural tokens that definitively end
  a construct (`:end`, `:eof`, `:->`  etc.). Definition boundaries are detected
  by pattern, not enumerated in recovery sets.

  ## Usage

  For definition contexts, use `at_definition_boundary?/2`:

      if Recovery.at_definition_boundary?(state, Recovery.params()) do
        # Stop - we've hit a definition form OR structural token
        ...
      end

  For non-definition contexts, use `at_recovery?/2`:

      if Recovery.at_recovery?(state, Recovery.collection()) do
        # Stop - we've hit a structural token
        ...
      end
  """

  alias Hurricane.Parser.State

  ## SHARED TOKEN SETS

  @closing_delimiters [:rparen, :rbracket, :rbrace, :rangle]

  @doc "Closing delimiter tokens (orphan closers that indicate recovery points)."
  def closing_delimiters, do: @closing_delimiters

  ## RECOVERY SET DEFINITIONS

  @doc """
  Recovery set for module body items.
  Tokens that indicate the start of a new module-level item or end of module.

  Note: Definition-like forms (def, defmodule, import, use, etc.) are NOT included
  here - they're detected by pattern via `looks_like_definition?/1`. This makes
  custom macros like defn first-class citizens and treats directives uniformly.
  """
  def module_body do
    [
      :@,
      # Stab arrow - indicates stray arrow from incomplete pattern
      :->,
      :end,
      :eof
    ]
  end

  @doc """
  Recovery set for block body (do/end contents in modules).
  Tokens that indicate block termination or new block section.
  Does NOT include definition keywords - those are valid in module bodies.
  """
  def block_body do
    [
      :end,
      :rescue,
      :catch,
      :else,
      :after,
      # Stab arrow - indicates stray arrow from incomplete pattern
      :->
      | @closing_delimiters ++ [:eof]
    ]
  end

  @doc """
  Recovery set for function body (do/end contents in functions).
  Definition patterns are detected by `looks_like_definition?/1` via `at_definition_boundary?/2`.
  """
  def function_body do
    [
      :end,
      :rescue,
      :catch,
      :else,
      :after,
      # Stab arrow - indicates stray arrow from incomplete pattern
      :->
      | @closing_delimiters ++ [:eof]
    ]
  end

  @doc """
  Recovery set for parameter lists.
  Tokens that indicate end of parameter parsing.
  Definition patterns are detected by `looks_like_definition?/1` via `at_definition_boundary?/2`.
  """
  def params do
    [
      :rparen,
      :->,
      :do,
      :when,
      :end,
      :eof
    ]
  end

  @doc """
  Recovery set for stab clauses (case/cond/fn bodies).
  Tokens that indicate end of a clause or the block.
  """
  def stab_clause do
    [
      :->,
      :end,
      :else,
      :rescue,
      :catch,
      :after,
      :eof
    ]
  end

  @doc """
  Recovery set for collection contents (list, tuple, map, binary).
  Tokens that indicate end of collection.
  """
  def collection do
    @closing_delimiters ++ [:end, :eof]
  end

  @doc """
  Recovery set for expressions.
  Tokens that indicate end of expression context.
  Definition patterns are detected by `looks_like_definition?/1` via `at_definition_boundary?/2`.
  """
  def expression do
    [
      :comma,
      :do,
      :end,
      :rescue,
      :catch,
      :else,
      :after,
      :->
      | @closing_delimiters ++ [:eof]
    ]
  end

  @doc """
  Recovery set for with clauses.
  """
  def with_clause do
    [
      :do,
      :else,
      :end,
      :eof
    ]
  end

  ## PATTERN-BASED DETECTION

  # Keywords that should not trigger definition detection when they appear
  # as the first identifier. These are:
  # - Operators: and, or, not, in, when
  # - Common macros that take expressions: if, unless, raise, throw, import, etc.
  #
  # We exclude these because `if user` shouldn't look like a definition, even though
  # it matches the pattern "identifier followed by identifier".
  @non_definition_identifiers [
    # Operators
    :and,
    :or,
    :not,
    :in,
    :when,
    # Control flow macros
    :if,
    :unless,
    :raise,
    :reraise,
    :throw,
    # Directive macros
    :import,
    :alias,
    :require,
    :use
  ]

  @doc """
  Check if the current position looks like a definition form.

  Detects the pattern: `identifier` followed by `identifier|paren_identifier|do_identifier|alias`

  This catches ALL definition forms uniformly - both built-in (def, defmodule, defmacro)
  and custom (defn, defmemo, defrpc). This aligns with how Elixir's parser works: it
  doesn't know about def as special syntax, just as a regular call with a do block.

  Examples that match:
  - `def foo(x)` - def is identifier, foo is paren_identifier
  - `defmodule Foo do` - defmodule is identifier, Foo is alias
  - `defn softmax(t)` - defn is identifier, softmax is paren_identifier

  Examples that don't match:
  - `Logger.info` - Logger is alias, not identifier
  - `and foo` - and is excluded as a keyword
  - `user ... s` - tokens separated by blank line aren't definitions
  """
  def looks_like_definition?(state) do
    current = State.current(state)
    next = State.peek(state)

    case {current, next} do
      {%{kind: :identifier, value: name, line: curr_line}, %{kind: next_kind, line: next_line}}
      when next_kind in [:identifier, :paren_identifier, :do_identifier, :alias] and
             name not in @non_definition_identifiers and
             next_line - curr_line <= 1 ->
        true

      _ ->
        false
    end
  end

  @doc """
  Check if at a definition boundary (token-based OR pattern-based).

  Since def* keywords are no longer given special token kinds (they stay as identifiers),
  ALL definition forms (def, defmodule, defn, defmemo, etc.) are detected by pattern.
  The recovery_set catches structural tokens like :end, :@, :eof.
  """
  def at_definition_boundary?(state, recovery_set) do
    State.at_any?(state, recovery_set) or looks_like_definition?(state)
  end

  ## RECOVERY OPERATIONS

  @doc """
  Check if the current token is in the given recovery set.
  """
  def at_recovery?(state, recovery_set) do
    State.at_any?(state, recovery_set)
  end

  @doc """
  Skip tokens until we reach one in the recovery set.
  Returns the state positioned at the first recovery token.
  """
  def sync_to(state, recovery_set) do
    if State.at_any?(state, recovery_set) or State.at_end?(state) do
      state
    else
      {state, _token} = State.advance(state)
      sync_to(state, recovery_set)
    end
  end

  @doc """
  Skip tokens until we reach one in the recovery set, emitting a single error.
  """
  def sync_to_with_error(state, recovery_set, message) do
    if State.at_any?(state, recovery_set) or State.at_end?(state) do
      state
    else
      state = State.add_error(state, message)
      skip_to(state, recovery_set)
    end
  end

  @doc """
  Skip tokens until we reach one in the recovery set (no error emission).
  Use when error was already emitted.
  """
  def skip_to(state, recovery_set) do
    if State.at_any?(state, recovery_set) or State.at_end?(state) do
      state
    else
      {state, _token} = State.advance(state)
      skip_to(state, recovery_set)
    end
  end
end
