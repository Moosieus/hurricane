defmodule Hurricane.Parser.Recovery do
  @moduledoc """
  Recovery sets and IDE heuristics for resilient parsing.

  ## Three-Layer Recovery

  **Layer 1: Recovery Sets (Structural)**

  Token-based sync points that definitively end a construct: `:end`, `:eof`,
  `:->`, closing delimiters, block keywords. Use with `at_recovery?/2`:

      if Recovery.at_recovery?(state, Recovery.collection()) do
        # Hit closing delimiter, :end, or :eof
      end

  **Layer 2: Indentation Detection (Primary Heuristic)**

  When the current token's column is at or before the block's opening column,
  we've likely left that block. Uses `should_close_block?/1`:

      if Recovery.should_close_block?(state) do
        # Token dedented past block start - close the block
      end

  This works for ALL `do/end` constructs uniformly: `defmodule`, `def`, `case`,
  Phoenix's `scope`, ExUnit's `describe`, custom macros, etc.

  **Layer 3: Definition Detection (Secondary/Tiebreaker)**

  When indentation is ambiguous (same column as block start), the `def*` naming
  convention provides a secondary signal. Use `at_block_boundary?/2`:

      if Recovery.at_block_boundary?(state, Recovery.params()) do
        # Hit structural token OR dedented OR `def foo(...)`
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

  ## INDENTATION-BASED DETECTION (PRIMARY HEURISTIC)
  #
  # Elixir's formatter enforces 2-space indentation, making column position
  # a reliable signal of intended structure. When a token dedents past the
  # opening keyword's column, we've likely left that block.

  @doc """
  Check if we should close the current block based on indentation.

  Returns true if the current token's column is at or before the innermost
  block's opening column - a strong signal we've left that block.

  This works uniformly for all `do/end` constructs:
  - `defmodule`, `def`, `defp`, `defmacro`
  - `case`, `cond`, `if`, `unless`, `with`
  - `scope`, `pipeline` (Phoenix)
  - `describe`, `test` (ExUnit)
  - Any custom macro with do/end
  """
  def should_close_block?(state) do
    case State.current_block(state) do
      nil ->
        false

      {block_start_col, _type} ->
        current_token = State.current(state)

        case current_token do
          nil -> false
          %{column: current_col} -> current_col <= block_start_col
        end
    end
  end

  ## DEFINITION DETECTION (SECONDARY HEURISTIC/TIEBREAKER)
  #
  # When indentation is ambiguous (same column as block start), the `def*`
  # naming convention provides a secondary signal. This is NOT part of
  # structural parsing - it's an IDE heuristic for better mid-edit recovery.

  @doc """
  Check if the current position looks like a definition form.

  Uses Elixir's `def*` naming convention as a tiebreaker when indentation
  is ambiguous. Catches standard and custom definition macros:
  - Standard: def, defp, defmacro, defmodule, defstruct, etc.
  - Libraries: defn (Nx), defmemo, defrpc, etc.
  """
  def looks_like_definition?(state) do
    current = State.current(state)
    next = State.peek(state)

    case {current, next} do
      {%{kind: :identifier, value: name, line: curr_line}, %{kind: next_kind, line: next_line}}
      when next_kind in [:identifier, :paren_identifier, :do_identifier, :alias] and
             next_line - curr_line <= 1 ->
        definition_like_name?(name)

      _ ->
        false
    end
  end

  # Check if identifier follows Elixir's "def*" convention for definitions
  defp definition_like_name?(name) when is_atom(name) do
    name
    |> Atom.to_string()
    |> String.starts_with?("def")
  end

  @doc """
  Check if at a block boundary (all three layers combined).

  1. Structural: current token is in recovery_set
  2. Indentation: current token dedented past block start
  3. Definition: current token looks like `def* name` (tiebreaker)

  Use this in loops that need to detect when to close a block.
  """
  def at_block_boundary?(state, recovery_set) do
    State.at_any?(state, recovery_set) or
      should_close_block?(state) or
      looks_like_definition?(state)
  end

  @doc """
  Check if at a definition boundary (token-based OR pattern-based).

  DEPRECATED: Use `at_block_boundary?/2` instead, which includes indentation.
  Kept for backwards compatibility.
  """
  def at_definition_boundary?(state, recovery_set) do
    at_block_boundary?(state, recovery_set)
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
