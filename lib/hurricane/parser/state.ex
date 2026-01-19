defmodule Hurricane.Parser.State do
  @moduledoc """
  Parser state management and core operations.

  The state tracks:
  - Token stream (as a list with current position)
  - Position index (for advance assertions)
  - Checkpoint stack (for detecting stuck parsers)
  - Accumulated errors
  - AST fragments being built

  ## Advance Assertions

  Every loop that parses items must use advance assertions to prevent infinite loops:

      state = advance_push(state)
      {state, item} = parse_item(state)
      state = advance_pop!(state)  # Crashes immediately if stuck

  If a function may legitimately exit without consuming tokens:

      state = advance_push(state)
      {state, result} = try_parse(state)
      if consumed? do
        state = advance_pop!(state)
      else
        state = advance_drop(state)  # Clear checkpoint, no assertion
      end

  This materializes the "must consume" contract in code rather than relying on
  mental tracking of which functions advance vs. which may bail.
  """

  alias Hurricane.Token

  defstruct [
    :tokens,
    :pos,
    :checkpoints,
    :errors,
    :ast,
    :block_stack,
    :recovery_counter
  ]

  @type t :: %__MODULE__{
          tokens: [Token.t()],
          pos: non_neg_integer(),
          checkpoints: [non_neg_integer()],
          errors: [{map(), String.t()}],
          ast: any(),
          block_stack: [{pos_integer(), atom()}],
          recovery_counter: :counters.counters_ref() | nil
        }

  @doc """
  Create a new parser state from a list of tokens.
  """
  def new(tokens) when is_list(tokens) do
    %__MODULE__{
      tokens: tokens,
      pos: 0,
      checkpoints: [],
      errors: [],
      ast: nil,
      block_stack: [],
      recovery_counter: :counters.new(1, [:write_concurrency])
    }
  end

  ## TOKEN INSPECTION

  @doc """
  Get the current token without consuming it.
  """
  def current(%__MODULE__{tokens: tokens, pos: pos}) do
    Enum.at(tokens, pos)
  end

  @doc """
  Peek at the next token (one ahead of current).
  """
  def peek(%__MODULE__{tokens: tokens, pos: pos}) do
    Enum.at(tokens, pos + 1)
  end

  @doc """
  Get the previous token (one before current).
  """
  def prev(%__MODULE__{tokens: tokens, pos: pos}) when pos > 0 do
    Enum.at(tokens, pos - 1)
  end

  def prev(_state), do: nil

  @doc """
  Check if there's a newline between previous token and current token.
  Used to detect expression boundaries.
  """
  def newline_before?(state) do
    case {prev(state), current(state)} do
      {%{line: prev_line}, %{line: curr_line}} when curr_line > prev_line -> true
      _ -> false
    end
  end

  @doc """
  Count the number of newlines between previous token and current token.
  Returns 0 if no newlines, otherwise the line difference.
  Used for metadata like `newlines: 1` on operators.
  """
  def newlines_before(state) do
    case {prev(state), current(state)} do
      {%{end_line: prev_end_line}, %{line: curr_line}} when curr_line > prev_end_line ->
        curr_line - prev_end_line

      _ ->
        0
    end
  end

  @doc """
  Get the kind of the current token.
  """
  def current_kind(state) do
    case current(state) do
      nil -> :eof
      token -> token.kind
    end
  end

  @doc """
  Check if the current token is of the given kind.
  """
  def at?(state, kind) do
    current_kind(state) == kind
  end

  @doc """
  Check if the current token is any of the given kinds.
  """
  def at_any?(state, kinds) when is_list(kinds) do
    current_kind(state) in kinds
  end

  @doc """
  Check if we've reached the end of input.
  """
  def at_end?(state) do
    at?(state, :eof)
  end

  ## TOKEN CONSUMPTION

  @doc """
  Consume the current token and advance to the next.
  Returns the new state and the consumed token.
  """
  def advance(state) do
    token = current(state)
    {%{state | pos: state.pos + 1}, token}
  end

  @doc """
  Consume the current token if it matches the given kind.
  Returns `{:ok, state, token}` on match, `{:error, state}` otherwise.
  """
  def eat(state, kind) do
    if at?(state, kind) do
      {new_state, token} = advance(state)
      {:ok, new_state, token}
    else
      {:error, state}
    end
  end

  @doc """
  Expect the current token to be of the given kind.
  Consumes it on success, emits error and continues on failure.
  Returns `{state, token | nil}`.

  When Toxic inserts error_tokens followed by synthetic delimiters,
  we need to skip past error_tokens to find the expected token.
  """
  def expect(state, kind) do
    cond do
      at?(state, kind) ->
        advance(state)

      # Skip error_token and check if next token matches
      # This handles Toxic's pattern of: error_token, synthetic_delimiter
      at?(state, :error_token) ->
        {state, error_token} = advance(state)
        error = error_token.value

        error_msg =
          if is_struct(error) and Map.has_key?(error, :message),
            do: error.message,
            else: "lexer error"

        state = add_error(state, error_msg)

        # Now try to match the expected token
        if at?(state, kind) do
          advance(state)
        else
          token = current(state)
          message = "expected #{inspect(kind)}, got #{inspect(token && token.kind)}"
          state = add_error(state, message)
          {state, nil}
        end

      true ->
        token = current(state)
        message = "expected #{inspect(kind)}, got #{inspect(token && token.kind)}"
        state = add_error(state, message)
        {state, nil}
    end
  end

  @doc """
  Consume any of the given token kinds.
  Returns `{:ok, state, token}` on match, `{:error, state}` otherwise.
  """
  def eat_any(state, kinds) do
    if at_any?(state, kinds) do
      {new_state, token} = advance(state)
      {:ok, new_state, token}
    else
      {:error, state}
    end
  end

  ## ERROR HANDLING

  @doc """
  Add an error at the current position.
  Also increments the recovery counter since encountering an error triggers recovery logic.
  """
  def add_error(state, message) do
    token = current(state)

    meta =
      if token do
        %{line: token.line, column: token.column}
      else
        %{line: 1, column: 1}
      end

    # Increment recovery counter - any error on valid code indicates a parser issue
    state = increment_recovery_count(state)
    %{state | errors: [{meta, message} | state.errors]}
  end

  @doc """
  Emit an error and consume the current token to make progress.
  Note: add_error already increments the recovery counter.
  """
  def advance_with_error(state, message) do
    state = add_error(state, message)
    {new_state, _token} = advance(state)
    new_state
  end

  @doc """
  Get all accumulated errors (in order they occurred).
  """
  def errors(state) do
    Enum.reverse(state.errors)
  end

  ## RECOVERY COUNTER

  @doc """
  Increment the recovery counter.
  Call this when the parser uses a recovery set to skip tokens.
  """
  def increment_recovery_count(state) do
    if state.recovery_counter do
      :counters.add(state.recovery_counter, 1, 1)
    end

    state
  end

  @doc """
  Get the current recovery count.
  """
  def recovery_count(state) do
    if state.recovery_counter do
      :counters.get(state.recovery_counter, 1)
    else
      0
    end
  end

  ## ADVANCE ASSERTIONS

  @doc """
  Push current position onto checkpoint stack before a loop iteration.
  """
  def advance_push(state) do
    %{state | checkpoints: [state.pos | state.checkpoints]}
  end

  @doc """
  Pop checkpoint and assert progress was made.
  Raises if parser is stuck at the same position.
  """
  def advance_pop!(state) do
    case state.checkpoints do
      [] ->
        raise "advance_pop! called without matching advance_push"

      [start | rest] ->
        if state.pos == start do
          token = current(state)

          raise """
          Parser stuck at position #{start}
          Token: #{inspect(token)}
          This is a bug in the parser - every loop iteration must consume at least one token.
          """
        end

        %{state | checkpoints: rest}
    end
  end

  @doc """
  Drop checkpoint without asserting progress.
  Use for early returns when legitimately not consuming tokens.
  """
  def advance_drop(state) do
    case state.checkpoints do
      [] ->
        raise "advance_drop called without matching advance_push"

      [_start | rest] ->
        %{state | checkpoints: rest}
    end
  end

  ## POSITION HELPERS

  @doc """
  Get metadata (line/column) for the current position.
  """
  def current_meta(state) do
    case current(state) do
      nil -> [line: 1, column: 1]
      token -> [line: token.line, column: token.column]
    end
  end

  @doc """
  Get metadata from a token.
  """
  def token_meta(nil), do: [line: 1, column: 1]
  def token_meta(token), do: [line: token.line, column: token.column]

  ## BLOCK STACK (for indentation-aware recovery)

  @doc """
  Push a block onto the stack when entering a do/end block.
  Tracks the opening keyword's column for indentation-based recovery.
  """
  def push_block(state, column, type \\ :do) do
    %{state | block_stack: [{column, type} | state.block_stack]}
  end

  @doc """
  Pop a block from the stack when exiting a do/end block.
  """
  def pop_block(state) do
    case state.block_stack do
      [_ | rest] -> %{state | block_stack: rest}
      [] -> state
    end
  end

  @doc """
  Get the current (innermost) block, or nil if not in a block.
  Returns `{column, type}` tuple.
  """
  def current_block(state) do
    List.first(state.block_stack)
  end
end
