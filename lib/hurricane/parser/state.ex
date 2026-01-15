defmodule Hurricane.Parser.State do
  @moduledoc """
  Parser state management and core operations.

  The state tracks:
  - Token stream (as a list with current position)
  - Position index (for advance assertions)
  - Checkpoint stack (for detecting stuck parsers)
  - Accumulated errors
  - AST fragments being built
  """

  alias Hurricane.Token

  defstruct [
    :tokens,
    :pos,
    :checkpoints,
    :errors,
    :ast
  ]

  @type t :: %__MODULE__{
          tokens: [Token.t()],
          pos: non_neg_integer(),
          checkpoints: [non_neg_integer()],
          errors: [{map(), String.t()}],
          ast: any()
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
      ast: nil
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
  """
  def expect(state, kind) do
    if at?(state, kind) do
      advance(state)
    else
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
  """
  def add_error(state, message) do
    token = current(state)

    meta =
      if token do
        %{line: token.line, column: token.column}
      else
        %{line: 1, column: 1}
      end

    %{state | errors: [{meta, message} | state.errors]}
  end

  @doc """
  Emit an error and consume the current token to make progress.
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
end
