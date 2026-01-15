defmodule Hurricane.Parser.Recovery do
  @moduledoc """
  Recovery set definitions for resilient parsing.

  Recovery sets define "sync tokens" - tokens that definitively end a construct.
  When the parser gets lost, it can skip to the next token in the recovery set
  to continue parsing subsequent valid code.

  ## Usage

  At every parsing loop, check if we've hit a recovery token:

      if State.at_any?(state, Recovery.module_body()) do
        # Stop parsing this construct, parent will handle
        state
      else
        # Continue parsing
        ...
      end
  """

  alias Hurricane.Parser.State

  ## RECOVERY SET DEFINITIONS

  @doc """
  Recovery set for module body items.
  Tokens that indicate the start of a new module-level item or end of module.
  """
  def module_body do
    [
      :def,
      :defp,
      :defmacro,
      :defmacrop,
      :defmodule,
      :defstruct,
      :defprotocol,
      :defimpl,
      :defdelegate,
      :defguard,
      :defguardp,
      :defexception,
      :defoverridable,
      :@,
      :use,
      :import,
      :alias_directive,
      :require,
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
      :eof
    ]
  end

  @doc """
  Recovery set for function body (do/end contents in functions).
  Includes definition keywords which indicate incomplete function body.
  """
  def function_body do
    [
      :end,
      :rescue,
      :catch,
      :else,
      :after,
      # Definition keywords - indicate function body ended abnormally
      :def,
      :defp,
      :defmacro,
      :defmacrop,
      :defmodule,
      :eof
    ]
  end

  @doc """
  Recovery set for parameter lists.
  Tokens that indicate end of parameter parsing.
  """
  def params do
    [
      :rparen,
      :->,
      :do,
      :when,
      :def,
      :defp,
      :defmacro,
      :defmacrop,
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
    [
      :rbracket,
      :rbrace,
      :rparen,
      :rangle,
      :end,
      :eof
    ]
  end

  @doc """
  Recovery set for expressions.
  Tokens that indicate end of expression context.
  """
  def expression do
    [
      :comma,
      :rparen,
      :rbracket,
      :rbrace,
      :rangle,
      :do,
      :end,
      :rescue,
      :catch,
      :else,
      :after,
      :->,
      # Definition keywords - should not be consumed by expression parser
      :def,
      :defp,
      :defmacro,
      :defmacrop,
      :defmodule,
      :eof
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
