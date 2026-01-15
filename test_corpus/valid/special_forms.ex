# Special forms - case, cond, with, try, fn, for

defmodule SpecialForms do
  # Case with multiple clauses
  def with_case(x) do
    case x do
      {:ok, value} -> value
      {:error, reason} -> raise reason
      nil -> :default
      _ -> :unknown
    end
  end

  # Cond
  def with_cond(x) do
    cond do
      x < 0 -> :negative
      x == 0 -> :zero
      x > 0 -> :positive
    end
  end

  # With expression
  def with_with(opts) do
    with {:ok, a} <- fetch_a(opts),
         {:ok, b} <- fetch_b(a),
         {:ok, c} <- fetch_c(b) do
      {:ok, a + b + c}
    else
      {:error, reason} -> {:error, reason}
      _ -> {:error, :unknown}
    end
  end

  # Try/rescue/catch/after
  def with_try do
    try do
      dangerous_operation()
    rescue
      e in RuntimeError -> {:error, e.message}
      ArgumentError -> {:error, :bad_arg}
    catch
      :exit, reason -> {:exit, reason}
      :throw, value -> {:throw, value}
    after
      cleanup()
    end
  end

  # Anonymous functions
  def with_fn do
    single = fn x -> x + 1 end

    multi = fn
      :a -> 1
      :b -> 2
      _ -> 0
    end

    captured = &(&1 + &2)
    captured_named = &Enum.map/2
  end

  # Comprehensions
  def with_for do
    for x <- 1..10, x > 5, do: x * 2

    for x <- list,
        y <- other_list,
        x != y,
        into: %{} do
      {x, y}
    end
  end

  # If/unless
  def with_if(x) do
    if x > 0 do
      :positive
    else
      :non_positive
    end

    unless x == 0, do: x, else: 1
  end

  # Quote/unquote
  defmacro with_quote(expr) do
    quote do
      result = unquote(expr)
      {result, unquote(Macro.to_string(expr))}
    end
  end

  # Receive
  def with_receive do
    receive do
      {:msg, content} -> handle(content)
      :stop -> :ok
    after
      5000 -> :timeout
    end
  end
end
