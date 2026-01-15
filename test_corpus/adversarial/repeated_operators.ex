# Repeated operators without operands
# Parser should not loop forever

defmodule RepeatedOperators do
  def repeated_plus do
    1 + + + + + 2
  end

  def repeated_pipe do
    x |> |> |> |> y
  end

  def trailing_operator do
    1 +
  end

  def leading_operator do
    + 1
  end

  def only_operators do
    + - * /
  end
end
