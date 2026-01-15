# Incomplete collections
# Parser should recover at structural boundaries

defmodule MidEditList do
  def incomplete_list do
    [1, 2, 3,
  end

  def incomplete_tuple do
    {1, 2,
  end

  def incomplete_map do
    %{a: 1, b:
  end

  def valid_function(x), do: x * 2
end
