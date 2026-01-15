# Wrong or misplaced keywords
# Parser should recover

defmodule WrongKeywords do
  def missing_do(x)
    x + 1
  end

  def extra_end(x) do
    x
  end
  end

  def misplaced_else(x) do
    x
  else
    y
  end

  def valid_function(x), do: x
end
