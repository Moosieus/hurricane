# Mismatched brackets/parens
# Parser should recover at structural boundaries

defmodule MismatchedDelimiters do
  def list_with_brace do
    [1, 2, 3}
  end

  def tuple_with_bracket do
    {1, 2, 3]
  end

  def paren_with_bracket do
    foo(1, 2]
  end

  def valid_function(x), do: x
end
