# Extra/misplaced tokens
# Parser should skip and continue

defmodule ExtraTokens do
  def double_comma(x,, y) do
    x + y
  end

  def extra_paren(x)) do
    x
  end

  def missing_comma(x y z) do
    x + y + z
  end

  def valid_at_end(x), do: x
end
