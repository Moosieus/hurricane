# User typing a case expression
# Parser should handle incomplete clauses

defmodule MidEditCase do
  def incomplete_case(x) do
    case x do
      :a ->
      :b -> 2
    end
  end

  def another_incomplete(x) do
    case x do
      {:ok, value} ->

  def after_incomplete(x), do: x
end
