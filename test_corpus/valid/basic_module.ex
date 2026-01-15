# Basic module with functions
# Should parse identically to Code.string_to_quoted

defmodule BasicModule do
  @moduledoc "A basic module for testing"

  @default_value 42

  def public_function(x) do
    x + @default_value
  end

  def with_guard(x) when is_integer(x) do
    x * 2
  end

  def multi_clause(:a), do: 1
  def multi_clause(:b), do: 2
  def multi_clause(_), do: 0

  defp private_function(x, y) do
    x + y
  end
end
