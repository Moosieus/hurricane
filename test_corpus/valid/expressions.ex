# Expression tests - operators, precedence, associativity

defmodule Expressions do
  # Arithmetic precedence
  def arith do
    1 + 2 * 3           # 1 + (2 * 3)
    (1 + 2) * 3         # explicit grouping
    1 - 2 - 3           # left-assoc: (1 - 2) - 3
  end

  # Right-associative
  def right_assoc do
    a = b = c = 1       # a = (b = (c = 1))
    [1 | [2 | [3 | []]]]  # cons is right-assoc
    a ++ b ++ c         # a ++ (b ++ c)
  end

  # Pipe operator
  def pipes do
    value
    |> transform()
    |> filter(& &1 > 0)
    |> Enum.map(&(&1 * 2))
  end

  # Boolean operators
  def boolean do
    a and b or c        # (a and b) or c
    a || b && c         # a || (b && c)
    not a and b         # (not a) and b
  end

  # Comparison chaining
  def comparison do
    a == b != c         # (a == b) != c
    a < b <= c          # (a < b) <= c
  end

  # Match operator
  def pattern_match do
    {:ok, result} = fetch()
    %{name: name} = user
    [head | tail] = list
  end

  # Unary operators
  def unary do
    -x
    +y
    !flag
    not condition
    ^pinned
    &captured
    ~~~bits
  end

  # Access and calls
  def access do
    map[:key]
    map.field
    Module.function(arg)
    fun.(arg)
    nested[:a][:b][:c]
  end
end
