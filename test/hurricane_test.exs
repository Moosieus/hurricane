defmodule HurricaneTest do
  use ExUnit.Case
  doctest Hurricane

  test "greets the world" do
    assert Hurricane.hello() == :world
  end
end
