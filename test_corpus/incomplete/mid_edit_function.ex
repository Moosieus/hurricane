# Simulates user mid-edit: incomplete function, but next function is valid
# Parser should:
# - Recognize broken_function as incomplete def
# - Parse working_function completely
# - Parse the module structure

defmodule MidEdit do
  def broken_function(x,

  def working_function(y) do
    y + 1
  end
end
