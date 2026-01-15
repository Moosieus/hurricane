# Many unclosed constructs - parser must not hang
# Should return quickly with errors

defmodule Unclosed do
  def unclosed_list do
    [[[[[
  end

  def unclosed_tuple do
    {{{{{
  end

  def unclosed_map do
    %{%{%{%{%{
  end

  def unclosed_fn do
    fn -> fn -> fn -> fn ->
  end

  def unclosed_do do
    if true do
      if true do
        if true do
          if true do
