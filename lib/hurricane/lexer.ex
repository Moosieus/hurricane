defmodule Hurricane.Lexer do
  @moduledoc """
  Lexer that uses Toxic for error-tolerant tokenization.

  This lexer provides resilient tokenization that continues past errors,
  enabling Hurricane to parse valid code that appears after lexer errors.
  """

  alias Hurricane.Lexer.ToxicAdapter

  @doc """
  Tokenize source code into a list of tokens.

  Returns `{:ok, tokens}` where tokens is a list of Hurricane.Token structs.
  The token list always ends with an :eof token.

  Unlike :elixir_tokenizer, this lexer continues past errors, emitting
  :error_token tokens inline, allowing the parser to handle them gracefully.
  """
  defdelegate tokenize(source), to: ToxicAdapter
end
