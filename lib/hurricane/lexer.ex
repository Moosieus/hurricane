defmodule Hurricane.Lexer do
  @moduledoc """
  Lexer that wraps :elixir_tokenizer and produces Hurricane.Token structs.

  Handles both successful tokenization and partial results from broken code.
  """

  alias Hurricane.Token

  @doc """
  Tokenize source code into a list of tokens.

  Returns `{:ok, tokens}` on success, or `{:ok, tokens}` with partial results
  on error (for resilient parsing). The token list always ends with an :eof token.
  """
  def tokenize(source) when is_binary(source) do
    charlist = String.to_charlist(source)

    case :elixir_tokenizer.tokenize(charlist, 1, 1, []) do
      {:ok, end_line, end_column, _warnings, raw_tokens, _terminators} ->
        tokens = build_tokens(raw_tokens, end_line, end_column)
        {:ok, tokens}

      {:error, _error_info, _remaining, _warnings, partial_tokens} ->
        # On error, we still return partial tokens for resilient parsing
        # Use last token position or default to 1,1 for EOF
        {end_line, end_column} = last_position(partial_tokens)
        tokens = build_tokens(partial_tokens, end_line, end_column)
        {:ok, tokens}
    end
  end

  defp build_tokens(raw_tokens, end_line, end_column) do
    # Raw tokens are in reverse order from :elixir_tokenizer
    tokens =
      raw_tokens
      |> Enum.reverse()
      |> Enum.map(&Token.from_raw/1)
      |> filter_eol_tokens()

    # Always append EOF
    tokens ++ [Token.eof(end_line, end_column)]
  end

  # Filter out consecutive EOL tokens and leading EOLs
  # Keep EOLs that are semantically significant (after expressions)
  defp filter_eol_tokens(tokens) do
    tokens
    |> Enum.reject(fn token -> token.kind == :eol end)
  end

  defp last_position([]) do
    {1, 1}
  end

  defp last_position([{_, {line, column, _}} | _]) do
    {line, column}
  end

  defp last_position([{_, {line, column, _}, _} | _]) do
    {line, column}
  end
end
