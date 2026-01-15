defmodule Hurricane.Lexer.ToxicAdapter do
  @moduledoc """
  Adapter for the Toxic error-tolerant lexer.

  This module provides the bridge between Toxic's streaming tokenizer and
  Hurricane's token format. The key benefits over :elixir_tokenizer are:

  1. **Error recovery**: Toxic continues tokenizing after errors, emitting
     error tokens inline, allowing Hurricane to parse valid code after errors.

  2. **Ranged positions**: Toxic provides both start AND end positions for
     every token, enabling precise "cursor in token" queries for IDE features.

  The conversion pipeline:
  1. Toxic.new/4 - Create a streaming tokenizer in tolerant mode
  2. Toxic.to_stream/1 - Convert to Elixir stream
  3. Toxic.Legacy.collapse_linear_ranges/1 - Collapse linearized strings/sigils
  4. Convert to Hurricane.Token structs (preserving full ranges)
  """

  alias Hurricane.Token

  @doc """
  Tokenize source code using Toxic in tolerant mode.

  Returns `{:ok, tokens}` where tokens is a list of Hurricane.Token structs.
  Error tokens are included inline rather than stopping tokenization.
  Each token includes both start and end positions.
  """
  def tokenize(source) when is_binary(source) do
    stream = Toxic.new(source, 1, 1, error_mode: :tolerant)

    tokens =
      stream
      |> Toxic.to_stream()
      |> Enum.to_list()
      |> Toxic.Legacy.collapse_linear_ranges()
      # Note: We skip ranges_to_legacy to preserve end positions!
      |> convert_tokens()

    {:ok, tokens}
  end

  defp convert_tokens(ranged_tokens) do
    tokens =
      ranged_tokens
      |> Enum.map(&Token.from_toxic/1)
      |> filter_eol_tokens()

    # Append EOF based on last token position
    {end_line, end_column} = last_position(tokens)
    tokens ++ [Token.eof(end_line, end_column)]
  end

  # Filter out EOL tokens (same as current lexer behavior)
  defp filter_eol_tokens(tokens) do
    Enum.reject(tokens, fn token -> token.kind == :eol end)
  end

  defp last_position([]) do
    {1, 1}
  end

  defp last_position(tokens) do
    case List.last(tokens) do
      %Token{end_line: line, end_column: column} -> {line, column}
      _ -> {1, 1}
    end
  end
end
