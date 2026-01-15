defmodule Hurricane.Token do
  @moduledoc """
  Token struct representing a single token from the lexer.

  The `kind` field normalizes the various token types from :elixir_tokenizer
  into a simpler vocabulary for the parser.
  """

  defstruct [:kind, :value, :line, :column, :raw]

  @type t :: %__MODULE__{
          kind: atom(),
          value: any(),
          line: pos_integer(),
          column: pos_integer(),
          raw: any()
        }

  @doc """
  Create a token from raw :elixir_tokenizer output.
  """
  def from_raw(raw_token) do
    {kind, value, line, column} = extract_fields(raw_token)

    %__MODULE__{
      kind: kind,
      value: value,
      line: line,
      column: column,
      raw: raw_token
    }
  end

  # Extract normalized kind, value, line, and column from raw token
  defp extract_fields(raw) do
    case raw do
      # Sigil tokens: {:sigil, pos, sigil_name, content, modifiers, interpolation, delimiter}
      {:sigil, {line, column, _extra}, sigil_name, content, modifiers, _interpolation, delimiter} ->
        {:sigil, %{sigil_name: sigil_name, content: content, modifiers: modifiers, delimiter: delimiter}, line, column}

      # Heredoc tokens: {:bin_heredoc, pos, indent, content} or {:list_heredoc, pos, indent, content}
      {:bin_heredoc, {line, column, _extra}, _indent, content} ->
        {:heredoc, join_chardata(content), line, column}

      {:list_heredoc, {line, column, _extra}, _indent, content} ->
        {:charlist_heredoc, content, line, column}

      # Atoms with interpolation: {:atom_unsafe, pos, parts}
      {:atom_unsafe, {line, column, _extra}, parts} ->
        {:atom_unsafe, parts, line, column}

      # Two-element tokens (keywords, punctuation)
      {type, {line, column, _extra}} ->
        {normalize_kind(type, nil), nil, line, column}

      # Three-element tokens (identifiers, literals, operators)
      {type, {line, column, _extra}, value} ->
        {normalize_kind(type, value), normalize_value(type, value), line, column}
    end
  end

  # Join chardata list into a single binary
  defp join_chardata(parts) when is_list(parts) do
    parts
    |> Enum.map(fn
      part when is_binary(part) -> part
      part when is_list(part) -> IO.chardata_to_string(part)
    end)
    |> Enum.join()
  end

  # Normalize token types to simpler kinds for the parser
  defp normalize_kind(type, value) do
    case type do
      # Identifiers - preserve whitespace-sensitive subtypes from tokenizer
      # BUT check if the value is a keyword first (e.g., `cond do` makes cond a do_identifier)
      :identifier -> normalize_identifier(value)
      :paren_identifier -> normalize_paren_identifier(value)
      :do_identifier -> normalize_do_identifier(value)
      :bracket_identifier -> normalize_bracket_identifier(value)
      :block_identifier -> normalize_block_identifier(value)
      :kw_identifier -> :kw_identifier
      :alias -> :alias
      # Anonymous function call: fun.(args)
      :dot_call_op -> :dot_call
      # Literals
      :int -> :integer
      :flt -> :float
      :char -> :char
      :atom -> :atom
      :atom_quoted -> :atom
      :bin_string -> :string
      :list_string -> :charlist
      :bin_heredoc -> :heredoc
      :list_heredoc -> :charlist_heredoc
      # Operators - preserve the specific operator as the kind
      :match_op -> value
      :or_op -> value
      :and_op -> value
      :concat_op -> value
      :arrow_op -> value
      :dual_op -> value
      :mult_op -> value
      :power_op -> value
      :two_op -> value
      :comp_op -> value
      :rel_op -> value
      :in_op -> value
      :in_match_op -> value
      :xor_op -> value
      :ternary_op -> value
      :type_op -> value
      :pipe_op -> value
      :assoc_op -> value
      :capture_op -> value
      :unary_op -> value
      :at_op -> :@
      :range_op -> value
      :stab_op -> :->
      :when_op -> :when
      # Punctuation - use as-is
      :"(" -> :lparen
      :")" -> :rparen
      :"[" -> :lbracket
      :"]" -> :rbracket
      :"{" -> :lbrace
      :"}" -> :rbrace
      :"<<" -> :langle
      :">>" -> :rangle
      :"," -> :comma
      :. -> :dot
      :%{} -> :map_open
      :% -> :percent
      # Keywords
      :do -> :do
      :end -> :end
      :fn -> :fn
      true -> true
      false -> false
      nil -> nil
      # Special
      :eol -> :eol
      :eof -> :eof
      :";" -> :semicolon
      # Pass through anything else
      other -> other
    end
  end

  # Normalize identifier to check for keywords
  defp normalize_identifier(value) when is_atom(value) do
    case value do
      :def -> :def
      :defp -> :defp
      :defmacro -> :defmacro
      :defmacrop -> :defmacrop
      :defmodule -> :defmodule
      :defstruct -> :defstruct
      :defprotocol -> :defprotocol
      :defimpl -> :defimpl
      :defdelegate -> :defdelegate
      :defguard -> :defguard
      :defguardp -> :defguardp
      :defexception -> :defexception
      :defoverridable -> :defoverridable
      :case -> :case
      :cond -> :cond
      :if -> :if
      :unless -> :unless
      :with -> :with
      :for -> :for
      :try -> :try
      :receive -> :receive
      :raise -> :raise
      :reraise -> :reraise
      :throw -> :throw
      :quote -> :quote
      :unquote -> :unquote
      :unquote_splicing -> :unquote_splicing
      :import -> :import
      :alias -> :alias_directive
      :require -> :require
      :use -> :use
      :when -> :when
      :and -> :and
      :or -> :or
      :not -> :not
      :in -> :in
      :rescue -> :rescue
      :catch -> :catch
      :else -> :else
      :after -> :after
      :do -> :do
      :end -> :end
      _ -> :identifier
    end
  end

  defp normalize_identifier(_), do: :identifier

  # Normalize paren_identifier - preserve unless it's a keyword
  # e.g., `if(x)` - `if` should be :if, not :paren_identifier
  defp normalize_paren_identifier(value) when is_atom(value) do
    case normalize_identifier(value) do
      :identifier -> :paren_identifier
      keyword -> keyword
    end
  end

  defp normalize_paren_identifier(_), do: :paren_identifier

  # Normalize do_identifier - preserve unless it's a keyword
  # e.g., `cond do` - `cond` should be :cond, not :do_identifier
  defp normalize_do_identifier(value) when is_atom(value) do
    case normalize_identifier(value) do
      :identifier -> :do_identifier
      keyword -> keyword
    end
  end

  defp normalize_do_identifier(_), do: :do_identifier

  # Normalize bracket_identifier - preserve unless it's a keyword
  defp normalize_bracket_identifier(value) when is_atom(value) do
    case normalize_identifier(value) do
      :identifier -> :bracket_identifier
      keyword -> keyword
    end
  end

  defp normalize_bracket_identifier(_), do: :bracket_identifier

  # Block identifiers are special keywords in block contexts
  defp normalize_block_identifier(value) when is_atom(value) do
    case value do
      :rescue -> :rescue
      :catch -> :catch
      :else -> :else
      :after -> :after
      _ -> :identifier
    end
  end

  defp normalize_block_identifier(_), do: :identifier

  # Normalize the value based on token type
  defp normalize_value(type, value) do
    case type do
      :identifier -> value
      :paren_identifier -> value
      :do_identifier -> value
      :bracket_identifier -> value
      :kw_identifier -> value
      :alias -> value
      :int -> parse_integer(value)
      :flt -> parse_float(value)
      :char -> value
      :atom -> value
      :bin_string -> value
      :list_string -> value
      :bin_heredoc -> value
      :list_heredoc -> value
      _ when is_atom(value) -> value
      _ -> value
    end
  end

  defp parse_integer(charlist) when is_list(charlist) do
    charlist |> List.to_string() |> String.replace("_", "") |> String.to_integer()
  end

  defp parse_integer(value), do: value

  defp parse_float(charlist) when is_list(charlist) do
    charlist |> List.to_string() |> String.replace("_", "") |> String.to_float()
  end

  defp parse_float(value), do: value

  @doc """
  Create an EOF token at the given position.
  """
  def eof(line, column) do
    %__MODULE__{
      kind: :eof,
      value: nil,
      line: line,
      column: column,
      raw: nil
    }
  end
end
