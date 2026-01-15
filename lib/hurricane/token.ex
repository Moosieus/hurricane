defmodule Hurricane.Token do
  @moduledoc """
  Token struct representing a single token from the lexer.

  Tokens include both start and end positions, enabling precise range queries
  like "is the cursor inside this string?". The positions come directly from
  Toxic's ranged token format.

  ## Fields

  - `kind` - Normalized token type (e.g., `:string`, `:identifier`, `:lparen`)
  - `value` - Token value (string content, atom name, integer value, etc.)
  - `line` - Start line (1-indexed)
  - `column` - Start column (1-indexed)
  - `end_line` - End line (1-indexed, inclusive)
  - `end_column` - End column (1-indexed, inclusive)
  - `raw` - Original Toxic token for debugging
  """

  defstruct [:kind, :value, :line, :column, :end_line, :end_column, :raw]

  @type t :: %__MODULE__{
          kind: atom(),
          value: any(),
          line: pos_integer(),
          column: pos_integer(),
          end_line: pos_integer(),
          end_column: pos_integer(),
          raw: any()
        }

  @doc """
  Create a token from Toxic's native ranged format.

  Toxic produces tokens in the format:
  - `{kind, {{start_l, start_c}, {end_l, end_c}, extra}, value}` (3-element)
  - `{kind, {{start_l, start_c}, {end_l, end_c}, extra}}` (2-element, punctuation)
  """
  def from_toxic(raw_token) do
    {kind, value, line, column, end_line, end_column} = extract_ranged_fields(raw_token)

    %__MODULE__{
      kind: kind,
      value: value,
      line: line,
      column: column,
      end_line: end_line,
      end_column: end_column,
      raw: raw_token
    }
  end

  # Extract fields from Toxic's ranged token format
  defp extract_ranged_fields(raw) do
    case raw do
      # Sigil tokens: {:sigil, pos, sigil_name, content, modifiers, indentation, delimiter}
      {:sigil, {{start_l, start_c}, {end_l, end_c}, _extra}, sigil_name, content, modifiers,
       indentation, delimiter} ->
        {:sigil,
         %{
           sigil_name: sigil_name,
           content: content,
           modifiers: modifiers,
           indentation: indentation,
           delimiter: delimiter
         }, start_l, start_c, end_l, end_c}

      # Heredoc tokens: {:bin_heredoc, pos, indent, content} or {:list_heredoc, pos, indent, content}
      {:bin_heredoc, {{start_l, start_c}, {end_l, end_c}, _extra}, indent, content} ->
        # Check for interpolation - if present, preserve structure
        value =
          if has_interpolation?(content) do
            content
          else
            join_chardata(content)
          end

        {:heredoc, %{indent: indent, content: value}, start_l, start_c, end_l, end_c}

      {:list_heredoc, {{start_l, start_c}, {end_l, end_c}, _extra}, indent, content} ->
        {:charlist_heredoc, %{indent: indent, content: content}, start_l, start_c, end_l, end_c}

      # Atoms with interpolation: {:atom_unsafe, pos, parts}
      {:atom_unsafe, {{start_l, start_c}, {end_l, end_c}, _extra}, parts} ->
        {:atom_unsafe, parts, start_l, start_c, end_l, end_c}

      # Safe quoted atoms (from Toxic): {:atom_safe, pos, parts}
      {:atom_safe, {{start_l, start_c}, {end_l, end_c}, _extra}, parts} ->
        {:atom_safe, parts, start_l, start_c, end_l, end_c}

      # Keyword identifiers with quotes (from Toxic)
      {:kw_identifier_safe, {{start_l, start_c}, {end_l, end_c}, _extra}, parts} ->
        {:kw_identifier, join_parts_to_atom(parts), start_l, start_c, end_l, end_c}

      {:kw_identifier_unsafe, {{start_l, start_c}, {end_l, end_c}, _extra}, parts} ->
        {:kw_identifier_unsafe, parts, start_l, start_c, end_l, end_c}

      # Error tokens from Toxic
      {:error_token, {{start_l, start_c}, {end_l, end_c}, _extra}, error} ->
        {:error_token, error, start_l, start_c, end_l, end_c}

      # Two-element tokens (keywords, punctuation) - value is nil
      {type, {{start_l, start_c}, {end_l, end_c}, _extra}, nil} ->
        {normalize_kind(type, nil), nil, start_l, start_c, end_l, end_c}

      # Two-element tokens without explicit nil (some punctuation)
      {type, {{start_l, start_c}, {end_l, end_c}, _extra}} ->
        {normalize_kind(type, nil), nil, start_l, start_c, end_l, end_c}

      # Three-element tokens with compound value (like `not in` operator)
      # Format: {:in_op, pos, {:"not in", end_pos}}
      {type, {{start_l, start_c}, {end_l, end_c}, _extra}, {value, _nested_pos}}
      when is_atom(value) ->
        {normalize_kind(type, value), value, start_l, start_c, end_l, end_c}

      # Standard three-element tokens (identifiers, literals, operators)
      {type, {{start_l, start_c}, {end_l, end_c}, _extra}, value} ->
        {normalize_kind(type, value), normalize_value(type, value), start_l, start_c, end_l,
         end_c}
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

  # Join string parts into an atom (for kw_identifier_safe)
  defp join_parts_to_atom(parts) when is_list(parts) do
    parts
    |> Enum.map(fn
      part when is_binary(part) -> part
      part when is_list(part) -> IO.chardata_to_string(part)
    end)
    |> Enum.join()
    |> String.to_atom()
  end

  defp join_parts_to_atom(atom) when is_atom(atom), do: atom

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
      :atom_safe -> :atom_safe
      :atom_unsafe -> :atom_unsafe
      :kw_identifier_unsafe -> :kw_identifier_unsafe
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
      :bin_string -> normalize_string(value)
      :list_string -> normalize_charlist(value)
      :bin_heredoc -> value
      :list_heredoc -> value
      _ when is_atom(value) -> value
      _ -> value
    end
  end

  # Normalize string value - join simple strings, preserve interpolation structure
  defp normalize_string(parts) when is_list(parts) do
    if has_interpolation?(parts) do
      # Preserve interpolation structure for parser to handle
      parts
    else
      # Simple string - join chardata
      join_chardata(parts)
    end
  end

  defp normalize_string(value), do: value

  # Normalize charlist value - convert string parts to actual charlist
  defp normalize_charlist(parts) when is_list(parts) do
    if has_interpolation?(parts) do
      # Preserve interpolation structure for parser to handle
      parts
    else
      # Simple charlist - join and convert to charlist
      parts
      |> join_chardata()
      |> String.to_charlist()
    end
  end

  defp normalize_charlist(value), do: value

  # Check if string parts contain interpolation tuples
  defp has_interpolation?(parts) when is_list(parts) do
    Enum.any?(parts, fn
      # Interpolation tuple with ranged positions
      {{_, _, _}, {_, _, _}, _tokens} -> true
      _ -> false
    end)
  end

  defp parse_integer(charlist) when is_list(charlist) do
    str = charlist |> List.to_string() |> String.replace("_", "")

    case str do
      "0b" <> rest -> String.to_integer(rest, 2)
      "0B" <> rest -> String.to_integer(rest, 2)
      "0o" <> rest -> String.to_integer(rest, 8)
      "0O" <> rest -> String.to_integer(rest, 8)
      "0x" <> rest -> String.to_integer(rest, 16)
      "0X" <> rest -> String.to_integer(rest, 16)
      _ -> String.to_integer(str)
    end
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
      end_line: line,
      end_column: column,
      raw: nil
    }
  end

  @doc """
  Check if a position (line, column) falls within this token's range.
  """
  def contains?(%__MODULE__{} = token, line, column) do
    cond do
      line < token.line -> false
      line > token.end_line -> false
      line == token.line and column < token.column -> false
      line == token.end_line and column > token.end_column -> false
      true -> true
    end
  end

  @doc """
  Get the range of this token as a tuple: `{start_line, start_col, end_line, end_col}`.
  """
  def range(%__MODULE__{} = token) do
    {token.line, token.column, token.end_line, token.end_column}
  end
end
