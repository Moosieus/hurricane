# Elixir Operator Precedence Table

Extracted from Spitfire and Elixir documentation. This is the authoritative
reference for Hurricane's Pratt parser.

## Binding Power Convention

- Higher number = binds tighter
- Left-associative: right BP = left BP + 1
- Right-associative: left BP = right BP + 1
- Increment by 2 between precedence levels

## Complete Precedence Table

Listed from **lowest** to **highest** precedence.

### Lowest Precedence

| BP (L, R) | Operators | Assoc | Notes |
|-----------|-----------|-------|-------|
| (4, 5) | `\\` | Left | Default argument (per Elixir official docs) |
| (9, 8) | `\|` | Right | List cons, pattern |
| (11, 10) | `when` | Right | Guard clause |
| (13, 12) | `::` | Right | Type annotation |
| (16, 17) | `<-` | Left | Comprehension, with (per Elixir official docs) |
| (19, 18) | `=` | Right | Match operator |

### Logical Operators

| BP (L, R) | Operators | Assoc | Notes |
|-----------|-----------|-------|-------|
| (21, 22) | `\|\|`, `\|\|\|`, `or` | Left | Boolean or |
| (23, 24) | `&&`, `&&&`, `and` | Left | Boolean and |

### Comparison Operators

| BP (L, R) | Operators | Assoc | Notes |
|-----------|-----------|-------|-------|
| (25, 26) | `==`, `!=`, `=~`, `===`, `!==` | Left | Equality |
| (27, 28) | `<`, `>`, `<=`, `>=` | Left | Relational |

### Other Infix

| BP (L, R) | Operators | Assoc | Notes |
|-----------|-----------|-------|-------|
| (29, 30) | `\|>` | Left | Pipe |
| (31, 32) | `in`, `not in` | Left | Membership |
| (33, 34) | `^^^` | Left | Bitwise xor |
| (35, 34) | `++`, `--`, `+++`, `---`, `<>`, `..`, `..//` | Right | Concat & range (same tier per Elixir docs) |

### Arithmetic

| BP (L, R) | Operators | Assoc | Notes |
|-----------|-----------|-------|-------|
| (39, 40) | `+`, `-` | Left | Add/subtract |
| (41, 42) | `*`, `/` | Left | Multiply/divide |

### High Precedence

| BP (L, R) | Operators | Assoc | Notes |
|-----------|-----------|-------|-------|
| (43, 44) | `**` | Left | Power |
| (30, -) | `!`, `not` (prefix) | - | Unary not (low BP so `!a in b` = `!(a in b)`) |
| (53, -) | `-`, `+` (prefix) | - | Unary plus/minus |
| (55, -) | `~~~` (prefix) | - | Bitwise not |
| (57, -) | `^` | - | Pin operator |
| (1, -) | `&` | - | Capture (very low so `&Enum.map/2` captures all) |
| (61, 62) | `.` | Left | Dot access |
| (63, -) | `@` | - | Module attribute |

### Postfix (Call-like)

| BP | Construct | Notes |
|----|-----------|-------|
| 60 | `foo(...)` | Function call |
| 60 | `expr[...]` | Bracket access |
| 62 | `expr.field` | Dot access |

## Prefix Operators

| Operator | BP | Notes |
|----------|-----|-------|
| `@` | 63 | Module attribute |
| `^` | 57 | Pin |
| `~~~` | 55 | Bitwise not |
| `+` | 53 | Unary plus |
| `-` | 53 | Unary minus |
| `!` | 30 | Boolean not (intentionally low for `!(a in b)` behavior) |
| `not` | 30 | Boolean not (intentionally low for `not(a in b)` behavior) |
| `&` | 1 | Capture (intentionally very low to capture entire expression) |

## Special Cases

### Stab Operator `->`

Used in:
- `fn` bodies: `fn x -> x + 1 end`
- `case` clauses: `case x do :a -> 1 end`
- `cond` clauses: `cond do true -> 1 end`
- Keyword blocks: `foo do x -> x end`

BP: Very low (6, 5) — binds loosely to allow full expressions on each side.

### Comma `,`

Context-dependent:
- In lists/tuples/maps: separator, not operator
- In top-level: allows `foo a, b` (no parens call)
- In stab RHS: allows `-> a, b, c`

BP varies by context (8-14).

### Do Keyword

Not an operator but affects parsing:
- Starts a block: `def foo do ... end`
- Can appear after expressions: `foo do ... end`
- Affects when infix loop terminates

## Associativity Examples

### Left-Associative (default)

```elixir
# a + b + c parses as:
{:+, [], [{:+, [], [a, b]}, c]}
# ((a + b) + c)
```

### Right-Associative

```elixir
# a ++ b ++ c parses as:
{:++, [], [a, {:++, [], [b, c]}]}
# (a ++ (b ++ c))

# a = b = c parses as:
{:=, [], [a, {:=, [], [b, c]}]}
# (a = (b = c))
```

## Implementation Notes

1. **Concat and range operators** (`++`, `--`, `<>`, `..`, `..//`) are all at the
   same precedence tier (right-associative) per official Elixir documentation.

2. **Pipe** (`|>`) is left-associative, allowing natural chaining:
   `a |> b |> c` = `((a |> b) |> c)`

3. **Match** (`=`) is right-associative for pattern matching:
   `{a, b} = x = get_tuple()` binds correctly

4. **When** binds very loosely so guards can contain complex expressions:
   `def foo(x) when x > 0 and x < 100, do: x`

5. **Unary minus** must be higher than binary minus:
   `-a + b` = `((-a) + b)`, not `-(a + b)`

6. **`!` and `not`** have intentionally low BP (30) so that `!a in b` parses as
   `!(a in b)`, matching Elixir's actual behavior. This differs from the BP that
   would be expected from the precedence table position, but is verified correct.

7. **`&` capture** has BP 1 (very low) so `&Enum.map/2` captures the entire
   expression, matching Elixir's actual behavior.

8. **`<-` and `\\`** are left-associative per official Elixir documentation,
   despite appearing in a list of "lowest precedence" operators that are mostly
   right-associative.
