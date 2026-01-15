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
| (5, 4) | `\\` | Right | Default argument |
| (9, 8) | `\|` | Right | List cons, pattern |
| (11, 10) | `when` | Right | Guard clause |
| (13, 12) | `::` | Right | Type annotation |
| (17, 16) | `<-` | Right | Comprehension, with |
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
| (35, 34) | `++`, `--`, `+++`, `---`, `<>` | Right | Concat (right!) |
| (37, 38) | `..`, `..//` | Right | Range |

### Arithmetic

| BP (L, R) | Operators | Assoc | Notes |
|-----------|-----------|-------|-------|
| (39, 40) | `+`, `-` | Left | Add/subtract |
| (41, 42) | `*`, `/` | Left | Multiply/divide |

### High Precedence

| BP (L, R) | Operators | Assoc | Notes |
|-----------|-----------|-------|-------|
| (43, 44) | `**` | Left | Power |
| (53, -) | `-`, `+` (prefix) | - | Unary plus/minus |
| (55, -) | `!`, `not`, `^^^` (prefix) | - | Unary not |
| (57, -) | `^` | - | Pin operator |
| (59, -) | `&` | - | Capture operator |
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
| `&` | 59 | Capture |
| `^` | 57 | Pin |
| `!` | 55 | Boolean not |
| `not` | 55 | Boolean not |
| `~~~` | 55 | Bitwise not |
| `+` | 53 | Unary plus |
| `-` | 53 | Unary minus |

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

1. **Concat operators** (`++`, `--`, `<>`) are right-associative despite being
   at the same conceptual level as arithmetic.

2. **Pipe** (`|>`) is left-associative, allowing natural chaining:
   `a |> b |> c` = `((a |> b) |> c)`

3. **Match** (`=`) is right-associative for pattern matching:
   `{a, b} = x = get_tuple()` binds correctly

4. **When** binds very loosely so guards can contain complex expressions:
   `def foo(x) when x > 0 and x < 100, do: x`

5. **Unary minus** must be higher than binary minus:
   `-a + b` = `((-a) + b)`, not `-(a + b)`
