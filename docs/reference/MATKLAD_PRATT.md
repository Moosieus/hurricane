# Pratt Parsing: Distilled

Source: https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html

## Core Idea

Pratt parsing handles operator precedence and associativity using **binding power**
instead of grammar transformations. It's an enhancement of recursive descent that
elegantly handles expressions.

## The Problem

Traditional approach encodes precedence in grammar:
```
Expr   = Factor | Expr '+' Factor
Factor = Atom | Factor '*' Atom
```

This is awkward, especially with many precedence levels. Elixir has 27.

## The Solution: Binding Power

Instead of "high/low precedence," think of operators **binding** to operands.
In `A + B * C`, the `*` binds tighter, producing `A + (B * C)`.

### For Associativity

Use **asymmetric** binding powers:
- Left-associative `+`: right side binds tighter
  - `A + B + C` → `(A + B) + C`
  - Left BP = 1, Right BP = 2
- Right-associative `=`: left side binds tighter
  - `A = B = C` → `A = (B = C)`
  - Left BP = 2, Right BP = 1

## The Algorithm (40 lines)

```
function expr(min_bp):
    lhs = parse_atom_or_prefix()

    while true:
        op = peek()
        (left_bp, right_bp) = binding_power(op)

        if left_bp < min_bp:
            break

        advance()  # consume operator
        rhs = expr(right_bp)
        lhs = make_binop(op, lhs, rhs)

    return lhs
```

The `min_bp` parameter is the binding power to beat. Operators with lower left BP
than `min_bp` belong to an outer expression.

## Extending the Algorithm

### Prefix Operators (!, -, not)

Only have right binding power:
```elixir
def prefix_bp(:!) do 55 end
def prefix_bp(:not) do 55 end
def prefix_bp(:-) do 53 end  # unary minus
```

Handle in `parse_atom_or_prefix`:
```
if is_prefix(current()):
    op = advance()
    rhs = expr(prefix_bp(op))
    return make_unary(op, rhs)
```

### Postfix Operators (function call, bracket access)

Only have left binding power. Check after infix loop:
```
# After checking infix operators:
if current() == '(' and min_bp < call_bp:
    args = parse_args()
    lhs = make_call(lhs, args)
    continue
```

### Parentheses

Handle at atom level:
```
if current() == '(':
    advance()  # consume (
    inner = expr(0)  # reset binding power
    expect(')')
    return inner
```

### Indexing: `a[i]`

Treat as postfix with delimited content:
```
if current() == '[':
    advance()
    index = expr(0)
    expect(']')
    lhs = make_index(lhs, index)
```

### Ternary: `c ? t : f`

Parse `:` as part of `?` operator:
```
if op == '?':
    advance()
    then_branch = expr(0)
    expect(':')
    else_branch = expr(right_bp)
    lhs = make_ternary(lhs, then_branch, else_branch)
```

## Binding Power Assignment Strategy

Use **odd numbers** as base values: 1, 3, 5, 7, 9...

For left-associative binary operators, right BP = left BP + 1:
```elixir
:+  => {47, 48}  # left-assoc
:*  => {49, 50}  # left-assoc, higher precedence
```

For right-associative operators, left BP = right BP + 1:
```elixir
:=  => {27, 26}  # right-assoc
:++ => {45, 44}  # right-assoc
```

Reserve 0 for "no binding" (end of expression).

## When to Use Pratt

**Perfect for:**
- Expressions with operators
- Mixed associativity
- Many precedence levels
- Hand-written parsers

**Not for:**
- Top-level structure (use recursive descent)
- Statements and declarations
- Block constructs (do/end, case, etc.)

## Key Insight for Hurricane

Pratt parsing is the **expression layer**. Structure (defmodule, def, do/end) should
use recursive descent with recovery sets. Pratt handles `1 + 2 * 3`, not
`def foo(x) do ... end`.
