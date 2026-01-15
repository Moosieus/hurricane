# Hurricane Test Corpus

Test files for validating parser behavior.

## Directory Structure

```
test_corpus/
├── valid/          # Should match Code.string_to_quoted exactly
├── incomplete/     # Mid-edit states, should recover gracefully
├── malformed/      # Syntax errors, should not crash
└── adversarial/    # Worst-case inputs, should not hang
```

## Testing Strategy

### Valid Tests

For every file in `valid/`:
```elixir
code = File.read!(path)
{:ok, hurricane_ast} = Hurricane.parse(code)
{:ok, reference_ast} = Code.string_to_quoted(code, columns: true, token_metadata: true)
assert hurricane_ast == reference_ast
```

### Incomplete Tests

For files in `incomplete/`:
- Parser must return `{:ok, ast}` (not crash)
- AST should contain error nodes for broken parts
- Complete constructs after errors should be intact
- Check that function names/arities are recoverable

### Malformed Tests

For files in `malformed/`:
- Parser must return (not crash)
- Error nodes mark problem areas
- Subsequent valid code parses correctly

### Adversarial Tests

For files in `adversarial/`:
- Parser must return in bounded time (< 1 second)
- No stack overflow
- No infinite loops
- Advance assertions should catch stuck parser immediately

## Adding Tests

When adding new test cases:
1. Choose appropriate directory based on test type
2. Add comments explaining what the test validates
3. Include at least one valid construct after errors (for recovery testing)
4. For valid tests, verify with `Code.string_to_quoted` first
