# Problem Format Specification

This document specifies the JSON format for quantifier-free real polynomial constraints.

## Top-Level Structure

```json
{
  "vars": [ ... ],
  "formula": { ... },
  "config": { "precision": 0.001 }
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `vars` | array | Yes | Variable declarations with bounds |
| `formula` | object | Yes | The constraint formula |
| `config` | object | No | Solver configuration |

## Variable Declarations

Each variable has a name and bounds:

```json
{
  "vars": [
    { "name": "x", "lo": 0.0, "hi": 1.0 },
    { "name": "y", "lo": -10.0, "hi": 10.0 }
  ]
}
```

| Field | Type | Description |
|-------|------|-------------|
| `name` | string | Variable identifier (alphanumeric) |
| `lo` | number | Lower bound (inclusive) |
| `hi` | number | Upper bound (inclusive) |

Constraint: `lo <= hi`

## Expression Nodes

Expressions are polynomial terms over variables and constants.

### Variable Reference

```json
{ "kind": "var", "name": "x" }
```

### Constant

```json
{ "kind": "const", "value": 3.14159 }
```

### Addition

```json
{
  "kind": "add",
  "children": [
    { "kind": "var", "name": "x" },
    { "kind": "const", "value": 1.0 }
  ]
}
```

Represents: `x + 1`

### Multiplication

```json
{
  "kind": "mul",
  "children": [
    { "kind": "const", "value": 2.0 },
    { "kind": "var", "name": "x" },
    { "kind": "var", "name": "y" }
  ]
}
```

Represents: `2 * x * y`

### Negation

```json
{
  "kind": "neg",
  "child": { "kind": "var", "name": "x" }
}
```

Represents: `-x`

### Power

```json
{
  "kind": "pow",
  "base": { "kind": "var", "name": "x" },
  "exp": 2
}
```

Represents: `x^2`

Constraint: `exp` must be a nonnegative integer.

## Formula Nodes

Formulas combine comparisons with logical connectives.

### Comparison

```json
{
  "kind": "cmp",
  "op": "<=",
  "lhs": { ... expression ... },
  "rhs": { ... expression ... }
}
```

Operators:
- `"<"` - strictly less than
- `"<="` - less than or equal
- `"="` or `"=="` - equal
- `">="` - greater than or equal
- `">"` - strictly greater than

### Conjunction (AND)

```json
{
  "kind": "and",
  "children": [
    { ... formula 1 ... },
    { ... formula 2 ... }
  ]
}
```

Empty children array is equivalent to `true`.

### Disjunction (OR)

```json
{
  "kind": "or",
  "children": [
    { ... formula 1 ... },
    { ... formula 2 ... }
  ]
}
```

Empty children array is equivalent to `false`.

### Negation (NOT)

```json
{
  "kind": "not",
  "child": { ... formula ... }
}
```

## Configuration

Optional solver configuration:

```json
{
  "config": {
    "precision": 0.001
  }
}
```

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `precision` | number | 0.001 | dReal delta-satisfiability precision |

## Complete Example

Find a point inside the unit circle with positive coordinates:

```json
{
  "vars": [
    { "name": "x", "lo": 0.0, "hi": 1.0 },
    { "name": "y", "lo": 0.0, "hi": 1.0 }
  ],
  "formula": {
    "kind": "and",
    "children": [
      {
        "kind": "cmp",
        "op": "<=",
        "lhs": {
          "kind": "add",
          "children": [
            { "kind": "pow", "base": { "kind": "var", "name": "x" }, "exp": 2 },
            { "kind": "pow", "base": { "kind": "var", "name": "y" }, "exp": 2 }
          ]
        },
        "rhs": { "kind": "const", "value": 1.0 }
      },
      {
        "kind": "cmp",
        "op": ">",
        "lhs": { "kind": "var", "name": "x" },
        "rhs": { "kind": "const", "value": 0.0 }
      },
      {
        "kind": "cmp",
        "op": ">",
        "lhs": { "kind": "var", "name": "y" },
        "rhs": { "kind": "const", "value": 0.0 }
      }
    ]
  },
  "config": { "precision": 0.0001 }
}
```

This represents: `x^2 + y^2 <= 1 ∧ x > 0 ∧ y > 0` with `x, y ∈ [0, 1]`.
