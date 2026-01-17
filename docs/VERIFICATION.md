# Verification Guide

This document explains how the SemiAlgebraic library verifies constraint satisfaction and unsatisfiability.

## Certificate Structure

A certificate (`cert_<sha256>.json`) contains:

```json
{
  "version": 1,
  "problem_sha256": "<64-char hex hash>",
  "problem": { ... },
  "problem_path": "/path/to/original/problem.json",
  "backend": "dreal4",
  "docker_image": "dreal/dreal4:latest",
  "result": { "status": "sat|unsat|error", "model": {...} },
  "witness": { "env": {...}, "eps": 0.001 },
  "unsat_cert": { ... },
  "unsat_interval_cert": { ... },
  "certified": true|false,
  "check_msg": "description"
}
```

## Hash Verification

The `problem_sha256` field ensures certificate integrity:

1. **Canonicalization**: The problem JSON is processed with RFC 8785 JCS
   - Object keys sorted by UTF-16 code unit order
   - Minimal escaping for strings
   - Deterministic number formatting

2. **Hashing**: SHA-256 is computed over the canonical string
   - Pure Lean implementation (no external dependencies)
   - 32-byte digest encoded as lowercase hex

3. **Verification**: `cad_verify` recomputes and compares hashes

## SAT Witness Verification

For SAT results, the certificate includes a witness:

```json
{
  "witness": {
    "env": { "x": 0.5, "y": 0.25 },
    "eps": 0.001
  }
}
```

### Float Mode (Default)

Verification steps:
1. Parse witness values as `Float`
2. Check each variable is within declared bounds
3. Evaluate the formula with epsilon tolerance
4. Report pass/fail

Epsilon tolerance handles floating-point imprecision for comparisons like `x <= y + eps`.

### Exact Mode (`--exact`)

For higher assurance, exact mode uses rational arithmetic:

```bash
lake exe cad_verify --cert cert.json --exact
```

Requirements:
- Witness values must be parseable as rationals
- Format: `"1/2"` or `{"num": 1, "den": 2}`
- No epsilon tolerance; exact arithmetic throughout

## UNSAT Certification

Two methods for certifying unsatisfiability:

### 1. Restricted Patterns (`unsat_cert`)

Fast detection of simple contradictions:

- **Bounds Contradiction**: Variable bound conflicts (e.g., `x > 5` with `x ∈ [0,1]`)
- **Nonneg-Le-Neg**: Nonnegative expression required less than negative constant
- **Nonpos-Ge-Pos**: Nonpositive expression required greater than positive constant

Example certificate:
```json
{
  "unsat_cert": {
    "kind": "bounds_contradiction",
    "var": "x",
    "var_lo": 0.0,
    "var_hi": 1.0,
    "required_lo": 5.0
  }
}
```

### 2. Interval Partition (`unsat_interval_cert`)

For more complex cases, interval arithmetic with partitioning:

```json
{
  "unsat_interval_cert": {
    "kind": "interval_tree",
    "max_depth": 10,
    "tree": { ... recursive structure ... }
  }
}
```

The tree partitions the variable domain and proves UNSAT in each region using tri-valued logic:
- `tt`: definitely true
- `ff`: definitely false
- `unknown`: inconclusive (requires further partitioning)

## Verification Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Certificate verified successfully |
| 1 | Command-line usage error |
| 2 | Hash mismatch or file error |
| 3 | Witness verification failed |
| 4 | No witness present (UNSAT not certified) |

## Example Workflow

```bash
# Generate certificate
lake exe cad_certify --in problem.json --out cert.json

# Verify with float mode
lake exe cad_verify --cert cert.json

# Verify with exact mode
lake exe cad_verify --cert cert.json --exact

# Check specific solver backend
lake exe cad_certify --in problem.json --backend z3 --out cert_z3.json
```

## Security Considerations

- Certificates are not cryptographically signed
- Hash verification prevents accidental corruption
- For high-assurance applications, extend with digital signatures
- Docker execution provides solver isolation
