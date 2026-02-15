# Action Algebra Specification

## Overview

This document defines the **Action Algebra** - the stable ABI (Application Binary Interface) between the Noetica kernel and the NSC kernel. All actions MUST conform to this specification.

**Version**: `action_algebra_version = 1.0`

---

## Action Schema

All actions are JSON objects that MUST validate against `../schemas/action.schema.json`.

### Action Types

| Type | Description | Required Fields |
|------|-------------|-----------------|
| `WRITE` | Write a value to a variable | `type`, `var`, `value` |
| `CALL` | Invoke an operation | `type`, `op_id`, `args` |
| `ASSERT` | Assert a predicate | `type`, `pred` |
| `REPAIR` | Request repair hint | `type`, `hint` |
| `SOLVE` | Solve a residual | `type`, `residual_id`, `params` |
| `MEASURE` | Compute a metric | `type`, `metric_id`, `params` |

---

## Canonicalization Rules

For deterministic action processing, all actions MUST be canonicalized before hashing or comparison.

### JSON Canonicalization

1. **Key Ordering**: Object keys MUST be sorted alphabetically
2. **No Whitespace**: Use compact encoding: `,` and `:` with no spaces
3. **UTF-8**: Encode as UTF-8 without BOM
4. **Number Encoding**:
   - Integers MUST NOT have trailing `.0`
   - Floats MUST use lowercase `e` (not `E`)
   - No unnecessary leading zeros
   - Special values (`NaN`, `Infinity`) are NOT permitted

### Example Canonicalization

```python
# Input (non-canonical):
{"type": "WRITE", "var": "x", "value": 42.0}

# Canonical form:
{"type":"WRITE","value":42,"var":"x"}
```

---

## Determinism Requirements

### No Hidden Randomness

- Actions MUST NOT contain timestamps (use sequence IDs instead)
- Actions MUST NOT contain random values
- Nonces MUST be derived from deterministic sources (e.g., step index)

### Nonce Rules

For action streams that require ordering:

- Each action in a sequence MUST have a monotonically increasing `step_id`
- The first action MUST have `step_id = 0`
- Nonce format: `"nonce": "step_<step_id>"`

---

## Error Model

All errors are categorized into the following codes:

| Error Code | Description | Category |
|------------|-------------|----------|
| `schema_error` | Action fails JSON schema validation | Input |
| `rail_violation` | Action violates rail constraints | Governance |
| `contract_violation` | Action violates L0/L1/L2 contract | Governance |
| `debt_overflow` | Debt exceeds budget threshold | Governance |
| `replay_mismatch` | Replay verification failed | Integrity |

---

## Versioning

### Schema Version

The action schema uses semantic versioning:

- **MAJOR**: Breaking changes (removed fields, new required fields)
- **MINOR**: Backward-compatible additions (new optional fields)
- **PATCH**: Bug fixes (clarifications that don't change behavior)

### Compatibility Notes

| Version | Compatible With |
|---------|-----------------|
| 1.0.0 | Initial release |
| 1.1.0 | Added `MEASURE` type |
| 2.0.0 | Incompatible - see migration guide |

---

## Golden Vectors

Canonical action streams for testing determinism are stored in:

- `nsc-kernel/test_vectors/tv_nsc_actions_*.jsonl`

Each line is a JSON object with:
- `action`: the canonical action
- `canonical_bytes`: expected SHA256 input

---

## Reference Implementation

```python
import json
import hashlib

def canonical_json(obj: dict) -> bytes:
    """Canonicalize a JSON object for deterministic hashing."""
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")

def action_hash(action: dict) -> str:
    """Compute SHA256 hex digest of canonical action."""
    return hashlib.sha256(canonical_json(action)).hexdigest()

# Example usage:
action = {"type": "WRITE", "var": "x", "value": 42}
print(action_hash(action))  # Deterministic output
```

---

## See Also

- [`../schemas/action.schema.json`](action.schema.json) - JSON Schema for actions
- [`interface_seam.md`](interface_seam.md) - Kernel interface specification
- [`kernel_contract.md`](kernel_contract.md) - Full kernel contract
