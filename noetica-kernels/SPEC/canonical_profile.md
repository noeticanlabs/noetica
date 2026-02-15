# Canonical Profile Specification

This document defines the canonical encoding profile for Noetica kernel operations.
All golden vectors MUST follow these rules to ensure deterministic replay.

---

## Version

- **ACTION_ALGEBRA_VERSION**: 1.0
- **RECEIPT_SCHEMA_VERSION**: 1.0

---

## JSON Canonicalization

All JSON used for hashing MUST be canonicalized with the following rules:

### 1. Key Ordering
- **Rule**: Object keys MUST be sorted lexicographically (alphabetically)
- **Implementation**: `json.dumps(..., sort_keys=True)`

### 2. Whitespace
- **Rule**: No unnecessary whitespace
- **Implementation**: Use compact separators `(",", ":")`
- **Example**: `{"a":1,"b":2}` not `{"a": 1, "b": 2}`

### 3. Encoding
- **Rule**: UTF-8 without BOM
- **Implementation**: `.encode("utf-8")`

### 4. Numeric Encoding

#### Integers
- **Rule**: No leading zeros
- **Valid**: `5`, `-12`
- **Invalid**: `05`, `+5`

#### Floats
- **Rule**: Use decimal strings with fixed precision OR canonical rational encoding
- **Policy**: 17 significant digits (IEEE 754 double precision)
- **No trailing zeros**: `1.5` not `1.500`
- **Lowercase exponent**: `1e10` not `1E10`
- **Implementation**: Round to 17 significant digits, strip trailing zeros

#### Special Values
- **Rule**: No NaN or Infinity values in canonical form

### 5. Booleans
- **Rule**: Lowercase only
- **Valid**: `true`, `false`
- **Invalid**: `True`, `FALSE`

### 6. Null
- **Rule**: Use `null` (lowercase)
- **Invalid**: `None`, `NULL`, `""`

### 7. Strings
- **Rule**: UTF-8 only
- **Escape handling**: Use JSON standard escapes (`\n`, `\t`, `\\`, etc.)

---

## Hash Function

- **Algorithm**: SHA-256
- **Output**: 64-character lowercase hex string

### Hash Computation

```python
def compute_hash(obj):
    canonical_bytes = canonical_json(obj)
    return sha256(canonical_bytes).hexdigest()
```

---

## Receipt Chain Canonicalization

Each receipt MUST be canonicalized before hashing:

1. Remove the `receipt_hash` field
2. Sort all remaining keys lexicographically
3. Serialize with compact JSON
4. Compute SHA-256

### Genesis Block

- `prev` = `"GENESIS"` (for first receipt)
- This is a constant string, not a hash

---

## State Hash Canonicalization

- State is represented as a JSON object
- Keys sorted alphabetically
- Compact serialization
- SHA-256 hash of canonical bytes

---

## Version Pinning

All golden vectors are pinned to specific versions:

```
ACTION_ALGEBRA_VERSION = "1.0"
RECEIPT_SCHEMA_VERSION = "1.0"
CANONICAL_PROFILE_VERSION = "1.0"
```

Future changes:
1. Bump version number
2. Create new golden vector folder (e.g., `action_v2/`)
3. Keep old vectors unchanged for backward compatibility

---

## Compliance

Implementations that produce golden vectors MUST:
- Follow all rules in this document
- Be reproducible across Python versions (use `json` module)
- Pass hash verification

---

## Reference Implementation

```python
import json
import hashlib

def canonical_json(obj: Any) -> bytes:
    """Canonicalize JSON object for deterministic hashing."""
    return json.dumps(
        obj,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False
    ).encode("utf-8")

def compute_hash(obj: Any) -> str:
    """Compute SHA-256 hash of canonical JSON."""
    return hashlib.sha256(canonical_json(obj)).hexdigest()

def canonical_float(f: float) -> str:
    """Canonicalize float to 17 significant digits."""
    s = f"{f:.17g}"
    if "." in s and "e" not in s.lower():
        s = s.rstrip("0").rstrip(".")
    return s
```
