# NSC Receipts Specification

## Overview

This document specifies the receipt chain format for the NSC (Deterministic Governed Execution Substrate). Receipts provide tamper-evident audit trails for all execution steps.

---

## Receipt Structure

```json
{
  "receipt_id": "R_k",
  "prev": "H(R_{k-1})",
  "curr": "H(contents)",
  "step_index": k,
  "timestamp": "ISO8601",
  "action": { ... },
  "state_delta": { ... },
  "governance": {
    "budget": "B_k",
    "debt": "D_k",
    "rail_mode": "reject|project",
    "contract_level": "L0|L1|L2"
  },
  "canonical_state": "bytes"
}
```

---

## Hash Chain

Each receipt R_k satisfies:

- `R_k.prev = R_{k-1}.curr` (hash linkage)
- `R_k.curr = H(canonical(R_k excluding curr))` (self-contained hash)

### Genesis

- `R_0.prev = GENESIS` (constant)
- `R_0.curr = H(canonical(R_0 excluding curr))`

---

## Canonicalization

Receipt canonicalization (`canon`) must be:

1. **Deterministic**: Same input → same bytes
2. **Schema-stable**: Field order fixed
3. **Key-sorted**: Object keys sorted alphabetically
4. **Numeric-canonical**: Numbers in consistent format (no trailing zeros)

---

## Receipt Contents

### Required Fields

| Field | Type | Description |
|-------|------|-------------|
| `receipt_id` | string | Unique identifier (format: `R_{step_index}`) |
| `prev` | hash | Previous receipt hash |
| `curr` | hash | Self-hash of this receipt |
| `step_index` | integer | Step number in execution |
| `timestamp` | string | ISO 8601 timestamp |
| `action` | object | Executed action |
| `canonical_state` | bytes | Canonicalized state snapshot |

### Governance Fields

| Field | Type | Description |
|-------|------|-------------|
| `budget` | object | Budget allocation |
| `debt` | object | Current debt state |
| `rail_mode` | string | Rail enforcement mode |
| `contract_level` | string | Active contract level |

---

## Verification

### Hash Verification

```
verify_hash(R):
  computed = H(canonical(R excluding curr))
  return computed == R.curr
```

### Chain Verification

```
verify_chain(R_0, ..., R_n):
  for k in 1..n:
    if R_k.prev != R_{k-1}.curr:
      return False
    if not verify_hash(R_k):
      return False
  return True
```

---

## Replay Integration

Receipts are used for replay verification:

- Full state reconstruction from genesis + action stream
- Hash chain equality check: `R_k.replay.curr == R_k.orig.curr` ∀k
- Deterministic state transition verification

---

## Schema

See `nsc-kernel/schemas/nsc_receipt.schema.json` for JSON Schema definition.
