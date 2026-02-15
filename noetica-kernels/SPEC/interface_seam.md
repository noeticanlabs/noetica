# Interface Seam Specification

## Overview

This document defines the interfaces between the three kernels:

- **Noetica** (Semantic Language Kernel)
- **NSC** (Deterministic Governed Execution Substrate)
- **Coherence** (Certified Debt Governance)

---

## Noetica → NSC Interface

### Action Stream

Noetica emits actions that NSC executes:

```json
{
  "action": {
    "type": "WRITE|CALL|ASSERT|REPAIR|SOLVE|MEASURE",
    ...
  }
}
```

### Semantic State Serialization

Noetica provides canonicalizable state serialization:

```json
{
  "semantic_state": {
    "format": "canonicalizable",
    "serialization": "..."
  }
}
```

### Registry Digest

Noetica provides a registry digest for replay lock:

```json
{
  "registry_digest": "sha256:..."
}
```

---

## NSC → Noetica Interface

### Execution Results

NSC returns execution results to Noetica:

```json
{
  "result": {
    "state": "...",
    "actions_emitted": [...],
    "governance_failures": [...]
  }
}
```

### Governance Failures

When NSC rejects steps due to governance:

```json
{
  "governance_failure": {
    "reason": "budget_exceeded|contract_violation|rail_violation",
    "policy_action": "abort|repair|rollback",
    "details": "..."
  }
}
```

---

## NSC → Coherence Interface

### Certification Request

NSC requests debt certification:

```json
{
  "cert_request": {
    "type": "debt_certification",
    "V_k": "invariant violations",
    "B_k": "budget",
    "residuals": [...],
    "timestamp": "ISO8601"
  }
}
```

---

## Coherence → NSC Interface

### Certification Response

Coherence returns certified debt:

```json
{
  "cert_response": {
    "D_k": "certified_debt_value",
    "proof_object": {
      "type": "lyapunov_bound|domination|drift",
      "proof": "..."
    },
    "timestamp": "ISO8601",
    "valid_until": "ISO8601"
  }
}
```

---

## Data Flow Summary

```
Noetica (Semantics)
    │
    │ glyphs → AST → IR → Actions
    ▼
NSC (Execution)
    │
    │ Execute actions + emit receipts
    │ ┌────────────────────────────┐
    │ ▼                          ▼
    │ Request cert          Governance check
    │                            │
    ▼                            ▼
Coherence                   Fail-closed
(Math)                     governance
    │
    │ Certified debt
    ▼
NSC (receipt)
```

---

## Versioning

All interfaces are versioned:

```json
{
  "interface_version": "1.0",
  "nsc_version": "1.0",
  "noetica_version": "1.0",
  "coherence_version": "1.0"
}
```

Breaking changes require version bump.

---

## Error Handling

| Error | Source | Response |
|-------|--------|----------|
| Invalid action format | Noetica → NSC | Reject with parse error |
| Governance failure | NSC | Apply policy (abort/repair/rollback) |
| Certification failure | Coherence → NSC | Treat as debt exceeded |
| Replay mismatch | NSC | Report failure with details |

---

## Normative References

- `nsc-kernel/SPEC/nsc_spec.md` - NSC execution semantics
- `noetica-kernel/SPEC/noetica_spec.md` - Noetica semantics
- `coherence-kernel/SPEC/ck0_spec.md` - Coherence mathematics
