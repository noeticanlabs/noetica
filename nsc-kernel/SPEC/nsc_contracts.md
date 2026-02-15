# NSC Contracts Specification

## Overview

This document specifies the contract system for NSC execution governance. Contracts define admissibility criteria for program execution.

---

## Contract Levels

### L0: Budget-Only Contract

Minimal governance:

```
ExecContract_L0 = < level: "L0", B: Budget, upd: DebtUpdateFn >
```

Admissibility:
```
A_L0(Σ) = [D <= B]
```

### L1: Predicate Preservation Contract

Predicate-based invariants:

```
ExecContract_L1 = < level: "L1", B: Budget, P: Predicate, cert: Certificate >
```

Admissibility:
```
A_L1(Σ) = [D <= B] ∧ [P(Σ) = true]
```

Certificate proves predicate preservation under budget constraints.

### L2: Lyapunov Stability Contract

Full coherence certification:

```
ExecContract_L2 = < level: "L2", B: Budget, V: LyapunovFn, D_max: DebtBound >
```

Admissibility:
```
A_L2(Σ) = [D <= B] ∧ [V(Σ) <= D_max] ∧ drift_inequality_holds
```

Certificate includes:
- Lyapunov function value
- Dominance relation
- Drift inequality proof

---

## Contract Declaration

Programs declare contracts via metadata:

```json
{
  "contract": {
    "level": "L1",
    "budget": { "steps": 1000, "energy": 1.0 },
    "predicate": "invariant_maintained",
    "cert": { ... }
  }
}
```

---

## Admissibility Check

### Function: check_admissibility

```
check_admissibility(Σ, contract) → (bool, policy_action)
```

1. Evaluate debt D from Σ.governance
2. Compare against budget B
3. If L1: verify predicate P holds
4. If L2: verify Lyapunov conditions
5. If all pass: return (true, proceed)
6. If fails: return (false, policy_action)

### Policy Actions

| Policy | Action |
|--------|--------|
| `abort` | Stop execution, discard state |
| `repair` | Apply repair function, retry |
| `rollback` | Revert to last checkpoint |

---

## Fail-Closed Gate

NSC enforces fail-closed semantics:

```
NSCStep(Σ, σ):
  Σ' = execute(Σ, σ)
  if not check_admissibility(Σ', contract):
    return apply_policy(Σ, contract.policy)
  emit_receipt(Σ, σ, Σ')
  return Σ'
```

---

## Certificate Interface

### L1 Certificate

```json
{
  "type": "L1_predicate_preservation",
  "predicate_hash": "...",
  "budget_bound": "...",
  "proof": "..."
}
```

### L2 Certificate

```json
{
  "type": "L2_lyapunov_stability",
  "lyapunov_value": "...",
  "domination_relation": "...",
  "drift_inequality": "...",
  "proof_object": "..."
}
```

---

## Verification

NSC includes a strict certificate checker:

```
verify_certificate(cert, Σ) → bool
```

No trusted third parties - all verification is deterministic and local.

---

## Schema

See `nsc-kernel/schemas/nsc_contract.schema.json` for JSON Schema definition.
