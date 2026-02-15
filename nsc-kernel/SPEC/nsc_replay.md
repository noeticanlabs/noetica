# NSC Replay Specification

## Overview

Replay verifies deterministic execution by reproducing the receipt chain from genesis and comparing hashes.

---

## Replay Algorithm

### Full Replay

```
replay(receipts: [R_0, ..., R_n], actions: [σ_1, ..., σ_n]) → ReplayResult:
  Σ = genesis_state
  
  for k in 1..n:
    # Execute action deterministically
    Σ' = NSCStep(Σ, σ_k)
    
    # Verify receipt matches
    if R_k.curr != H(canonical(Σ')):
      return ReplayResult(failed_at=k, reason="state_hash_mismatch")
    
    Σ = Σ'
  
  return ReplayResult(success=true, final_state=Σ)
```

---

## Replay Verification

### Hash Equality Check

```
verify_replay_hash(receipt, state):
  computed = H(canonical(state))
  return computed == receipt.curr
```

### Chain Continuity Check

```
verify_chain_continuity(R_{k-1}, R_k):
  return R_k.prev == R_{k-1}.curr
```

---

## Replay Report

```json
{
  "replay_result": {
    "success": true,
    "verified_steps": 100,
    "final_state_hash": "...",
    "mismatches": []
  }
}
```

### Failure Report

```json
{
  "replay_result": {
    "success": false,
    "failed_at_step": 42,
    "reason": "state_hash_mismatch",
    "expected_hash": "...",
    "computed_hash": "..."
  }
}
```

---

## Registry Lock

Replay requires a stable registry:

- Registry digest captured at genesis
- Any registry changes invalidate replay
- Digest included in genesis receipt

```
registry_digest = H(registry_contents)
```

---

## Determinism Guarantees

For replay to succeed:

1. **Same actions**: Action stream must be identical
2. **Same initial state**: Genesis state must match
3. **Same registry**: Operator/type registry must be stable
4. **Deterministic execution**: NSCStep must be pure

---

## Schema

See `nsc-kernel/schemas/nsc_replay_report.schema.json` for JSON Schema definition.
