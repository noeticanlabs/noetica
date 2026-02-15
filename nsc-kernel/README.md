# NSC Kernel

## Deterministic Governed Execution Substrate

NSC is the runtime kernel that executes Noetica programs under governance. It provides deterministic execution, tamper-evident receipts, replay verification, and contract enforcement.

---

## Specification

- [`SPEC/nsc_spec.md`](SPEC/nsc_spec.md) - Main runtime specification
- [`SPEC/nsc_receipts.md`](SPEC/nsc_receipts.md) - Receipt chain format
- [`SPEC/nsc_replay.md`](SPEC/nsc_replay.md) - Replay verification
- [`SPEC/nsc_contracts.md`](SPEC/nsc_contracts.md) - Contract levels (L0/L1/L2)
- [`SPEC/nsc_rails.md`](SPEC/nsc_rails.md) - Rail enforcement

---

## Schemas

- `schemas/nsc_receipt.schema.json` - Receipt JSON Schema
- `schemas/nsc_replay_report.schema.json` - Replay report JSON Schema

---

## Interface

### To Noetica (Consumer)
NSC receives actions from Noetica and executes them deterministically:
- `WRITE(var, value)` - Write to variable
- `CALL(op_id, args)` - Call operator
- `ASSERT(pred)` - Assert predicate
- `REPAIR(hint)` - Apply repair hint
- `SOLVE(residual_id, params)` - Solve residual
- `MEASURE(metric_id, params)` - Measure metric

### To Coherence (Certified Debt)
NSC may request debt certification:
- Certification request: `{ V_k, B_k, residuals }`
- Certification response: `{ D_k, proof_object, timestamp }`

---

## Guarantees

- Deterministic execution of actions
- Tamper-evident receipts (hash chain)
- Replay equality
- Fail-closed governance
- Rail-constrained updates
- Schema-stable canonicalization
