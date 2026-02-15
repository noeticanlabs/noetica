# Noetica + NSC + Coherence Kernel Contract (Normative)

## Overview

This document defines the 3-way contract between:

- **Noetica** - Semantic Language Kernel (meaning)
- **NSC** - Deterministic Governed Execution Substrate (execution)
- **Coherence** - Certified Debt Governance (certification)

---

## Noetica → NSC Contract

Noetica implementations MUST:

1. Emit deterministic action streams
2. Provide canonicalizable semantic state serialization
3. Include registry digest for replay lock
4. Define action schema (WRITE, CALL, ASSERT, REPAIR, SOLVE, MEASURE)

---

## NSC → Coherence Contract

NSC implementations MUST:

1. Request debt certification when contract level is L2
2. Pass V_k (invariant violations), B_k (budget), residuals to Coherence
3. Handle certification responses with fail-closed semantics
4. If certification invalid/expired → treat as debt exceeded

---

## Coherence Contract

Coherence implementations MUST:

1. Compute certified debt D_k from V_k, B_k, residuals
2. Provide verifiable proof objects
3. Return timestamp and validity bounds
4. Maintain Lyapunov stability guarantees

---

## Governance Flow

```
Noetica (semantics) → Action stream → NSC (execution)
                                          │
                    ┌─────────────────────┼─────────────────────┐
                    ▼                     ▼                     ▼
              Budget check          Contract check         Certification
                    │                     │                     │
                    └─────────────────────┼─────────────────────┘
                                          ▼
                                    Governance result
                                          │
                    ┌─────────────────────┼─────────────────────┐
                    ▼                     ▼                     ▼
              Proceed              Apply policy           Update debt
                                    (abort/repair/rollback)
```

---

## Invalidation

NSC MUST invalidate execution when:

1. D > D_max (budget exceeded)
2. Contract predicate fails (L1/L2)
3. Rail constraint violated
4. Certification invalid/expired

---

## Replay

All three kernels MUST support replay:

- Noetica: deterministic action emission
- NSC: receipt chain verification
- Coherence: deterministic debt computation
