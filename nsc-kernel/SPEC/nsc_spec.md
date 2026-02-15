# NSC KERNEL

## Deterministic Governed Execution Substrate (NSC-DGES) v1.0

---

# 0. What NSC Is Now

NSC is the **minimal deterministic runtime** that executes *Noetica programs* under governance:

* deterministic stepping
* canonicalization
* hash chaining receipts
* replay verification
* contract enforcement (L0/L1/L2)
* rails enforcement
* budget/debt gating
* optional Coherence Kernel integration (certified debt)

NSC does **not** define meaning. It executes meaning supplied by Noetica.

---

# 1. Runtime State

[
\Sigma := (S, E, K, \Omega)
]

* (S): **opaque program state** (Noetica-owned)
* (E): environment (registries, config, clocks)
* (K): kernel governance state (budgets, debt, rail-mode, contract pointers)
* (\Omega): receipt chain accumulator

---

# 2. Deterministic Step Function

NSC defines an abstract step:

[
\mathrm{NSCStep} : (\Sigma, \sigma) \to \Sigma'
]

where (\sigma) is a **resolved action** emitted by the Noetica semantic layer.

Determinism axiom:

[
(\Sigma,\sigma)\mapsto \Sigma' \text{ is unique.}
]

If any nondeterminism is allowed, it must be:

* explicitly declared,
* seeded,
* committed to receipts,
* and replay-identical.

---

# 3. Canonicalization and Hashing

## 3.1 Canonical serialization

[
\mathrm{canon} : \Sigma \to \mathrm{Bytes}
]
Must be deterministic, schema-stable, key-sorted, and numeric-canonical.

## 3.2 Receipt chain

Receipts (R_k) satisfy:

* (R_k.\mathrm{prev} = R_{k-1}.\mathrm{curr})
* (R_k.\mathrm{curr} = H(\mathrm{canon}(R_k\setminus{\mathrm{curr}})))

Genesis:

* (R_0.\mathrm{prev}=\mathrm{GENESIS})

---

# 4. Contracts and Admissibility

A program or module declares:

[
\mathsf{ExecContract}=
\langle \mathrm{level}, \mathbf B, \mathrm{rails}, \mathrm{cert}, \mathrm{policy} \rangle
]

Admissibility:

[
\mathcal A(\Sigma) := [\mathbf D \preceq \mathbf B]\ \wedge\ \text{rail-ok}\ \wedge\ \text{cert-ok}
]

Fail-closed gate:

* if (\mathcal A(\Sigma')) fails → reject step and apply policy (abort/repair/rollback)

---

# 5. Rails

Rails define permitted update directions (or permitted action classes). Enforcement is deterministic:

* reject mode: step invalid
* project mode: apply deterministic projection and log it in receipt

---

# 6. Debt/Budget Interface

NSC maintains governance variables (D) or (\mathbf D).

Debt update sources:

* **Certified debt callback** from Coherence Kernel (preferred)
* Or declared local update function `upd` (L0/L1 only)

Debt and budget must be receipt-visible.

---

# 7. Certificate Checking (L1/L2)

NSC includes the **verifier interface**:

* L1: predicate preservation under within-budget stepping
* L2: debt equals Lyapunov measure + domination + drift inequality

Proof objects must be checkable by a strict checker (no "trust me bro").

---

# 8. Replay Determinism

Replay must reproduce receipt chain exactly:

[
R_k^{\mathrm{replay}}.\mathrm{curr} = R_k^{\mathrm{orig}}.\mathrm{curr}\quad \forall k
]

---

# 9. NSC Guarantees

Given deterministic semantics from Noetica and valid contracts, NSC guarantees:

* deterministic execution
* tamper-evident receipts
* replay equality
* fail-closed governance
* rail-constrained updates (if enabled)

NSC does **not** define meaning.

---

# 10. Interface to Noetica

## 10.1 Action Schema

Actions (\sigma) received from Noetica:

```
WRITE(var, value)    -> Write to variable
CALL(op_id, args)    -> Call operator
ASSERT(pred)          -> Assert predicate
REPAIR(hint)         -> Apply repair hint
SOLVE(residual_id, params)  -> Solve residual
MEASURE(metric_id, params)   -> Measure metric
```

## 10.2 State Serialization Contract

Noetica provides:

* Semantic state (S) serialization format
* Registry digest for replay lock
* Action schema version

---

# 11. Interface to Coherence

## 11.1 Certified Debt Callback

NSC may request debt certification:

```
CertificationRequest:
  - V_k: invariant violations
  - B_k: budget
  - residuals: residual values
  
CertificationResponse:
  - D_k: certified debt
  - proof_object: proof of bounds
  - timestamp: certification time
```

## 11.2 Fail-Closed Integration

If Coherence returns invalid/expired certification:

* Treat as debt exceeded
* Apply contract policy (abort/repair/rollback)

---

# Normative References

* Noetica Semantic Kernel (action definitions)
* Coherence Kernel (certification interface)
* `noetica-kernels/SPEC/kernel_contract.md`
* `noetica-kernels/SPEC/interface_seam.md`
