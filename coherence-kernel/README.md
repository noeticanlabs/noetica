# Coherence Kernel

## Certified Debt Governance

Coherence is the mathematical kernel that provides certified debt governance for NSC execution. It defines:

* **Residual-energy geometry** - mathematical foundation for debt tracking
* **Curvature/budget laws** - stability conditions
* **Debt certification** - proof objects for debt bounds
* **Lyapunov stability** - formal guarantees for bounded debt evolution

---

## Specification

- [`SPEC/ck0_spec.md`](SPEC/ck0_spec.md) - Main mathematical specification
- [`SPEC/ck0_theorems.md`](SPEC/ck0_theorems.md) - Lyapunov, domination, drift theorems
- [`SPEC/ck0_receipts.md`](SPEC/ck0_receipts.md) - Receipt definitions

---

## Interface to NSC

Coherence provides certified debt callbacks:

### Certification Request
```json
{
  "V_k": "invariant violations",
  "B_k": "budget",
  "residuals": "residual values"
}
```

### Certification Response
```json
{
  "D_k": "certified debt",
  "proof_object": "proof of bounds",
  "timestamp": "certification time"
}
```

---

## Guarantees

* Lyapunov stability certification
* Debt bounds verification
* Perturbation tolerance
* Certified proof objects
* Certified debt callback interface for NSC integration

---

## Conformance

A Coherence implementation conforms if it:
1) Implements the recurrence laws exactly (SPEC/ck0_spec.md)
2) Provides debt certification on request
3) Emits verifiable proof objects
4) Maintains stability guarantees

---

## Non-goals

Coherence does not define a programming language. It defines the mathematical governance contract for debt tracking and stability.
