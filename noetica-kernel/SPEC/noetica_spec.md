# Noetica Kernel

## Semantic Language Kernel (Noetica-SLK) v1.0

---

# 0. What Noetica Is Now

Noetica is the **semantic definition** of the language:

* glyph system (encoding + identity)
* syntax / AST rules
* typing rules
* operator registry semantics
* evaluation/reduction rules
* module linking semantics
* how programs produce actions (σ) to be executed by NSC

Noetica does **not** define receipts, hashing, replay, budgets, or debt enforcement. That's NSC.

---

# 1. Program Forms

A Noetica program (P) is parsed (from glyphs or text) into an AST:

[
P \Rightarrow \mathrm{AST}(P)
]

Then lowered to a semantic IR:

[
\mathrm{AST}(P)\Rightarrow \mathrm{IR}(P)
]

(You can still call the IR "NSC-IR" if you want, but the **kernel meaning** is in Noetica now.)

---

# 2. Type System

Typing judgment:

[
\Gamma \vdash e : \tau
]

Noetica defines:

* base types
* composite types
* contract annotations (as types or as attached metadata)
* effect annotations (if any)

---

# 3. Operational Semantics

Noetica defines meaning by a reduction relation that produces **actions**:

[
\langle e, S\rangle \Rightarrow \langle e', S', \sigma\rangle
]

Interpretation:

* Noetica evaluates an expression in semantic state (S),
* produces next semantic state (S'),
* and emits an action (σ) to be executed by NSC.

---

# 4. Action Algebra

Actions (σ) are the sole interface to NSC. Example classes:

* `WRITE(var, value)` - Write to variable
* `CALL(op_id, args)` - Call operator
* `ASSERT(pred)` - Assert predicate
* `REPAIR(hint)` - Apply repair hint
* `SOLVE(residual_id, params)` - Solve residual
* `MEASURE(metric_id, params)` - Measure metric

Noetica defines **what these actions mean**.
NSC defines **how they are executed safely and auditable**.

---

# 5. Glyph Semantics

Glyphs map to operators and typed constructs:

[
\mathrm{GlyphSeq} \Rightarrow \mathrm{AST}
\Rightarrow \mathrm{IR}
\Rightarrow \text{typed actions}
]

This is where:

* GLLL identity guarantees
* GHLL semantic operator meaning
* registry binding
* ambiguity resolution rules

all live.

---

# 6. Noetica Guarantees

Noetica guarantees:

* well-formedness (grammar)
* type correctness (static semantics)
* meaning preservation across lowering stages
* deterministic action emission **given the same inputs and registry**
* **canonicalizable** semantic-state serialization (NSC implements canonicalization)

Noetica does **not** guarantee:

* audit integrity
* replay verification
* budget/debt admissibility

That's NSC.

---

# 7. Interface to NSC

Noetica provides to NSC:

1. a **semantic state** (S) serialization contract (so receipts can hash it)
2. a deterministic **action stream** emitter
3. an action schema for (σ)
4. a registry digest (operators/types) used for replay lock

---

# Normative References

* NSC Kernel (execution substrate)
* Coherence Kernel (certification interface)
* `noetica-kernels/SPEC/kernel_contract.md`
* `noetica-kernels/SPEC/interface_seam.md`
