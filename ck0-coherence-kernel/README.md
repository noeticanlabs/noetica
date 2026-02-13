# CK-0 Coherence Kernel (Normative)

CK-0 defines the minimal formal contract for coherence-governed evolution:
- invariant predicate I : X → Prop
- violation measure V : X → ℝ≥0
- intrinsic growth E ≥ 0
- corrective action C bounded by budget B
- debt accumulator D with a hard invalidation bound D_max
- receipt + replay verification predicates

This repo contains:
- Normative spec in SPEC/
- JSON schemas for receipts and replay reports
- Lean 4 kernel (no `sorry` in CK0 core files)
- Reference Python model and test vectors

## Conformance
A system conforms to CK-0 iff it:
1) Implements the CK-0 recurrence laws exactly (SPEC/ck0_spec.md)
2) Emits receipts matching schemas/ck0_receipt.schema.json
3) Replays and verifies receipt chains (SPEC/ck0_receipts.md)
4) Enforces invalidation when D > D_max

## Non-goals
CK-0 does not define a programming language. It defines a governance-grade evolution contract.