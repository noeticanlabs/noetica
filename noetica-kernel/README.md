# Noetica Kernel

## Semantic Language Kernel

Noetica is the semantic definition layer of the Noetica computing language. It defines:

* **Glyph system** - encoding and identity
* **Syntax/AST rules** - grammar and parsing
* **Typing rules** - static semantics
* **Operator registry** - semantic meaning of operators
* **Evaluation/reduction rules** - operational semantics
* **Action emission** - produces actions for NSC execution

---

## Specification

- [`SPEC/noetica_spec.md`](SPEC/noetica_spec.md) - Main semantic specification
- [`SPEC/nk0_grammar.ebnf`](SPEC/nk0_grammar.ebnf) - Module grammar
- [`SPEC/nk0_typing_rules.md`](SPEC/nk0_typing_rules.md) - Type system
- [`SPEC/nk0_operational_semantics.md`](SPEC/nk0_operational_semantics.md) - Reduction rules

---

## Action Algebra

Noetica emits actions that NSC executes:

| Action | Description |
|--------|-------------|
| `WRITE(var, value)` | Write to variable |
| `CALL(op_id, args)` | Call operator |
| `ASSERT(pred)` | Assert predicate |
| `REPAIR(hint)` | Apply repair hint |
| `SOLVE(residual_id, params)` | Solve residual |
| `MEASURE(metric_id, params)` | Measure metric |

---

## Interface to NSC

Noetica provides:
1. **Semantic state serialization** - canonicalizable state for receipts
2. **Action stream** - deterministic emission of actions
3. **Action schema** - versioned JSON schema for actions
4. **Registry digest** - hash of operators/types for replay lock

---

## Guarantees

* Well-formedness (grammar)
* Type correctness (static semantics)
* Meaning preservation across lowering
* Deterministic action emission
* Canonicalizable semantic-state serialization

---

## Conformance

A Noetica implementation conforms if it:
1. Accepts modules per grammar and typing rules
2. Produces well-typed IR from glyphs/AST
3. Emits deterministic action streams
4. Provides canonicalizable state serialization
