# NK-0 Noetica Kernel (Normative + Reference)

NK-0 is a minimal deterministic execution kernel with:
- declarative module grammar
- small but normative typing rules
- operational semantics with receipt emission
- replay verification over hash-linked receipts

This repo contains:
- Normative specs in SPEC/
- JSON schemas for modules, receipts, replay reports
- Minimal deterministic Python parser/typechecker/runtime
- Examples, test vectors, and tests

## Conformance
An implementation conforms to NK-0 iff it:
1) Accepts modules per grammar and typing rules
2) Executes deterministically for the same inputs
3) Emits hash-linked receipts matching schema
4) Supports replay verification from initial store and receipts
