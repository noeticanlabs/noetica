# NK-0 Conformance (Normative)

An implementation conforms to NK-0 iff:

1. Parser accepts grammar-conforming modules and rejects malformed syntax.
2. Typechecker enforces rules in `nk0_typing_rules.md`.
3. Runtime executes deterministically and evaluates assertions.
4. Receipts are emitted per step, hash-linked, and schema-valid.
5. Replay verification can validate a receipt chain from an initial store.
