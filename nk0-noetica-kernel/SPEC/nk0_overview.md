# NK-0 Overview (Normative)

NK-0 specifies a deterministic kernel for module parsing, typing, execution,
receipt emission, and replay verification.

Execution is deterministic for fixed:
- module source
- input store
- function arguments

Receipts are mandatory at step boundaries and are hash-linked.
