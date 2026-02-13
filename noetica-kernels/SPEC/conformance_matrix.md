# Conformance Matrix

| Requirement | CK-0 | NK-0 | Evidence |
|---|---|---|---|
| Violation recurrence | MUST | maps to CK fields | `ck0_spec.md`, runtime receipts |
| Debt + invalidation | MUST | MUST map/enforce | `ck0_spec.md`, runtime policy checks |
| Receipt chain | MUST | MUST | receipt schema + verify_chain |
| Replay verification | MUST | MUST | replay modules + tests |
| Deterministic execution | N/A | MUST | `nk0_runtime.py`, replay tests |
