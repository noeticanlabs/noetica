# CK-0 Receipts & Replay (Normative)

## Receipt chain
Define canonical encoding enc(R) as deterministic JSON:
- UTF-8
- sorted keys
- no whitespace
- floats encoded with fixed rules (recommend: decimal string with max 17 sig figs)

Define:
h(R) := SHA-256(enc(R))

A receipt includes prev_receipt_hash = h(R_{k-1}) (or 32 bytes of 0 for k=0).

## Replay verification predicate
Given initial state x_0 and receipts {R_k}:
Replay is valid iff for all k:
1) prev hash matches: R_k.prev = h(R_{k-1})
2) input/output hashes match recomputed state hashes
3) violation/debt fields satisfy CK-0 recurrences exactly
4) budget bound enforced: 0 ≤ C_k ≤ B_k (if C_k recorded) OR if C_k omitted, system must provide a proof-equivalent field (e.g., C_k implied by rule)
5) invalidation enforced if any D_k > D_max

## Canonical hash of state
state_hash := SHA-256(canonical_bytes(state))
Canonicalization MUST be declared (format + ordering).
