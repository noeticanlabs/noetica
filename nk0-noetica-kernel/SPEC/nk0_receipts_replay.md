# NK-0 Receipts & Replay (Normative)

Receipt hash uses canonical JSON with:
- UTF-8
- sorted keys
- separators `,` and `:` only

Replay is valid iff:
1) Receipt hash chain verifies
2) Each step input hash matches reconstructed state
3) Deterministic step function reproduces output hash
4) CK-0 linked fields (V, dV, D, B) remain recurrence-consistent
