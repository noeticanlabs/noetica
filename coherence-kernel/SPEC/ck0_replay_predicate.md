# CK-0 Replay Predicate (Normative)

Define `ReplayValid(x0, {Rk}, F, Canon)` iff for all k:

1. Hash chain: `Rk.prev_receipt_hash = h(Rk-1)` with `h` per canonicalization.
2. State hash: `Rk.input_hash = h(Canon(xk))` and `Rk.output_hash = h(Canon(xk+1))`.
3. Recurrence: `V_{k+1} = V_k + E_k - C_k` and `D_{k+1} = max(0, D_k + ΔV_k - B_k)`.
4. Debt invalidation: if any `D_k > D_max`, invalidation MUST trigger at the first such k.

Replay is valid iff all conditions hold for the full receipt chain.
