# CK-0 Conformance (Normative)

A system conforms to CK-0 iff it satisfies all of the following:

1. Evolution recurrences are implemented exactly:
   - V_{k+1} = V_k + E_k - C_k
   - ΔV_k = max(0, V_k - V_{k-1}), with ΔV_0 = 0
   - D_{k+1} = max(0, D_k + ΔV_k - B_k)

2. Budget constraints are enforced:
   - 0 ≤ C_k ≤ B_k

3. Invalidation is enforced when:
   - D_k > D_max

4. Receipts are emitted and hash-linked per `ck0_receipts.md`.

5. Replay verification checks pass for every provided chain.
