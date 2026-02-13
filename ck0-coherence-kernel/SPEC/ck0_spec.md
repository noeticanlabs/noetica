# CK-0 Spec (Normative)

## 1. State, invariants, violation
Let X be a state space. Define:
- I : X → Prop (invariants)
- V : X → ℝ≥0 (violation magnitude)

Validity is defined by policy:
- Strict mode: valid(x) ↔ I(x) and V(x)=0
- Relaxed mode: valid(x) ↔ V(x) ≤ V_max (with I derived/approximate)

CK-0 requires only: V(x)=0 ⇒ I(x).

## 2. Evolution
Discrete steps k = 0,1,2,...

State update:
x_{k+1} = F(x_k, u_k)

Violation recurrence:
V_{k+1} = V_k + E_k − C_k

where:
- E_k ≥ 0 is intrinsic violation growth (uncontrolled drift, disturbances, approximation error)
- C_k is corrective action applied

Budget constraint:
0 ≤ C_k ≤ B_k, with B_k ≥ 0

## 3. Incremental growth and debt
Incremental violation:
ΔV_k := max(0, V_k − V_{k−1}) for k≥1, and ΔV_0 := 0.

Debt recurrence:
D_{k+1} := max(0, D_k + ΔV_k − B_k), with D_0 ≥ 0.

Invalidation rule:
If D_k > D_max, the system MUST enter an invalid state (halt, revoke, or escalate per governance).

## 4. Receipt obligation
At each step k, emit a receipt R_k containing:
- step_id = k
- input_hash, output_hash
- module_hash / rule_hash (identifier of F used)
- V_k, V_{k+1}, ΔV_k, B_k, D_k, D_{k+1}
- prev_receipt_hash (chain)
- timestamp (optional; non-normative for replay)

Receipts MUST be hash-linked and replay-verifiable (see ck0_receipts.md).
