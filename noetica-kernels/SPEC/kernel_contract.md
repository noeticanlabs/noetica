# CK-0 + NK-0 Kernel Contract (Normative)

NK-0 implementations MUST:
1) Emit NK-0 receipts and replay-valid chains.
2) Provide a mapping from NK-0 execution steps to CK-0 variables:
   - V_k computed from NK-0 invariants (default: Boolean → {0,1})
   - B_k from module budget declaration
   - ΔV_k and D_k computed exactly per CK-0
3) Invalidate execution when D > D_max (policy-driven threshold)

CK-0 remains the governance truth; NK-0 is the execution substrate.
