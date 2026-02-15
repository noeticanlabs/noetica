# NK-0 Operational Semantics (Normative)

Execution state:
⟨σ, ρ, k⟩ where:
- σ is the store mapping variables to values
- ρ is the receipt chain accumulator
- k is step_id

A function call executes deterministically:
1) Evaluate expressions left-to-right
2) Apply primitive operations exactly (IEEE-754 Real in reference runtime)
3) For each step, emit a receipt R_k with:
   input_hash = H(σ_in), output_hash = H(σ_out)
   rule_id = module_hash + function_name
   invariant_status before/after
   V_k, V_k1, dV_k, B_k, D_k, D_k1 (via CK-0 linkage)
4) If an assert fails, execution halts and emits a terminal receipt with status=FAILED_ASSERT.

Invariant handling:
- NK-0 requires invariants be evaluated at step boundaries.
- Violation V is computed by policy; NK-0 reference uses:
  V = 0 if all invariants true else 1
This is intentionally minimal; richer V is an extension.

Budget policy:
- NK-0 defines B_k := module.budget (constant per module) in the reference kernel.
- Extensions may add per-function or dynamic budgets, but MUST declare the policy.
