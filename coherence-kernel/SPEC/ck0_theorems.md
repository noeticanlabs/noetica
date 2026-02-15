# CK-0 Theorems (Normative Core + Reference)

This document captures minimal reviewable theorem obligations for CK-0.

## Sufficient single-step contraction condition
Given:
- E_k ≤ λV_k
- B_k ≥ (λ + μ)V_k
- C_k = B_k

Then:
V_{k+1} ≤ (1 - μ)V_k.

The Lean proof of this sufficient condition is in `lean/CK0/Theorems.lean`.

## Scope
These are sufficient, not necessary, conditions. CK-0 conformance does not require proving global asymptotic stability.
