import CK0.CK0
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace CK0

theorem step_contraction
  (s : StepVars) (λ μ : ℝ)
  (hμ : 0 < μ) (hλ : 0 ≤ λ)
  (hC : s.Ck = s.Bk)
  (hE : s.Ek ≤ λ * s.Vk)
  (hB : s.Bk ≥ (λ + μ) * s.Vk) :
  Vnext s ≤ (1 - μ) * s.Vk := by
  simp [Vnext, hC]
  have : s.Ek - s.Bk ≤ -μ * s.Vk := by
    have h1 : s.Ek - s.Bk ≤ (λ * s.Vk) - ((λ + μ) * s.Vk) := by
      exact sub_le_sub hE hB
    have hs : (λ * s.Vk) - ((λ + μ) * s.Vk) = -μ * s.Vk := by
      ring
    simpa [hs] using h1
  linarith

end CK0
