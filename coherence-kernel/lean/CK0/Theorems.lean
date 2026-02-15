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

namespace CK0

theorem debt_nonneg (Dk dVk Bk : ℝ) : 0 ≤ Dnext Dk dVk Bk := by
  simp [Dnext]

theorem debt_monotone_zero_budget (Dk dVk : ℝ) (hdv : 0 ≤ dVk) :
  Dk ≤ Dnext Dk dVk 0 := by
  have : Dk ≤ Dk + dVk := by linarith
  have : Dk ≤ max 0 (Dk + dVk - 0) := by
    have h1 : Dk ≤ Dk + dVk := by linarith
    have h2 : Dk + dVk ≤ max 0 (Dk + dVk) := by
      exact le_max_right _ _
    exact le_trans h1 h2
  simpa [Dnext] using this

end CK0
