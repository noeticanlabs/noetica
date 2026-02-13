import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order

namespace CK0

/-- CK-0 step variables (single-step view). -/
structure StepVars where
  Vk   : ℝ
  Ek   : ℝ
  Ck   : ℝ
  Bk   : ℝ
  deriving Repr

/-- CK-0 single-step violation recurrence: V_{k+1} = V_k + E_k - C_k. -/
def Vnext (s : StepVars) : ℝ := s.Vk + s.Ek - s.Ck

/-- CK-0 single-step debt recurrence: D_{k+1} = max(0, D_k + dV_k - B_k). -/
def Dnext (Dk dVk Bk : ℝ) : ℝ := max 0 (Dk + dVk - Bk)

/-- Budget constraint: 0 ≤ Ck ≤ Bk and nonnegativity for Vk, Ek, Bk. -/
def CK0Constraints (s : StepVars) : Prop :=
  0 ≤ s.Vk ∧ 0 ≤ s.Ek ∧ 0 ≤ s.Bk ∧ 0 ≤ s.Ck ∧ s.Ck ≤ s.Bk

end CK0
