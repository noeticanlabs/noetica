import CK0.CK0
import Mathlib.Data.String.Defs

namespace CK0

structure Receipt where
  stepId : Nat
  ruleId : String
  inputHash : String
  outputHash : String
  Vk : ℝ
  Vk1 : ℝ
  dVk : ℝ
  Bk : ℝ
  Dk : ℝ
  Dk1 : ℝ
  prevReceiptHash : String
  receiptHash : String
  deriving Repr

end CK0
