import ReversibleConfigurationHeaderPayload
import ReversiblePaddedForest
import Mathlib.Data.List.OfFn

set_option autoImplicit false
namespace ShiReversibleFormula
variable {ι : Type}

/-- The existing padded compiler uses exactly the same base-plus-index-times-stride addresses. -/
theorem paddedForestCompile_ofFn {count : Nat} (forms : Fin count → Formula ι)
    (inputs : ι → Nat) (base bound : Nat) :
    paddedForestCompile inputs base bound (List.ofFn forms) =
      (List.ofFn (fun i => (forms i).paddedCompile inputs (base + i.val * (bound + 1)) bound)).flatten := by
  induction count generalizing base with
  | zero => simp [paddedForestCompile]
  | succ count ih =>
      simp only [List.ofFn_succ, paddedForestCompile, List.flatten_cons, Fin.val_zero, Nat.zero_mul, Nat.add_zero]
      rw [ih]
      congr 1
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext i
      congr 1
      simp only [Fin.val_succ, Nat.succ_mul]
      omega

end ShiReversibleFormula
