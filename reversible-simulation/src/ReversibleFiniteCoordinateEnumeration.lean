import ReversibleConfigurationCoordinates
import Mathlib.Data.List.OfFn

set_option autoImplicit false
namespace ShiReversibleTM
variable {α : Type} {m n : Nat}

/-- Sum-coordinate enumeration uses the entire left block before the right block. -/
theorem ofFn_sum_coordinates (f : Fin m ⊕ Fin n → α) :
    List.ofFn (fun i => f (finSumFinEquiv.symm i)) =
      List.ofFn (fun i => f (.inl i)) ++ List.ofFn (fun j => f (.inr j)) := by
  rw [List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn
    funext i
    apply congrArg f
    apply finSumFinEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl
  · apply congrArg List.ofFn
    funext j
    apply congrArg f
    apply finSumFinEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl

/-- Product coordinates have the same outer/inner rank order as the established bit equivalence. -/
theorem ofFn_prod_coordinates (f : Fin m × Fin n → α) :
    List.ofFn (fun i => f (finProdFinEquiv.symm i)) =
      (List.ofFn (fun i : Fin m => List.ofFn (fun j : Fin n => f (i, j)))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  apply congrArg f
  apply finProdFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  change i.val * n + j.val = j.val + n * i.val
  ring

end ShiReversibleTM
