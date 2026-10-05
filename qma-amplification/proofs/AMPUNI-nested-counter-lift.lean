import «AMPUNI-nested-driver-step»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOuterLift

open ShiTMLayoutMachine

theorem liftStacks_update_counter (S : ∀ k, List (Gam k))
    (C : Fin 2 → List Cell) (k : Fin 2) (v : List Cell) :
    Function.update (liftStacks S C) (.inr k) v =
      liftStacks S (Function.update C k v) := by
  funext j
  cases j with
  | inl j =>
    have h : (Sum.inl j : OuterK) ≠ Sum.inr k := by simp
    rw [Function.update_of_ne h]
    rfl
  | inr j =>
    by_cases h : j = k
    · subst h
      simp [liftStacks]
    · have hj : (Sum.inr j : OuterK) ≠ Sum.inr k := by
        intro e
        exact h (Sum.inr.inj e)
      rw [Function.update_of_ne hj]
      change C j = Function.update C k v j
      rw [Function.update_of_ne h]

theorem nested_gate_driver_mark_lift (v : Sig)
    (S : ∀ k, List (Gam k)) (C : Fin 2 → List Cell)
    (tail : List Cell) (h : C 1 = Cell.mark :: tail) :
    nestedRun^[1]
      (some { l := some (.inr .gateDriver), var := v, stk := liftStacks S C }) =
        some (liftCfg (Function.update C 1 tail)
          { l := some (b .parseTag), var := some Cell.mark, stk := S }) := by
  rw [nested_gate_driver_mark v (liftStacks S C) tail (by simpa [liftStacks] using h)]
  simp [liftCfg, liftStacks_update_counter]

theorem nested_layer_driver_mark_lift (v : Sig)
    (S : ∀ k, List (Gam k)) (C : Fin 2 → List Cell)
    (tail : List Cell) (h : C 0 = Cell.mark :: tail) :
    nestedRun^[1]
      (some { l := some (.inr .layerDriver), var := v, stk := liftStacks S C }) =
        some { l := some (.inr .layerHeader), var := some Cell.mark, stk := liftStacks S (Function.update C 0 tail) } := by
  rw [nested_layer_driver_mark v (liftStacks S C) tail (by simpa [liftStacks] using h)]
  rw [liftStacks_update_counter]

end ShiTMOuterLift
