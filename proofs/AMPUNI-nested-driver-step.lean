import «AMPUNI-nested-machine»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOuterLift

open ShiTMLayoutMachine

theorem nested_gate_driver_mark (v : Sig)
    (S : ∀ k, List (OuterGam k)) (tail : List Cell)
    (h : S (.inr (1 : Fin 2)) = Cell.mark :: tail) :
    nestedRun^[1]
      (some { l := some (.inr .gateDriver), var := v, stk := S }) =
        some { l := some (.inl (b .parseTag)), var := some Cell.mark, stk := Function.update S (.inr (1 : Fin 2)) tail } := by
  simp [nestedRun, nestedMachine, step, stepAux, h, pop, isMark]

theorem nested_layer_driver_mark (v : Sig)
    (S : ∀ k, List (OuterGam k)) (tail : List Cell)
    (h : S (.inr (0 : Fin 2)) = Cell.mark :: tail) :
    nestedRun^[1]
      (some { l := some (.inr .layerDriver), var := v, stk := S }) =
        some { l := some (.inr .layerHeader), var := some Cell.mark, stk := Function.update S (.inr (0 : Fin 2)) tail } := by
  simp [nestedRun, nestedMachine, step, stepAux, h, pop, isMark]

end ShiTMOuterLift
