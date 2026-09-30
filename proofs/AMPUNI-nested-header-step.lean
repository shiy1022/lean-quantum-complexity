import «AMPUNI-nested-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOuterLift

open ShiTMLayoutMachine

def headerAt : Fin 2 → OuterControl
  | 0 => .circuitHeader
  | 1 => .layerHeader

def headerNext : Fin 2 → OuterControl
  | 0 => .layerDriver
  | 1 => .gateDriver

/-- A true unary header bit is copied to output and counted. -/
theorem nested_header_mark (k : Fin 2) (v : Sig)
    (S : ∀ j, List (OuterGam j)) (rest : List Cell)
    (hsrc : S (.inl (11 : Fin 14)) = .mark :: rest) :
    nestedRun^[1]
      (some { l := some (.inr (headerAt k)), var := v, stk := S }) =
        some { l := some (.inr (headerAt k)), var := (some Cell.mark), stk := Function.update (Function.update (Function.update S (.inl (11 : Fin 14)) rest) (.inr k) (.mark :: S (.inr k))) (.inl (13 : Fin 14)) (.mark :: S (.inl (13 : Fin 14))) } := by
  fin_cases k <;>
    simp [headerAt, nestedRun, nestedMachine, scanHeader, step, stepAux,
      hsrc, pop, isSome, isMark, cst]

/-- A false unary header bit terminates the count and is copied to output. -/
theorem nested_header_delim (k : Fin 2) (v : Sig)
    (S : ∀ j, List (OuterGam j)) (rest : List Cell)
    (hsrc : S (.inl (11 : Fin 14)) = .delim :: rest) :
    nestedRun^[1]
      (some { l := some (.inr (headerAt k)), var := v, stk := S }) =
        some { l := some (.inr (headerNext k)), var := (some Cell.delim), stk := Function.update (Function.update S (.inl (11 : Fin 14)) rest) (.inl (13 : Fin 14)) (.delim :: S (.inl (13 : Fin 14))) } := by
  fin_cases k <;>
    simp [headerAt, headerNext, nestedRun, nestedMachine, scanHeader,
      step, stepAux, hsrc, pop, isSome, isMark, cst]

end ShiTMOuterLift
