import «AMPUNI-output-entry-four-headers»
import Definitions.Def_ShiClassQMAU

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOuterLift

/-- The length-aware family encoding supplies exactly the four headers that
the redirected finite front-end consumes. -/
theorem family_headers_to_output (F : ShiClassQMA.QMAFamily) (n : Nat)
    (rest : List Cell) (v : Sig) (S : ∀ j, List (TopGam j))
    (hsrc : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit ++ rest) :
    ∃ (U : ∀ j, List (TopGam j)),
      run^[(n + 1) + (F.wit n + 1) + (F.anc n + 1) +
        ((F.out n : Nat) + 1)]
        (some { l := some (headerLabel .inputLength), var := v, stk := S }) =
          some { l := some outputEntry, var := some Cell.delim, stk := U }
      ∧ U (.inl (.inl (11 : Fin 14))) =
          (ShiBQP.encCirc (F.circ n)).map bit ++ rest
      ∧ U (.inr (0 : Fin 4)) = List.replicate n Cell.mark ++ S (.inr 0)
      ∧ U (.inr (1 : Fin 4)) = List.replicate (F.wit n) Cell.mark ++ S (.inr 1)
      ∧ U (.inr (2 : Fin 4)) = List.replicate (F.anc n) Cell.mark ++ S (.inr 2)
      ∧ U (.inr (3 : Fin 4)) =
          List.replicate (F.out n : Nat) Cell.mark ++ S (.inr 3)
      ∧ ∀ j : OuterK, j ≠ .inl (11 : Fin 14) → U (.inl j) = S (.inl j) := by
  have hsplit : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n).map bit ++ (ShiBQP.encNat (F.wit n)).map bit ++
        (ShiBQP.encNat (F.anc n)).map bit ++
        (ShiBQP.encNat (F.out n : Nat)).map bit ++
        ((ShiBQP.encCirc (F.circ n)).map bit ++ rest) := by
    simpa [ShiClassQMAU.encQMAFamilyAt, List.map_append,
      List.append_assoc] using hsrc
  exact four_headers_to_output n (F.wit n) (F.anc n) (F.out n : Nat)
    ((ShiBQP.encCirc (F.circ n)).map bit ++ rest) v S hsplit

end ShiTMOutputEntry
