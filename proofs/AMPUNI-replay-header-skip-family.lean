import «AMPUNI-replay-header-skip-four-run»
import «AMPUNI-output-entry-family»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMReplayHeaderSkip

open ShiTMLayoutMachine ShiTMRetainedTop

/-- On the actual length-aware verifier encoding, header skipping positions
the source at the circuit bytes and leaves the retained parameters untouched. -/
theorem skip_family_run (F : ShiClassQMA.QMAFamily) (n : Nat)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (hsrc : S source =
      (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit) :
    ∃ U : ∀ k, List (TopGam k),
      run^[skipCost n (F.wit n) (F.anc n) (F.out n : Nat)]
        (some ⟨some (0 : Phase), v, S⟩) =
          some ⟨some (4 : Phase), some Cell.delim, U⟩
      ∧ U source = (ShiBQP.encCirc (F.circ n)).map bit
      ∧ ∀ j : TopK, j ≠ source → U j = S j := by
  have hsplit : S source =
      (ShiBQP.encNat n).map bit ++
      (ShiBQP.encNat (F.wit n)).map bit ++
      (ShiBQP.encNat (F.anc n)).map bit ++
      (ShiBQP.encNat (F.out n : Nat)).map bit ++
      (ShiBQP.encCirc (F.circ n)).map bit := by
    simpa [ShiClassQMAU.encQMAFamilyAt, List.map_append,
      List.append_assoc] using hsrc
  exact skip_four_run n (F.wit n) (F.anc n) (F.out n : Nat)
    ((ShiBQP.encCirc (F.circ n)).map bit) v S hsplit

end ShiTMReplayHeaderSkip
