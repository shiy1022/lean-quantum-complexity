import «AMPUNI-output-entry-archive-frame»
import «AMPUNI-output-nested-header-frame»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop

/-- The first mapped circuit consumes the input stack, but leaves the saved
input underneath the retained output-index marks untouched. -/
theorem first_pass_archive_frame
    (F : ShiClassQMA.QMAFamily) (n : Nat)
    (S U V : ∀ j, List (TopGam j)) (steps : Nat) (v : Sig)
    (hsrc : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit)
    (hret0 : S (.inr (0 : Fin 4)) = [])
    (hret1 : S (.inr (1 : Fin 4)) = [])
    (hret2 : S (.inr (2 : Fin 4)) = [])
    (h13 : S (.inl (.inl (13 : Fin 14))) = [])
    (h3 : S (.inl (.inl (3 : Fin 14))) = [])
    (h1 : S (.inl (.inl (1 : Fin 14))) = [])
    (h2 : S (.inl (.inl (2 : Fin 14))) = [])
    (h8 : S (.inl (.inl (8 : Fin 14))) = [])
    (h9 : S (.inl (.inl (9 : Fin 14))) = [])
    (h10 : S (.inl (.inl (10 : Fin 14))) = [])
    (hentry : run^[entryCost F n]
      (some { l := some (headerLabel .inputLength), var := v, stk := S }) =
        some ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, U⟩)
    (hpass : run^[steps]
      (some ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, U⟩) =
        some ⟨some (parserLabel (.inl (.inr .exit))), none, V⟩) :
    V (.inr (3 : Fin 4)) =
      List.replicate (F.out n : Nat) Cell.mark ++ S (.inr (3 : Fin 4)) := by
  calc
    V (.inr (3 : Fin 4)) = U (.inr (3 : Fin 4)) :=
      nested_run_preserves_header (.inr .circuitHeader) none none
        (some (parserLabel (.inl (.inr .exit))) ) U V steps hpass 3
    _ = List.replicate (F.out n : Nat) Cell.mark ++ S (.inr (3 : Fin 4)) :=
      full_entry_archive_frame F n [] v S U
        (by simpa using hsrc) hret0 hret1 hret2 h13 h3 h1 h2 h8 h9 h10 hentry

end ShiTMOutputEntry
