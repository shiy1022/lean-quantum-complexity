import «AMPUNI-replay-mark-split-run»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMReplayMarkSplit

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOutputEntry

/-- The saved-input shape proved for the first circuit pass is exactly the
input expected by the mark-splitting controller. -/
theorem first_pass_to_split
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
    (harchive : S archive =
      Cell.mirrorEnd ::
        ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse)
    (hentry : ShiTMOutputEntry.run^[entryCost F n]
      (some { l := some (headerLabel .inputLength), var := v, stk := S }) =
        some ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, U⟩)
    (hpass : ShiTMOutputEntry.run^[steps]
      (some ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, U⟩) =
        some ⟨some (parserLabel (.inl (.inr .exit))), none, V⟩) :
    ∃ W : ∀ j, List (TopGam j),
      run^[(F.out n : Nat) + 1]
        (some { l := some false, var := none, stk := V }) =
          some { l := some true, var := some Cell.mirrorEnd, stk := W }
      ∧ W archive =
          ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse
      ∧ W marks = List.replicate (F.out n : Nat) Cell.mark ++ V marks
      ∧ ∀ j : TopK, j ≠ archive → j ≠ marks → W j = V j := by
  have hVarchive := first_pass_archive_frame F n S U V steps v hsrc
    hret0 hret1 hret2 h13 h3 h1 h2 h8 h9 h10 hentry hpass
  rw [harchive] at hVarchive
  exact split_all_run (F.out n : Nat)
    ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse
    none V hVarchive

end ShiTMReplayMarkSplit
