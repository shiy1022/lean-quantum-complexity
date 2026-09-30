import «AMPUNI-output-entry-full-run»
import «AMPUNI-output-nested-header-frame»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController

/-- The first typed circuit pass does not consume the three retained unary
parameters created by the length-aware entry scanner. -/
theorem first_pass_retained
    (F : ShiClassQMA.QMAFamily) (n : Nat) (v : Sig)
    (S U V : ∀ k, List (TopGam k)) (steps : Nat)
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
      (some ⟨some (headerLabel .inputLength), v, S⟩) =
        some ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, U⟩)
    (hpass : run^[steps]
      (some ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, U⟩) =
        some ⟨some (parserLabel (.inl (.inr .exit))), none, V⟩) :
    Retained n (F.wit n) (F.anc n) V := by
  obtain ⟨W, hentryW, _, _, _, _, hWret, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    full_entry_run F n [] v S (by simpa using hsrc)
      hret0 hret1 hret2 h13 h3 h1 h2 h8 h9 h10
  have hentryW' : run^[entryCost F n]
      (some ⟨some (headerLabel .inputLength), v, S⟩) =
        some ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, W⟩ := by
    simpa [parserLabel, bodyLabel, ShiTMOutputStage.stageLabel] using hentryW
  have hWU : W = U := by
    have h := hentryW'.symm.trans hentry
    exact congrArg Cfg.stk (Option.some.inj h)
  rw [hWU] at hWret
  rcases hWret with ⟨h0, h1, h2⟩
  exact ⟨
    (nested_run_preserves_header (.inr .circuitHeader) none none
      (some (parserLabel (.inl (.inr .exit))) ) U V steps hpass 0).trans h0,
    (nested_run_preserves_header (.inr .circuitHeader) none none
      (some (parserLabel (.inl (.inr .exit))) ) U V steps hpass 1).trans h1,
    (nested_run_preserves_header (.inr .circuitHeader) none none
      (some (parserLabel (.inl (.inr .exit))) ) U V steps hpass 2).trans h2⟩

end ShiTMOutputEntry
