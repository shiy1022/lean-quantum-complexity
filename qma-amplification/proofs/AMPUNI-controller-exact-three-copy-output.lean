import «AMPUNI-intermediate-exact-copies»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMCompleteController

open ShiTMLayoutMachine ShiTMRetainedTop

/-- One finite TM2, started on the ordinary length-aware verifier encoding,
reaches its done label with the exact three embedded verifier-copy circuit
encodings after the three amplified numeric fields. The stack is reversed,
as required by the TM2 output convention. -/
theorem controller_exact_three_copy_output
    (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ∃ (R : ∀ k, List (TopGam k)) (steps : Nat),
      run^[steps]
        (some (Turing.initList finiteMachine
          ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit))) =
        some ⟨some (copyLabel
          (ShiTMCopyStageWithSkip.oldLabel ShiTMCopyStage.doneLabel)),
          none, R⟩
      ∧ R (.inl (.inl (13 : Fin 14))) =
          ((ShiBQP.encNat (3 * F.wit n) ++
            ShiBQP.encNat (2 * n + 3 * F.anc n + 3) ++
            ShiBQP.encNat (3 * n + 3 * F.wit n + 3 * F.anc n + 3) ++
            ShiBQP.encCirc (embeddedCopy0 F n) ++
            ShiBQP.encCirc (embeddedCopy1 F n) ++
            ShiBQP.encCirc (embeddedCopy2 F n)).map bit).reverse := by
  obtain ⟨R, steps, hrun, hout⟩ := full_three_pass_forward_output F n
  refine ⟨R, steps, hrun, ?_⟩
  rw [hout, intermediateBits_exact_copies]

end ShiTMCompleteController
