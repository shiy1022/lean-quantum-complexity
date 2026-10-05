import «AMPUNI-complete-copy-encodings»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCompleteController

open ShiTMLayoutMachine ShiTMRetainedTop

/-- The forward bit string represented by the completed three-pass controller.
This is an intermediate format: each copy still carries its own circuit-depth
prefix, and the fixed fanout and readout blocks are not yet inserted. -/
def intermediateBits (F : ShiClassQMA.QMAFamily) (n : Nat) : PvsNP.Str :=
  ShiBQP.encNat (3 * F.wit n) ++
    ShiBQP.encNat (2 * n + 3 * F.anc n + 3) ++
    ShiBQP.encNat (3 * n + 3 * F.wit n + 3 * F.anc n + 3) ++
    ShiTMRawLayout.encodeCirc
      (ShiTMRawLayout.mapCirc depth
        (ShiTMRawLayout.ampPieces n (F.wit n) (F.anc n)) 0
        ((F.circ n).map (List.map ShiTMRawLayout.ofInstr))) ++
    ShiTMRawLayout.encodeCirc
      (ShiTMRawLayout.mapCirc depth
        (ShiTMPieceController.expectedPieces 1 n (F.wit n) (F.anc n)) 0
        ((F.circ n).map (List.map ShiTMRawLayout.ofInstr))) ++
    ShiTMRawLayout.encodeCirc
      (ShiTMRawLayout.mapCirc depth
        (ShiTMPieceController.expectedPieces 2 n (F.wit n) (F.anc n)) 0
        ((F.circ n).map (List.map ShiTMRawLayout.ofInstr)))

/-- The single finite controller reaches its terminal label with precisely the
reversal of `intermediateBits` on the output accumulator. -/
theorem full_three_pass_forward_output (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ∃ (R : ∀ k, List (TopGam k)) (steps : Nat),
      run^[steps]
        (some (Turing.initList finiteMachine
          ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit))) =
        some ⟨some (copyLabel
          (ShiTMCopyStageWithSkip.oldLabel ShiTMCopyStage.doneLabel)),
          none, R⟩
      ∧ R (.inl (.inl (13 : Fin 14))) =
          ((intermediateBits F n).map bit).reverse := by
  obtain ⟨R, steps, hrun, hacc, _, _, _, _⟩ := full_three_pass_run F n
  refine ⟨R, steps, hrun, ?_⟩
  rw [hacc]
  simp only [intermediateBits, numericBytes, firstCopyBytes,
    ShiTMCopyStageWithSkip.copyBytes, List.map_append, List.reverse_append,
    List.append_assoc]

end ShiTMCompleteController
