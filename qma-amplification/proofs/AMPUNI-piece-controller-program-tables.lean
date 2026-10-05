import «AMPUNI-piece-controller-program-run»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

def expectedPieces (copy : Fin 3) (n wit anc : Nat) : List (Nat × Nat) :=
  if copy = 0 then copyPieces0 n wit anc
  else if copy = 1 then copyPieces1 n wit anc
  else copyPieces2 n wit anc

/-- The complete fixed controller program produces the exact piece tables
specified for its copy, not merely an abstract command-interpreter state. -/
theorem run_program_piece_tables (copy : Fin 3) (n wit anc : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig)
      (steps : Nat) (pc' : PC),
      run^[steps]
        (some { l := some (.dispatch copy 0), var := v, stk := S }) =
          some { l := some (.dispatch copy pc'), var := v', stk := U }
      ∧ pc'.val = (program copy).length
      ∧ tableState U =
          (pieceCells Prod.fst (expectedPieces copy n wit anc) ++
            S (.inl (.inl (1 : Fin 14))),
           pieceCells Prod.snd (expectedPieces copy n wit anc) ++
            S (.inl (.inl (2 : Fin 14))))
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = [] := by
  obtain ⟨U, v', steps, pc', hrun, hpc, htable, hretU, hscratchU⟩ :=
    run_program copy n wit anc v S hret hscratch
  refine ⟨U, v', steps, pc', hrun, hpc, ?_, hretU, hscratchU⟩
  fin_cases copy
  · simpa [tableState, expectedPieces] using
      htable.trans (ShiTMPieceSchedule.run_program0 n wit anc
        (S (.inl (.inl (1 : Fin 14))))
        (S (.inl (.inl (2 : Fin 14)))))
  · simpa [tableState, expectedPieces] using
      htable.trans (ShiTMPieceSchedule.run_program1 n wit anc
        (S (.inl (.inl (1 : Fin 14))))
        (S (.inl (.inl (2 : Fin 14)))))
  · simpa [tableState, expectedPieces] using
      htable.trans (ShiTMPieceSchedule.run_program2 n wit anc
        (S (.inl (.inl (1 : Fin 14))))
        (S (.inl (.inl (2 : Fin 14)))))

end ShiTMPieceController
