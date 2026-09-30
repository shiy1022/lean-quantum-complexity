import «AMPUNI-piece-controller-work-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

def tableState (S : ∀ k, List (TopGam k)) : TableState :=
  (S (.inl (.inl (1 : Fin 14))), S (.inl (.inl (2 : Fin 14))))

/-- Executing a retained-field command has the same width/base effect as the
pure command interpreter. The retained source and empty scratch are preserved. -/
theorem dispatch_field_tables (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (n wit anc : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hcommand : commandAt (program copy) pc.val = some (.add table atom))
    (hone : atom ≠ .one)
    (hsource : S (.inr (source atom)) =
      List.replicate (value n wit anc atom) Cell.mark)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)),
      run^[2 * value n wit anc atom + 4]
        (some { l := some (.dispatch copy pc), var := v, stk := S }) =
          some { l := some (.dispatch copy (nextPC pc)), var := none, stk := U }
      ∧ tableState U = commandStep n wit anc (.add table atom) (tableState S)
      ∧ U (.inr (source atom)) =
          List.replicate (value n wit anc atom) Cell.mark
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, j ≠ .inr (source atom) →
          j ≠ .inl (.inl (destination table)) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  obtain ⟨U, hrun, hsrc, hdest, hscratch', hframe⟩ :=
    dispatch_field_run copy pc atom table (value n wit anc atom) v S
      hcommand hone hsource hscratch
  refine ⟨U, hrun, ?_, hsrc, hscratch', hframe⟩
  cases table with
  | width =>
      have hbase : U (.inl (.inl (2 : Fin 14))) =
          S (.inl (.inl (2 : Fin 14))) := by
        exact hframe _ (by simp) (by decide) (by decide)
      change
        (U (.inl (.inl (1 : Fin 14))), U (.inl (.inl (2 : Fin 14)))) =
          (List.replicate (value n wit anc atom) Cell.mark ++
            S (.inl (.inl (1 : Fin 14))), S (.inl (.inl (2 : Fin 14))))
      exact Prod.ext (by simpa [destination] using hdest) hbase
  | base =>
      have hwidth : U (.inl (.inl (1 : Fin 14))) =
          S (.inl (.inl (1 : Fin 14))) := by
        exact hframe _ (by simp) (by decide) (by decide)
      change
        (U (.inl (.inl (1 : Fin 14))), U (.inl (.inl (2 : Fin 14)))) =
          (S (.inl (.inl (1 : Fin 14))),
            List.replicate (value n wit anc atom) Cell.mark ++
              S (.inl (.inl (2 : Fin 14))))
      exact Prod.ext hwidth (by simpa [destination] using hdest)

end ShiTMPieceController
