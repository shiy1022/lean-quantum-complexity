import «AMPUNI-copy-stage-with-skip-mirror-chain»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop

def copyParserLabel (copy : Fin 3) (l : TopLabel) : Label :=
  oldLabel (ShiTMCopyStage.parserLabel copy l)

/-- Away from circuit-parser exit, the corrected copy controller executes the
same instruction as the already-proved retained top-level parser. -/
theorem parser_nonterminal_step (copy : Fin 3)
    (l : TopLabel) (hl : l ≠ (.inl (.inr .exit) : TopLabel))
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (copyParserLabel copy l), v, S⟩) =
      (topRun (some ⟨some l, v, S⟩)).map
        (liftCfg (copyParserLabel copy)) := by
  have h₁ := stepAux_liftStmt oldLabel
    (ShiTMCopyStage.liftStmt (ShiTMCopyStage.parserLabel copy)
      (topMachine l)) v S
  have h₂ := ShiTMCopyStage.stepAux_liftStmt
    (ShiTMCopyStage.parserLabel copy) (topMachine l) v S
  have h : stepAux
      (liftStmt oldLabel (ShiTMCopyStage.liftStmt
        (ShiTMCopyStage.parserLabel copy) (topMachine l))) v S =
      liftCfg (copyParserLabel copy) (stepAux (topMachine l) v S) := by
    rw [h₁, h₂]
    cases hc : stepAux (topMachine l) v S with
    | mk label value T =>
        cases label <;> rfl
  simpa [run, machine, copyParserLabel, oldLabel,
    ShiTMCopyStage.parserLabel, ShiTMCopyStage.machine,
    hl, topRun, step, liftStmt] using congrArg some h

private theorem iterate_none {A : Type}
    (smallRun : Option (Cfg TopGam A Sig) → Option (Cfg TopGam A Sig))
    (hNone : smallRun none = none) (n : Nat) :
    smallRun^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, hNone]
      exact ih

private theorem iterate_halted {A : Type}
    (smallRun : Option (Cfg TopGam A Sig) → Option (Cfg TopGam A Sig))
    (hNone : smallRun none = none)
    (hHalt : ∀ (v : Sig) (S : ∀ k, List (TopGam k)),
      smallRun (some ⟨none, v, S⟩) = none)
    (n : Nat) (v : Sig) (S : ∀ k, List (TopGam k)) :
    smallRun^[n + 1] (some ⟨none, v, S⟩) = none := by
  rw [show n + 1 = Nat.succ n by omega,
    Function.iterate_succ_apply, hHalt]
  exact iterate_none smallRun hNone n

/-- A finite parser run that first reaches exit lifts to the enclosing copy
controller; the controller's exit transition itself remains available for the
next replay cycle. -/
theorem parser_run_lift (copy : Fin 3) (n : Nat)
    (c : Option (Cfg TopGam TopLabel Sig))
    (d : Cfg TopGam TopLabel Sig)
    (hd : d.l = some (.inl (.inr .exit)))
    (hrun : topRun^[n] c = some d) :
    run^[n] (c.map (liftCfg (copyParserLabel copy))) =
      some (liftCfg (copyParserLabel copy) d) := by
  induction n generalizing c with
  | zero => simpa using congrArg (Option.map (liftCfg
      (copyParserLabel copy))) hrun
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      cases c with
      | none =>
          rw [show topRun none = none by rfl,
            iterate_none topRun rfl] at hrun
          cases hrun
      | some cfg =>
          cases cfg with
          | mk l v S =>
              cases l with
              | none =>
                  rw [show topRun (some ⟨none, v, S⟩) = none by rfl,
                    iterate_none topRun rfl] at hrun
                  cases hrun
              | some l =>
                  by_cases hl : l = (.inl (.inr .exit) : TopLabel)
                  · subst l
                    have hterminal : topRun
                        (some ⟨some (.inl (.inr .exit)), v, S⟩) =
                        some ⟨none, v, S⟩ := by rfl
                    rw [hterminal] at hrun
                    cases n with
                    | zero =>
                        simp only [Function.iterate_zero, id_eq] at hrun
                        have heq := congrArg Cfg.l (Option.some.inj hrun)
                        simp [hd] at heq
                    | succ n =>
                        rw [iterate_halted topRun rfl (by intros; rfl)
                          n v S] at hrun
                        cases hrun
                  · simp only [Option.map_some]
                    change run^[n]
                      (run (some ⟨some (copyParserLabel copy l), v, S⟩)) =
                        some (liftCfg (copyParserLabel copy) d)
                    rw [parser_nonterminal_step copy l hl v S]
                    exact ih (topRun (some ⟨some l, v, S⟩)) hrun

end ShiTMCopyStageWithSkip
