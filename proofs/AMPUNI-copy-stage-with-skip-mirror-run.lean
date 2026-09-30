import «AMPUNI-copy-stage-with-skip-mirror-step»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop

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

private theorem lift_to_terminal {A : Type}
    (smallRun : Option (Cfg TopGam A Sig) → Option (Cfg TopGam A Sig))
    (f : A → Label) (terminal : A)
    (hNone : smallRun none = none)
    (hHalt : ∀ (v : Sig) (S : ∀ k, List (TopGam k)),
      smallRun (some ⟨none, v, S⟩) = none)
    (hTerminal : ∀ (v : Sig) (S : ∀ k, List (TopGam k)),
      smallRun (some ⟨some terminal, v, S⟩) = some ⟨none, v, S⟩)
    (hStep : ∀ (l : A) (v : Sig) (S : ∀ k, List (TopGam k)),
      l ≠ terminal →
      run (some (liftCfg f ⟨some l, v, S⟩)) =
        (smallRun (some ⟨some l, v, S⟩)).map (liftCfg f))
    (n : Nat) (c : Option (Cfg TopGam A Sig))
    (d : Cfg TopGam A Sig) (hd : d.l = some terminal)
    (hrun : smallRun^[n] c = some d) :
    run^[n] (c.map (liftCfg f)) = some (liftCfg f d) := by
  induction n generalizing c with
  | zero => simpa using congrArg (Option.map (liftCfg f)) hrun
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      cases c with
      | none =>
          rw [hNone, iterate_none smallRun hNone] at hrun
          cases hrun
      | some cfg =>
          cases cfg with
          | mk l v S =>
              cases l with
              | none =>
                  rw [hHalt, iterate_none smallRun hNone] at hrun
                  cases hrun
              | some l =>
                  by_cases hl : l = terminal
                  · subst l
                    rw [hTerminal] at hrun
                    cases n with
                    | zero =>
                        simp only [Function.iterate_zero, id_eq] at hrun
                        have heq := congrArg Cfg.l (Option.some.inj hrun)
                        simp [hd] at heq
                    | succ n =>
                        rw [iterate_halted smallRun hNone hHalt n v S] at hrun
                        cases hrun
                  · simp only [Option.map_some]
                    rw [hStep l v S hl]
                    exact ih (smallRun (some ⟨some l, v, S⟩)) hrun

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- Build both mirror tables in the corrected finite controller, then enter
the original circuit parser. -/
theorem mirror_run_to_parser (copy : Fin 3)
    (widths bases : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hwidth : S (.inl (.inl (1 : Fin 14))) = widths)
    (hbase : S (.inl (.inl (2 : Fin 14))) = bases)
    (hm8 : S (.inl (.inl (8 : Fin 14))) = [])
    (hm9 : S (.inl (.inl (9 : Fin 14))) = [])
    (hscratch : S (.inl (.inl (10 : Fin 14))) = []) :
    ∃ U : ∀ k, List (TopGam k),
      run^[(2 * widths.length + 3) + (2 * bases.length + 3) + 1]
        (some ⟨some (oldLabel (ShiTMCopyStage.mirrorLabel copy
          .startWidth)), v, S⟩) =
        some ⟨some (oldLabel (ShiTMCopyStage.parserLabel copy
          (.inl (.inr .circuitHeader)))), none, U⟩
      ∧ U (.inl (.inl (1 : Fin 14))) = widths
      ∧ U (.inl (.inl (2 : Fin 14))) = bases
      ∧ U (.inl (.inl (8 : Fin 14))) = widths.reverse ++ [Cell.mirrorEnd]
      ∧ U (.inl (.inl (9 : Fin 14))) = bases.reverse ++ [Cell.mirrorEnd]
      ∧ U (.inl (.inl (10 : Fin 14))) = []
      ∧ ∀ j, j ≠ .inl (.inl (1 : Fin 14)) →
          j ≠ .inl (.inl (2 : Fin 14)) →
          j ≠ .inl (.inl (8 : Fin 14)) →
          j ≠ .inl (.inl (9 : Fin 14)) →
          j ≠ .inl (.inl (10 : Fin 14)) → U j = S j := by
  obtain ⟨U, hrun, hUw, hUb, hU8, hU9, hU10, hframe⟩ :=
    ShiTMMirrorInit.both_run widths bases v S
      hwidth hbase hm8 hm9 hscratch
  have hLift : run^[(2 * widths.length + 3) + (2 * bases.length + 3)]
      (some ⟨some (oldLabel (ShiTMCopyStage.mirrorLabel copy
        .startWidth)), v, S⟩) =
        some ⟨some (oldLabel (ShiTMCopyStage.mirrorLabel copy .done)),
          none, U⟩ := by
    have h := lift_to_terminal ShiTMMirrorInit.run
      (fun q => oldLabel (ShiTMCopyStage.mirrorLabel copy q))
      ShiTMMirrorInit.Phase.done
      (by rfl) (by intros; rfl) (by intros; rfl)
      (by intro p v S hp; exact mirror_nonterminal_step copy p hp v S)
      _
      (some ⟨some ShiTMMirrorInit.Phase.startWidth, v, S⟩)
      ⟨some ShiTMMirrorInit.Phase.done, none, U⟩ rfl hrun
    simpa [liftCfg, oldLabel, ShiTMCopyStage.mirrorLabel] using h
  have hnext : run^[1]
      (some ⟨some (oldLabel (ShiTMCopyStage.mirrorLabel copy .done)),
        none, U⟩) =
        some ⟨some (oldLabel (ShiTMCopyStage.parserLabel copy
          (.inl (.inr .circuitHeader)))), none, U⟩ := by
    simpa using mirror_terminal_step copy none U
  exact ⟨U, iterTwo run _ 1 _ _ _ hLift hnext,
    hUw, hUb, hU8, hU9, hU10, hframe⟩

end ShiTMCopyStageWithSkip
