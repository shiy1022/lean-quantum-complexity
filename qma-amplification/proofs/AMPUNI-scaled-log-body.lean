import «AMPUNI-scaled-log-run»
import «AMPUNI-terminal-exception»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2 ShiTMUnaryLog
namespace ShiTMScaledLogBody

def machine (copies offset : Nat) (l : Label) :
    Stmt Gam Label State :=
  if l = .done then .halt else ShiTMScaledLog.machine copies offset l

abbrev run (copies offset : Nat) :=
  ShiTMSubroutine.run (machine copies offset)

private def terminal (c : Option (Cfg Gam Label State)) : Prop :=
  ∃ v S, c = some ⟨some .done, v, S⟩

private def closed (c : Option (Cfg Gam Label State)) : Prop :=
  c = none ∨ ∃ v S, c = some ⟨none, v, S⟩

private theorem done_l_none (copies offset : Nat)
    (v : State) (S : ∀ k, List (Gam k)) :
    (stepAux (ShiTMScaledLog.machine copies offset .done) v S).l =
      none := by
  have hpush (k : Nat) (v : State)
      (S : ∀ j, List (Gam j)) :
      (stepAux (ShiTMScaledLog.pushCounter k .halt) v S).l =
        none := by
    induction k generalizing S with
    | zero => rfl
    | succ k ih =>
        exact ih (Function.update S .counter (true :: S .counter))
  exact hpush offset (none, true) S

private theorem closed_after_done (copies offset : Nat)
    (c : Option (Cfg Gam Label State)) (hc : terminal c) :
    closed (ShiTMScaledLog.run copies offset c) := by
  obtain ⟨v, S, rfl⟩ := hc
  right
  cases hcfg : stepAux
      (ShiTMScaledLog.machine copies offset .done) v S with
  | mk l v' S' =>
      have hl : l = none := by
        simpa [hcfg] using done_l_none copies offset v S
      subst l
      refine ⟨v', S', ?_⟩
      simp [ShiTMScaledLog.run, ShiTMSubroutine.run, step, hcfg]

private theorem closed_stays (copies offset : Nat)
    (c : Option (Cfg Gam Label State)) (hc : closed c) :
    closed (ShiTMScaledLog.run copies offset c) := by
  rcases hc with rfl | ⟨v, S, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl

private theorem closed_disjoint
    (c : Option (Cfg Gam Label State)) (hc : closed c) :
    ¬ terminal c := by
  intro ht
  rcases ht with ⟨v, S, hv⟩
  rcases hc with h | ⟨v', S', h⟩
  · simp [h] at hv
  · simp [h] at hv

private theorem agree_except_done (copies offset : Nat)
    (c : Option (Cfg Gam Label State)) (hc : ¬ terminal c) :
    run copies offset c = ShiTMScaledLog.run copies offset c := by
  cases c with
  | none => rfl
  | some c =>
      rcases c with ⟨l, v, S⟩
      cases l with
      | none => rfl
      | some l =>
          by_cases h : l = .done
          · subst l
            exact False.elim (hc ⟨v, S, rfl⟩)
          · simp [run, machine, h, ShiTMScaledLog.run,
              ShiTMSubroutine.run, step]

/-- The scaled machine's whole run never executes its `.done` statement
before reaching the active `.done` label. Thus its exact run also holds
when `.done` is treated as a return label. -/
theorem full_run (copies offset n : Nat) (b : Bool)
    (v : Option Bool) (ctr : List Bool) :
    ∃ direction parity : Bool,
      (run copies offset)^[ShiTMUnaryLogCost.work n]
        (some (cfg (.scan b) b v true
          (List.replicate n true) [] ctr)) =
      some (cfg .done direction none parity [] []
        (List.replicate (copies * Nat.log 2 n) true ++ ctr)) := by
  obtain ⟨direction, parity, h⟩ :=
    ShiTMScaledLog.full_run copies offset n b v ctr
  refine ⟨direction, parity, ?_⟩
  have hn : ∀ c, terminal c → ∀ k, 0 < k →
      ¬ terminal ((ShiTMScaledLog.run copies offset)^[k] c) :=
    ShiTMTerminalException.no_return_of_closed
      (ShiTMScaledLog.run copies offset) terminal closed
      (closed_after_done copies offset)
      (closed_stays copies offset) closed_disjoint
  have ht : terminal
      ((ShiTMScaledLog.run copies offset)^[ShiTMUnaryLogCost.work n]
        (some (cfg (.scan b) b v true
          (List.replicate n true) [] ctr))) := by
    rw [h]
    exact ⟨_, _, rfl⟩
  exact (ShiTMTerminalException.iterate_agree_until_terminal
    (run copies offset) (ShiTMScaledLog.run copies offset)
    terminal (agree_except_done copies offset) hn
    _ _ ht).trans h

end ShiTMScaledLogBody
