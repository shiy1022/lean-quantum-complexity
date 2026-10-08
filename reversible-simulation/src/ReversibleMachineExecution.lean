import ReversibleMachineTrace

set_option autoImplicit false

namespace ShiReversibleTM

def liftedStep (tm : Turing.FinTM2) (c : Option tm.Cfg) : Option tm.Cfg := c.bind tm.step

theorem tick_of_step (tm : Turing.FinTM2) (c d : tm.Cfg) (h : tm.step c = some d) :
    tick tm c = d := by
  cases c with
  | mk l v S =>
    cases l with
    | none => simp [Turing.FinTM2.step, Turing.TM2.step] at h
    | some l =>
      apply Option.some.inj
      exact h

theorem advance_of_steps (tm : Turing.FinTM2) (t : Nat) (c d : tm.Cfg)
    (h : (liftedStep tm)^[t] (some c) = some d) : advance tm t c = d := by
  induction t generalizing d with
  | zero => simpa [advance] using h
  | succ t ih =>
    rw [Function.iterate_succ_apply'] at h
    cases he : (liftedStep tm)^[t] (some c) with
    | none => simp [he, liftedStep, Option.bind] at h
    | some e =>
      have hh := ih e he
      have hs : tm.step e = some d := by simpa [he, liftedStep, Option.bind] using h
      simpa [advance, hh] using tick_of_step tm e d hs

theorem advance_add (tm : Turing.FinTM2) (a b : Nat) (c : tm.Cfg) :
    advance tm (a + b) c = advance tm b (advance tm a c) := by
  induction b with
  | zero => simp [advance]
  | succ b ih => simp [advance, Nat.add_succ, ih]

/-- A real Mathlib run certificate yields the same output at the padded clock budget. -/
theorem advance_of_outputs (tm : Turing.FinTM2) (xs : List (tm.Γ tm.k₀))
    (ys : List (tm.Γ tm.k₁)) (budget : Nat)
    (h : Turing.TM2OutputsInTime tm xs (some ys) budget) :
    advance tm budget (Turing.initList tm xs) = Turing.haltList tm ys := by
  have he : advance tm h.steps (Turing.initList tm xs) = Turing.haltList tm ys :=
    advance_of_steps tm h.steps _ _ h.evals_in_steps
  calc
    advance tm budget (Turing.initList tm xs) =
        advance tm (budget - h.steps) (advance tm h.steps (Turing.initList tm xs)) := by
      rw [← advance_add, Nat.add_sub_of_le h.steps_le_m]
    _ = Turing.haltList tm ys := by
      rw [he]
      exact advance_halted tm _ _ rfl

theorem polyTime_padded_run {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) f) (xs : List Bool) :
    advance M.tm (M.time.eval xs.length)
        (Turing.initList M.tm (xs.map M.inputAlphabet.invFun)) =
      Turing.haltList M.tm ((f xs).map M.outputAlphabet.invFun) :=
  advance_of_outputs M.tm _ _ _ (M.outputsFun xs)

end ShiReversibleTM
