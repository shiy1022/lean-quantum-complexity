import ReversibleCounterProgram
import ReversibleMachineExecution

set_option autoImplicit false
namespace ShiReversibleGenerator
open Turing.TM2 ShiReversibleTM

variable {R L : Type} [Fintype R] [DecidableEq R] [Fintype L]

/-- `none` is the Boolean output stack; `some r` is a unary counter stack. -/
def CounterInstr.compile : CounterInstr R L → Stmt (fun _ : Option R => Bool) L Bool
  | .inc r next => .push (some r) (fun _ => true) (.goto (fun _ => next))
  | .dec r next => .pop (some r) (fun v _ => v) (.goto (fun _ => next))
  | .branch r zero nonzero => .peek (some r) (fun _ a => a.isNone)
      (.branch id (.goto (fun _ => zero)) (.goto (fun _ => nonzero)))
  | .emit b next => .push none (fun _ => b) (.goto (fun _ => next))
  | .halt => .load (fun _ => false) .halt

noncomputable abbrev counterMachine (code : L → CounterInstr R L) (input : R) (main : L) : Turing.FinTM2 where
  K := Option R
  k₀ := some input
  k₁ := none
  Γ _ := Bool
  Λ := L
  main := main
  σ := Bool
  initialState := false
  m l := (code l).compile

def CounterCfg.Denotes (s : CounterCfg R L)
    (c : Cfg (fun _ : Option R => Bool) L Bool) : Prop :=
  c.l = s.pc ∧ (∀ r, (c.stk (some r)).length = s.counters r) ∧
    c.stk none = s.output ∧ (c.l = none → c.var = false)

theorem compile_step_denotes (instr : CounterInstr R L) (s : CounterCfg R L)
    (c : Cfg (fun _ : Option R => Bool) L Bool) (h : s.Denotes c) :
    (instr.eval s).Denotes (stepAux instr.compile c.var c.stk) := by
  rcases h with ⟨hl, hc, ho, hv⟩
  cases instr with
  | inc r next =>
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = r
      · subst j; simp [CounterInstr.compile, CounterInstr.eval, hc]
      · simp [CounterInstr.compile, CounterInstr.eval, Function.update_of_ne hj, hc, hj]
    · simpa [CounterInstr.compile, CounterInstr.eval] using ho
    · simp [CounterInstr.compile]
  | dec r next =>
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = r
      · subst j; simp [CounterInstr.compile, CounterInstr.eval, hc]
      · simp [CounterInstr.compile, CounterInstr.eval, Function.update_of_ne hj, hc, hj]
    · simpa [CounterInstr.compile, CounterInstr.eval] using ho
    · simp [CounterInstr.compile]
  | branch r zero nonzero =>
    have he : (c.stk (some r)).head?.isNone = decide (s.counters r = 0) := by
      rw [← hc r]
      cases (c.stk (some r)) <;> simp
    simp only [CounterInstr.compile, stepAux, he, CounterInstr.eval]
    by_cases hz : s.counters r = 0
    · simpa [CounterCfg.Denotes, hz] using And.intro hc ho
    · simpa [CounterCfg.Denotes, hz] using And.intro hc ho
  | emit b next =>
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro j; simpa [CounterInstr.compile, CounterInstr.eval] using hc j
    · simpa [CounterInstr.compile, CounterInstr.eval] using congrArg (List.cons b) ho
    · simp [CounterInstr.compile]
  | halt =>
    exact ⟨rfl, hc, ho, fun _ => rfl⟩

theorem counterMachine_initial (code : L → CounterInstr R L) (input : R) (main : L) (xs : List Bool) :
    (⟨some main, Function.update (fun _ : R => 0) input xs.length, []⟩ : CounterCfg R L).Denotes
      (Turing.initList (counterMachine code input main) xs) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro r
    by_cases hr : r = input
    · subst r; simp [Turing.initList, counterMachine] <;> rfl
    · simp [Turing.initList, counterMachine, hr, Function.update_of_ne hr]
  · simp [Turing.initList, counterMachine]
  · simp [Turing.initList, counterMachine]

/-- A counted source run supplies the same number of actual TM2 steps. -/
theorem CounterRun.compile (code : L → CounterInstr R L) (input : R) (main : L)
    {s d : CounterCfg R L} {t : Nat} (h : CounterRun code s t d)
    (c : (counterMachine code input main).Cfg) (hc : s.Denotes c) :
    ∃ e : (counterMachine code input main).Cfg,
      (liftedStep (counterMachine code input main))^[t] (some c) = some e ∧ d.Denotes e := by
  induction h generalizing c with
  | refl => exact ⟨c, rfl, hc⟩
  | @next s d t l hl rest ih =>
    let c' : (counterMachine code input main).Cfg := stepAux (code l).compile c.var c.stk
    have hs : (counterMachine code input main).step c = some c' := by
      cases c with
      | mk lab v S =>
        have hlab : lab = some l := hc.1.trans hl
        change Turing.TM2.step (fun l => (code l).compile) ⟨lab, v, S⟩ = some c'
        rw [hlab]
        rfl
    obtain ⟨e, he, hd⟩ := ih c' (compile_step_denotes (code l) s c hc)
    refine ⟨e, ?_, hd⟩
    have hs' : liftedStep (counterMachine code input main) (some c) = some c' := by
      change (counterMachine code input main).step c = some c'
      exact hs
    rw [Function.iterate_succ_apply, hs']
    exact he

theorem denotes_halted (code : L → CounterInstr R L) (input : R) (main : L)
    (s : CounterCfg R L) (c : (counterMachine code input main).Cfg)
    (h : s.Denotes c) (hp : s.pc = none) (hz : ∀ r, s.counters r = 0) :
    c = Turing.haltList (counterMachine code input main) s.output := by
  have hl : c.l = none := h.1.trans hp
  have hv := h.2.2.2 hl
  have hs : c.stk = fun k : Option R => if k = none then s.output else [] := by
    funext k
    cases k with
    | none => exact h.2.2.1
    | some r => exact List.eq_nil_of_length_eq_zero ((h.2.1 r).trans (hz r))
  cases c
  simp_all [Turing.haltList, counterMachine]
  congr 1

/-- Counted counter-program execution yields Mathlib's actual timed machine certificate. -/
theorem counterRun_outputs (code : L → CounterInstr R L) (input : R) (main : L)
    (xs ys : List Bool) (steps : Nat) (d : CounterCfg R L)
    (h : CounterRun code ⟨some main, Function.update (fun _ : R => 0) input xs.length, []⟩ steps d)
    (hp : d.pc = none) (hz : ∀ r, d.counters r = 0) (ho : d.output = ys) :
    Nonempty (Turing.TM2OutputsInTime (counterMachine code input main) xs (some ys) steps) := by
  obtain ⟨c, he, hc⟩ := h.compile code input main _ (counterMachine_initial code input main xs)
  have hf : c = Turing.haltList (counterMachine code input main) ys := by
    rw [← ho]
    exact denotes_halted code input main d c hc hp hz
  rw [hf] at he
  exact ⟨{ steps := steps, evals_in_steps := he, steps_le_m := le_rfl }⟩

/-- A source polynomial run bound is transported to a genuine finite-machine certificate. -/
theorem counterProgram_polytime (code : L → CounterInstr R L) (input : R) (main : L)
    (f : List Bool → List Bool) (p : Polynomial Nat)
    (h : ∀ xs, ∃ steps d,
      CounterRun code ⟨some main, Function.update (fun _ : R => 0) input xs.length, []⟩ steps d ∧
      d.pc = none ∧ (∀ r, d.counters r = 0) ∧ d.output = f xs ∧ steps ≤ p.eval xs.length) :
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) := by
  classical
  choose steps d hr hp hz ho ht using h
  refine ⟨{
    tm := counterMachine code input main
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := p
    outputsFun := ?_ }⟩
  intro xs
  let run := Classical.choice (counterRun_outputs code input main xs (f xs)
    (steps xs) (d xs) (hr xs) (hp xs) (hz xs) (ho xs))
  exact {
    steps := run.steps
    evals_in_steps := by
      change (liftedStep (counterMachine code input main))^[run.steps]
        (some (Turing.initList (counterMachine code input main) (xs.map (id : Bool → Bool)))) =
        some (Turing.haltList (counterMachine code input main) ((f xs).map (id : Bool → Bool)))
      rw [List.map_id, List.map_id]
      exact run.evals_in_steps
    steps_le_m := run.steps_le_m.trans (ht xs) }

end ShiReversibleGenerator
