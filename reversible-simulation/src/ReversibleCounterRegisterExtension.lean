import ReversibleCounterProgram

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R S L : Type}

def CounterInstr.extendRegisters : CounterInstr R L → CounterInstr (R ⊕ S) L
  | .inc r l => .inc (.inl r) l
  | .dec r l => .dec (.inl r) l
  | .branch r l m => .branch (.inl r) l m
  | .emit b l => .emit b l
  | .halt => .halt

def CounterCfg.extendRegisters (extra : S → Nat) (s : CounterCfg R L) : CounterCfg (R ⊕ S) L :=
  ⟨s.pc, Sum.elim s.counters extra, s.output⟩

theorem CounterInstr.eval_extendRegisters [DecidableEq R] [DecidableEq S]
    (instr : CounterInstr R L) (extra : S → Nat) (s : CounterCfg R L) :
    instr.extendRegisters.eval (s.extendRegisters extra) = (instr.eval s).extendRegisters extra := by
  cases instr with
  | inc r l | dec r l =>
      apply CounterCfg.ext
      · rfl
      · funext q; cases q <;>
          simp only [CounterInstr.eval, CounterInstr.extendRegisters, CounterCfg.extendRegisters,
            Sum.elim_inl, Sum.elim_inr, Function.update_apply, Sum.inl.injEq, Sum.inr_ne_inl,
            ite_false]
      · rfl
  | branch r l m => rfl
  | emit b l => rfl
  | halt => rfl

/-- Add finitely many registers without changing a prelude's instructions, cost, or caller state. -/
theorem CounterRun.extendRegisters [DecidableEq R] [DecidableEq S]
    (code : L → CounterInstr R L) (extra : S → Nat)
    {s t : CounterCfg R L} {k : Nat} (h : CounterRun code s k t) :
    CounterRun (fun l => (code l).extendRegisters) (s.extendRegisters extra) k (t.extendRegisters extra) := by
  induction h with
  | refl => exact CounterRun.refl _
  | @next s t k l hl rest ih =>
      apply CounterRun.next (l := l)
      · exact hl
      · rw [CounterInstr.eval_extendRegisters]
        exact ih

theorem CounterCfg.extendRegisters_left (extra : S → Nat) (s : CounterCfg R L) (r : R) :
    (s.extendRegisters extra).counters (.inl r) = s.counters r := rfl

theorem CounterCfg.extendRegisters_right (extra : S → Nat) (s : CounterCfg R L) (r : S) :
    (s.extendRegisters extra).counters (.inr r) = extra r := rfl

end ShiReversibleGenerator
