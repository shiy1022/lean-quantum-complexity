import ReversibleCounterProgram

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L L' : Type} [DecidableEq R]

def CounterInstr.relabel (f : L → L') : CounterInstr R L → CounterInstr R L'
  | .inc r l => .inc r (f l)
  | .dec r l => .dec r (f l)
  | .branch r l m => .branch r (f l) (f m)
  | .emit b l => .emit b (f l)
  | .halt => .halt

def CounterCfg.relabel (f : L → L') (s : CounterCfg R L) : CounterCfg R L' :=
  ⟨s.pc.map f, s.counters, s.output⟩

@[simp] theorem CounterInstr.eval_relabel (f : L → L') (instr : CounterInstr R L) (s : CounterCfg R L) :
    (instr.relabel f).eval (s.relabel f) = (instr.eval s).relabel f := by
  cases instr <;> simp [CounterInstr.relabel, CounterInstr.eval, CounterCfg.relabel]
  split <;> rfl

/-- Inclusion in a larger finite control graph preserves the exact instruction count. -/
theorem CounterRun.relabel (code : L → CounterInstr R L) (code' : L' → CounterInstr R L')
    (f : L → L') (hf : ∀ l, code' (f l) = (code l).relabel f)
    {s t : CounterCfg R L} {k : Nat} (h : CounterRun code s k t) :
    CounterRun code' (s.relabel f) k (t.relabel f) := by
  induction h with
  | refl => exact CounterRun.refl _
  | @next s t k l hl rest ih =>
    apply CounterRun.next (l := f l)
    · simp [CounterCfg.relabel, hl]
    · rw [hf, CounterInstr.eval_relabel]
      exact ih

end ShiReversibleGenerator
