import ReversibleCounterProgram

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

def CounterCfg.appendOutput (s : CounterCfg R L) (ys : List Bool) : CounterCfg R L :=
  ⟨s.pc,s.counters,s.output++ys⟩

theorem CounterInstr.eval_appendOutput (i : CounterInstr R L) (s : CounterCfg R L) (ys : List Bool) :
    i.eval (s.appendOutput ys)=(i.eval s).appendOutput ys := by
  cases i <;> simp [CounterInstr.eval,CounterCfg.appendOutput]
  split_ifs <;> simp_all

/-- A printing run is independent of the already printed suffix, including its exact instruction count. -/
theorem CounterRun.appendOutput (code : L → CounterInstr R L) {s t : CounterCfg R L} {k : Nat}
    (h : CounterRun code s k t) (ys : List Bool) :
    CounterRun code (s.appendOutput ys) k (t.appendOutput ys) := by
  induction h with
  | refl => exact CounterRun.refl _
  | @next s t k l hl rest ih =>
    apply CounterRun.next (l := l)
    · exact hl
    · rw [CounterInstr.eval_appendOutput]
      exact ih

end ShiReversibleGenerator
