import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- A finite control language for unary-counter printing programs. -/
inductive CounterInstr (R L : Type) where
  | inc : R → L → CounterInstr R L
  | dec : R → L → CounterInstr R L
  | branch : R → L → L → CounterInstr R L
  | emit : Bool → L → CounterInstr R L
  | halt : CounterInstr R L

@[ext] structure CounterCfg (R L : Type) where
  pc : Option L
  counters : R → Nat
  output : List Bool

def CounterInstr.eval {R L : Type} [DecidableEq R] : CounterInstr R L → CounterCfg R L → CounterCfg R L
  | .inc r next, s => ⟨some next, Function.update s.counters r (s.counters r + 1), s.output⟩
  | .dec r next, s => ⟨some next, Function.update s.counters r (s.counters r - 1), s.output⟩
  | .branch r zero nonzero, s => ⟨some (if s.counters r = 0 then zero else nonzero), s.counters, s.output⟩
  | .emit b next, s => ⟨some next, s.counters, b :: s.output⟩
  | .halt, s => ⟨none, s.counters, s.output⟩

/-- Count actual control instructions; stepping a halted state is excluded. -/
inductive CounterRun {R L : Type} [DecidableEq R] (code : L → CounterInstr R L) :
    CounterCfg R L → Nat → CounterCfg R L → Prop where
  | refl (s) : CounterRun code s 0 s
  | next {s d t l} (hl : s.pc = some l) (rest : CounterRun code ((code l).eval s) t d) :
      CounterRun code s (t + 1) d

theorem CounterRun.trans {R L : Type} [DecidableEq R] (code : L → CounterInstr R L)
    {s d e : CounterCfg R L} {t u : Nat} (h : CounterRun code s t d) (g : CounterRun code d u e) :
    CounterRun code s (t + u) e := by
  induction h with
  | refl => simpa using g
  | next hl rest ih =>
    have hnext := CounterRun.next hl (ih g)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext

theorem CounterRun.one {R L : Type} [DecidableEq R] (code : L → CounterInstr R L)
    (s : CounterCfg R L) (l : L) (hl : s.pc = some l) :
    CounterRun code s 1 ((code l).eval s) := CounterRun.next hl (CounterRun.refl _)

end ShiReversibleGenerator
