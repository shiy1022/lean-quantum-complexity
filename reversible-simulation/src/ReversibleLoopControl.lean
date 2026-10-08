import ReversibleCounterLoopReentry
import ReversibleCountedLoop

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R] [DecidableEq L]

/-- Replace two public halt labels by the fixed test/decrement loop control. -/
def reentryCode (code : L → CounterInstr R L) (r : R) (loop pop entry stop : L) :
    L → CounterInstr R L := fun l =>
  if l = loop then .branch r stop pop else if l = pop then .dec r entry else code l

theorem reentryCode_loop (code : L → CounterInstr R L) (r : R) (loop pop entry stop : L) :
    reentryCode code r loop pop entry stop loop = .branch r stop pop := by
  simp [reentryCode]

theorem reentryCode_pop (code : L → CounterInstr R L) (r : R) (loop pop entry stop : L)
    (h : pop ≠ loop) :
    reentryCode code r loop pop entry stop pop = .dec r entry := by
  simp [reentryCode, h]

theorem reentryCode_preserves_run (code : L → CounterInstr R L) (r : R) (loop pop entry stop : L)
    (hl : code loop = .halt) (hp : code pop = .halt)
    {s t : CounterCfg R L} {k : Nat} (h : CounterRun code s k t) (ht : t.pc ≠ none) :
    CounterRun (reentryCode code r loop pop entry stop) s k t := by
  apply CounterRun.modify_halts code _ _ h ht
  intro l hn
  have hnl : l ≠ loop := fun he => hn (he ▸ hl)
  have hnp : l ≠ pop := fun he => hn (he ▸ hp)
  simp [reentryCode, hnl, hnp]

end ShiReversibleGenerator
