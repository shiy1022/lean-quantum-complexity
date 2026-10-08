import ReversibleCounterLoopReentry
import ReversibleCounterRelabel

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L M : Type} [DecidableEq R] [DecidableEq L]

/-- Disjoint finite control graphs share counters and the accumulated output. -/
def disjointCounterCode (left : L → CounterInstr R L) (right : M → CounterInstr R M) :
    L ⊕ M → CounterInstr R (L ⊕ M) :=
  Sum.elim (fun l => (left l).relabel Sum.inl) (fun m => (right m).relabel Sum.inr)

/-- Replacing the first exit with one unconditional branch sequences two fixed graphs. -/
def chainedCounterCode (left : L → CounterInstr R L) (right : M → CounterInstr R M)
    (exit : L) (entry : M) (r : R) : L ⊕ M → CounterInstr R (L ⊕ M) :=
  fun q => match q with
  | .inl l => if l = exit then .branch r (.inr entry) (.inr entry) else (left l).relabel Sum.inl
  | .inr m => (right m).relabel Sum.inr

theorem chainedCounterCode_right (left : L → CounterInstr R L) (right : M → CounterInstr R M)
    (exit : L) (entry : M) (r : R) (m : M) :
    chainedCounterCode left right exit entry r (.inr m) = (right m).relabel Sum.inr := rfl

theorem chainedCounterCode_exit (left : L → CounterInstr R L) (right : M → CounterInstr R M)
    (exit : L) (entry : M) (r : R) :
    chainedCounterCode left right exit entry r (.inl exit) = .branch r (.inr entry) (.inr entry) := by
  simp [chainedCounterCode]

/-- Prefix execution never takes the original halt, so changing that exit preserves its run. -/
theorem chainedCounterCode_left_run (left : L → CounterInstr R L) (right : M → CounterInstr R M)
    (exit : L) (entry : M) (r : R) (hx : left exit = .halt)
    {s t : CounterCfg R L} {count : Nat} (h : CounterRun left s count t) (ht : t.pc ≠ none) :
    CounterRun (chainedCounterCode left right exit entry r)
      (s.relabel Sum.inl) count (t.relabel Sum.inl) := by
  have hl := CounterRun.relabel left (disjointCounterCode left right) Sum.inl (fun _ => rfl) h
  have hf : ∀ q, disjointCounterCode left right q ≠ .halt →
      chainedCounterCode left right exit entry r q = disjointCounterCode left right q := by
    intro q hn
    cases q with
    | inl l =>
        have he : l ≠ exit := by
          intro he
          subst l
          exact hn (by simp [disjointCounterCode, hx, CounterInstr.relabel])
        simp [chainedCounterCode, disjointCounterCode, he]
    | inr m => rfl
  exact CounterRun.modify_halts (disjointCounterCode left right) _ hf hl
    (by simpa [CounterCfg.relabel] using ht)

/-- Actual sequential execution costs both component runs plus one connecting instruction. -/
theorem chainedCounterCode_run (left : L → CounterInstr R L) (right : M → CounterInstr R M)
    (exit : L) (entry : M) (r : R) (hx : left exit = .halt)
    (s : CounterCfg R L) (cs : R → Nat) (ys : List Bool) (t : CounterCfg R M)
    (first second : Nat)
    (hfirst : CounterRun left s first ⟨some exit, cs, ys⟩)
    (hsecond : CounterRun right ⟨some entry, cs, ys⟩ second t) :
    CounterRun (chainedCounterCode left right exit entry r)
      (s.relabel Sum.inl) (first + 1 + second) (t.relabel Sum.inr) := by
  let code := chainedCounterCode left right exit entry r
  have hl := chainedCounterCode_left_run left right exit entry r hx hfirst (by simp)
  have hj := CounterRun.one code
    (⟨some (.inl exit), cs, ys⟩ : CounterCfg R (L ⊕ M)) (.inl exit) rfl
  rw [show code (.inl exit) = .branch r (.inr entry) (.inr entry) from
    chainedCounterCode_exit left right exit entry r] at hj
  have hr := CounterRun.relabel right code Sum.inr
    (chainedCounterCode_right left right exit entry r) hsecond
  dsimp only [CounterCfg.relabel, Option.map] at hl hr
  have hbridge : CounterRun code ⟨some (.inl exit), cs, ys⟩ 1 ⟨some (.inr entry), cs, ys⟩ := by
    simpa [CounterInstr.eval] using hj
  exact CounterRun.trans code (CounterRun.trans code hl hbridge) hr

end ShiReversibleGenerator
