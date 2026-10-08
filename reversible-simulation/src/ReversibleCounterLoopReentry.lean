import ReversibleCounterProgram

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

theorem CounterRun.none_terminal (code : L → CounterInstr R L)
    {s t : CounterCfg R L} {k : Nat} (h : CounterRun code s k t) (hs : s.pc = none) :
    t = s ∧ k = 0 := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | next hl rest ih => cases hs.symm.trans hl

/-- A run ending at a live continuation never executes a halt label; such labels can
be replaced by loop control without changing the checked private-body execution. -/
theorem CounterRun.modify_halts (code code' : L → CounterInstr R L)
    (hf : ∀ l, code l ≠ .halt → code' l = code l)
    {s t : CounterCfg R L} {k : Nat} (h : CounterRun code s k t) (ht : t.pc ≠ none) :
    CounterRun code' s k t := by
  induction h with
  | refl => exact CounterRun.refl _
  | @next s t k l hl rest ih =>
      have hnh : code l ≠ .halt := by
        intro hh
        have hn := CounterRun.none_terminal code rest (by rw [hh]; rfl)
        apply ht
        rw [hn.1, hh]
        rfl
      apply CounterRun.next hl
      rw [hf l hnh]
      exact ih ht

end ShiReversibleGenerator
