import ReversibleExtractionClosingLoopBudgetData

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- The actual descending-loop counter update preserves the vector budget. -/
theorem extractionClosingLoopBudget_update (tm : Turing.FinTM2) (B spent k : Nat)
    (cs : ExtractionTermRegister → Nat) (h : ExtractionClosingLoopBudget tm B spent cs) (hk : k ≤ B) :
    ExtractionClosingLoopBudget tm B spent (Function.update cs (9 : ExtractionTermRegister) k) := by
  refine {
    length := by simpa using h.length
    base := by simpa using h.base
    endpoint := by simpa using h.endpoint
    count := by simpa using h.count
    cache := by simpa using h.cache
    size := by simpa using h.size
    termPointer := by simpa using h.termPointer
    suffixPointer := by simpa using h.suffixPointer
    stable := ?_
    fields := ?_
    scratch := ?_ }
  · intro q hq
    by_cases h9 : q=9
    · subst q; simpa using hk
    · simpa only [Function.update_of_ne h9] using h.stable q hq
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    · simpa using h.fields 13 (by simp)
    · simpa using h.fields 14 (by simp)
    · simpa using h.fields 15 (by simp)
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    · simpa using h.scratch 5 (by simp)
    · simpa using h.scratch 6 (by simp)
    · simpa using h.scratch 7 (by simp)

theorem extractionClosingLoopBudget_global (tm : Turing.FinTM2) (B spent : Nat)
    (cs : ExtractionTermRegister → Nat) (h : ExtractionClosingLoopBudget tm B spent cs) (hs : spent ≤ B) :
    ∀ q,cs q ≤ 2*B+(extractionClosingContributionBudget tm+45)*(B+1) := by
  intro q
  exact (extractionClosingLoopBudget_uniform tm B spent cs h q).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right hs 1)) _)

end ShiReversibleGenerator
