import ReversibleExtractionCleanForestBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionCleanForestBudget_step (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (bound spent : Nat) (cs : ExtractionForestRegister → Nat)
    (h : ExtractionCleanForestBudget tm bound spent cs) :
    ExtractionCleanForestBudget tm bound (spent+1) ((extractionCleanForestStepTemplate tm e stride backward).counters cs) := by
  let u := (extractionCleanForestStepTemplate tm e stride backward).counters cs
  have hm := extractionCleanForestStepTemplate_metadata tm e stride backward cs
  change u 0=cs 0 ∧ u 1=(if backward then cs 1+1 else cs 1-1) ∧ u 11=cs 11 ∧
    u 18=(if backward then cs 18+cs 27+1 else cs 18-(cs 27+1)) ∧ u 26=cs 26 ∧ u 27=cs 27 at hm
  have hc := extractionCleanForestStepTemplate_count tm e stride backward cs
  change u 16=_ at hc
  have hl := extractionForestLayerIncrement_bound tm e (cs 0) (cs 1) bound h.capacity
  change ExtractionCleanForestBudget tm bound (spent+1) u
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hm.1]; exact h.capacity
  · rw [hm.2.1]
    have hp := h.position
    cases backward <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
  · rw [hm.2.2.1]; exact h.input
  · rw [hc,Nat.add_mul,Nat.one_mul]
    have hh := h.layers
    omega
  · rw [hm.2.2.2.1,Nat.add_mul,Nat.one_mul]
    have hh := h.slot
    have hp := h.padding
    cases backward <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
  · rw [hm.2.2.2.2.1]; exact h.remaining
  · rw [hm.2.2.2.2.2]; exact h.padding
  · intro q hq
    change (extractionCleanForestStepTemplate tm e stride backward).counters cs q ≤ bound
    rw [extractionCleanForestStepTemplate_scratch tm e stride backward cs q hq]
    exact Nat.zero_le _

end ShiReversibleGenerator
