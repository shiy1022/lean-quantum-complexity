import ReversibleExtractionClosingStepFieldBound
import ReversibleExtractionClosingStepScratchMetadata

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator
open ShiReversibleTM

noncomputable def extractionClosingContributionBudget (tm : Turing.FinTM2) : Nat :=
  10+Fintype.card (Option (MachineSymbol tm))*7

/-- A vector invariant separates growing live pointers from overwritten scratch and printer fields. -/
structure ExtractionClosingLoopBudget (tm : Turing.FinTM2) (B spent : Nat)
    (cs : ExtractionTermRegister → Nat) : Prop where
  length : cs 2 ≤ B+spent
  base : cs 18 ≤ B+extractionClosingContributionBudget tm*spent
  endpoint : cs 20 ≤ B
  count : cs 16 ≤ B+41*spent
  stable : ∀ q,q ∉ ([2,3,5,6,7,12,13,14,15,16,18,19,20,21] : List ExtractionTermRegister) → cs q ≤ B
  cache : cs 3 ≤ 2*(B+spent)
  size : cs 12 ≤ B+extractionClosingContributionBudget tm
  fields : ∀ q ∈ ([13,14,15] : List ExtractionTermRegister),
    cs q ≤ B+extractionClosingContributionBudget tm*spent+extractionClosingContributionBudget tm+3
  termPointer : cs 19 ≤ B+extractionClosingContributionBudget tm*spent
  suffixPointer : cs 21 ≤ B
  scratch : ∀ q ∈ ([5,6,7] : List ExtractionTermRegister),cs q ≤ B

theorem extractionClosingLoopBudget_initial (tm : Turing.FinTM2) (B : Nat)
    (cs : ExtractionTermRegister → Nat) (hb : ∀ q,cs q ≤ B) :
    ExtractionClosingLoopBudget tm B 0 cs := by
  refine ⟨?_,?_,hb 20,?_,fun q _ => hb q,?_,?_,?_,?_,hb 21,fun q _ => hb q⟩
  · simpa using hb 2
  · simpa using hb 18
  · simpa using hb 16
  · have h := hb 3; omega
  · exact (hb 12).trans (Nat.le_add_right _ _)
  · intro q hq
    have h := hb q
    omega
  · simpa using hb 19

/-- One linear budget bounds all actual counters at a given iteration number. -/
theorem extractionClosingLoopBudget_uniform (tm : Turing.FinTM2) (B spent : Nat)
    (cs : ExtractionTermRegister → Nat) (h : ExtractionClosingLoopBudget tm B spent cs) :
    ∀ q,cs q ≤ 2*B+(extractionClosingContributionBudget tm+45)*(spent+1) := by
  rcases h with ⟨h2,h18,h20,h16,hs,h3,h12,hf,h19,h21,hx⟩
  have h0 := hs 0 (by decide)
  have h1 := hs 1 (by decide)
  have h4 := hs 4 (by decide)
  have h8 := hs 8 (by decide)
  have h9 := hs 9 (by decide)
  have h10 := hs 10 (by decide)
  have h11 := hs 11 (by decide)
  have h17 := hs 17 (by decide)
  have h13 := hf 13 (by simp)
  have h14 := hf 14 (by simp)
  have h15 := hf 15 (by simp)
  have h5 := hx 5 (by simp)
  have h6 := hx 6 (by simp)
  have h7 := hx 7 (by simp)
  intro q
  fin_cases q <;> simp [Nat.add_mul,Nat.mul_add] at * <;> omega

end ShiReversibleGenerator
