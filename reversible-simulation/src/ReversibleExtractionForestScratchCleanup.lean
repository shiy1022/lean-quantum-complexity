import ReversibleExtractionForestStepPayload

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- These are the sources and accumulators carried across output slots. -/
def extractionForestControls : List ExtractionForestRegister := [0,1,11,16,18,26,27]

def extractionForestScratch : List ExtractionForestRegister :=
  [2,3,4,5,6,7,8,9,10,12,13,14,15,17,19,20,21,22,23,24,25]

theorem extractionForestScratch_complement (q : ExtractionForestRegister) :
    q ∈ extractionForestScratch ↔ q ∉ extractionForestControls := by
  fin_cases q <;> decide

theorem extractionForestScratch_frame (cs : ExtractionForestRegister → Nat)
    (q : ExtractionForestRegister) (hq : q ∈ extractionForestControls) :
    cleanupCounters extractionForestScratch cs q=cs q := by
  simp [cleanupCounters_apply,extractionForestScratch_complement,hq]

theorem extractionForestScratch_bound (cs : ExtractionForestRegister → Nat) (bound : Nat)
    (hb : ∀ q ∈ extractionForestControls,cs q ≤ bound) :
    ∀ q,cleanupCounters extractionForestScratch cs q ≤ bound := by
  intro q
  by_cases hq : q ∈ extractionForestControls
  · rw [extractionForestScratch_frame cs q hq]
    exact hb q hq
  · simp [cleanupCounters_apply,extractionForestScratch_complement,hq]

end ShiReversibleGenerator
