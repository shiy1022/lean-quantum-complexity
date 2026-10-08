import ReversibleExtractionCleanForestStepMetadata

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- A fixed input-capacity bound gives a uniform layer increment bound for every output position. -/
noncomputable def extractionForestLayerIncrementBound (tm : Turing.FinTM2) (bound : Nat) : Nat :=
  37*extractionBitBound tm bound+1

theorem extractionForestLayerIncrement_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j bound : Nat) (hc : capacity ≤ bound) :
    formulaElementaryLayers (extractionFormula tm e capacity j)+1 ≤ extractionForestLayerIncrementBound tm bound := by
  have h := (formulaElementaryLayers_bound _).trans (Nat.mul_le_mul_left 37 (extractionFormula_size tm e capacity j))
  have hm := Nat.mul_le_mul_right (10+Fintype.card (Option (MachineSymbol tm))*7) (Nat.add_le_add_right hc 1)
  have hs : extractionBitBound tm capacity ≤ extractionBitBound tm bound := by
    simp only [extractionBitBound]
    omega
  exact Nat.add_le_add_right (h.trans (Nat.mul_le_mul_left 37 hs)) 1

/-- Only the position, slot address and layer count grow; all scratch is reset between leaves. -/
structure ExtractionCleanForestBudget (tm : Turing.FinTM2) (bound spent : Nat)
    (cs : ExtractionForestRegister → Nat) : Prop where
  capacity : cs 0 ≤ bound
  position : cs 1 ≤ bound+spent
  input : cs 11 ≤ bound
  layers : cs 16 ≤ bound+spent*extractionForestLayerIncrementBound tm bound
  slot : cs 18 ≤ bound+spent*(bound+1)
  remaining : cs 26 ≤ bound
  padding : cs 27 ≤ bound
  scratch : ∀ q ∈ extractionForestScratch,cs q ≤ bound

theorem extractionCleanForestBudget_initial (tm : Turing.FinTM2) (bound : Nat)
    (cs : ExtractionForestRegister → Nat) (hb : ∀ q,cs q ≤ bound) :
    ExtractionCleanForestBudget tm bound 0 cs := by
  refine ⟨hb 0,?_,hb 11,?_,?_,hb 26,hb 27,fun q _ => hb q⟩
  all_goals simpa using hb _

theorem extractionCleanForestBudget_update (tm : Turing.FinTM2) (bound spent k : Nat)
    (cs : ExtractionForestRegister → Nat) (h : ExtractionCleanForestBudget tm bound spent cs)
    (hk : k ≤ bound) : ExtractionCleanForestBudget tm bound spent (Function.update cs 26 k) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa using h.capacity
  · simpa using h.position
  · simpa using h.input
  · simpa using h.layers
  · simpa using h.slot
  · simpa using hk
  · simpa using h.padding
  · intro q hq
    have hne : q ≠ 26 := by
      intro he; subst q; simp [extractionForestScratch] at hq
    simpa [hne] using h.scratch q hq

theorem extractionCleanForestBudget_uniform (tm : Turing.FinTM2) (bound spent : Nat)
    (cs : ExtractionForestRegister → Nat) (h : ExtractionCleanForestBudget tm bound spent cs)
    (hs : spent ≤ bound) :
    ∀ q,cs q ≤ bound+bound*(extractionForestLayerIncrementBound tm bound+bound+2) := by
  intro q
  let L := extractionForestLayerIncrementBound tm bound
  change cs q ≤ bound+bound*(L+bound+2)
  have hpos := h.position
  have hlay := h.layers
  have hslot := h.slot
  have hp : spent ≤ bound*(L+bound+2) := by nlinarith
  have hl : spent*L ≤ bound*(L+bound+2) := by nlinarith
  have ha : spent*(bound+1) ≤ bound*(L+bound+2) := by nlinarith
  by_cases hq : q ∈ extractionForestControls
  · simp only [extractionForestControls,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hh := h.capacity; omega
    · omega
    · have hh := h.input; omega
    · change cs 16 ≤ bound+bound*(L+bound+2); change cs 16 ≤ bound+spent*L at hlay; omega
    · omega
    · have hh := h.remaining; omega
    · have hh := h.padding; omega
  · have hh := h.scratch q ((extractionForestScratch_complement q).2 hq)
    omega

end ShiReversibleGenerator
