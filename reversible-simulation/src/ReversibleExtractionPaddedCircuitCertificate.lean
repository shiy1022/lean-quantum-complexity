import ReversibleExtractionPaddedForwardPayload
import ReversibleExtractionPaddedInversePayload
import ReversibleExtractionPaddedQuantumEncoding
import ReversibleExtractionPaddedLeafReady
import ReversibleExtractionPaddedLeafCount

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Exact finite-wire padded extraction from a real finite generator, with actual layer count, clock and all counter exits. -/
theorem extractionPaddedLeafTemplate_circuit_certificate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    ∃ budget clock : Polynomial Nat,∀ n (cs : ExtractionPaddedRegister → Nat),
      (∀ q,cs q ≤ bound.eval n) → cs 2=0 → (if backward then cs 22 else cs 9)=cs 0+1 →
      cs 20=cs 18+((extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 0+1)).map (fun p => p.size+4)).sum →
      cs 17=0 → cs 7=0 →
      ∀ (slotBound wires : Nat), cs 24=(extractionFormula tm e (cs 0) (cs 1)).result (cs 18) →
      cs 25=cs 18+slotBound →
      ∀ (hsize : (extractionFormula tm e (cs 0) (cs 1)).size ≤ slotBound)
        (hin : ∀ i : Fin (configurationWidth tm (cs 0)),cs 11+stride*i.val < cs 18)
        (hout : cs 18+slotBound+1 ≤ wires)
        (L : Type) (caller : L → CounterInstr ExtractionPaddedRegister L) (stop : L) (ys : List Bool),
      let p := extractionPaddedLeafTemplate tm e stride backward
      let gs := extractionPaddedQuantumLayers tm e (cs 0) (cs 1) (cs 11) stride (cs 18) slotBound wires hsize hin hout backward
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs 16=cs 16+gs.length ∧
      ∀ q,p.counters cs q ≤ budget.eval n := by
  obtain ⟨⟨budget,hexit⟩,⟨clock,hclock⟩⟩ := extractionPaddedLeafTemplate_resources tm e stride backward bound
  refine ⟨budget,clock,?_⟩
  intro n cs hb hell hcount hend h17 h7 slotBound wires hsource htarget hsize hin hout L caller stop ys
  dsimp only
  have hr := extractionPaddedLeafTemplate_ready tm e stride backward cs h17 h7
  have hrun := extractionPaddedLeafTemplate_run tm e stride backward L caller stop cs ys hr
  have hp : (extractionPaddedLeafTemplate tm e stride backward).bytes cs=
      ((if backward then (extractionPaddedRawNodes tm e (cs 0) (cs 1) (cs 11) stride (cs 18) slotBound).reverse
        else extractionPaddedRawNodes tm e (cs 0) (cs 1) (cs 11) stride (cs 18) slotBound).map (rawAssignmentPayload backward)).flatten := by
    cases backward
    · exact extractionPaddedLeafTemplate_forward_payload tm e stride slotBound cs hell hcount hend hsource htarget
    · exact extractionPaddedLeafTemplate_inverse_payload tm e stride slotBound cs hell hcount hsource htarget
  have hq := extractionPaddedQuantumLayers_payload tm e (cs 0) (cs 1) (cs 11) stride (cs 18) slotBound wires hsize hin hout backward
  rw [hp.trans hq] at hrun
  refine ⟨hrun,hclock n cs hb hr,?_,hexit n cs hb⟩
  rw [extractionPaddedQuantumLayers_length]
  exact extractionPaddedLeafTemplate_count tm e stride backward cs hell hcount

end ShiReversibleGenerator
