import ReversibleExtractionForwardClosingPayload
import ReversibleDescendingTemplatePointFrames

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Actual forward closing finishes at the original false-constant base and advances length by the exact term count. -/
theorem extractionForwardClosing_descending_coordinates (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (k : Nat) (cs : ExtractionTermRegister → Nat) (hlimit : cs 2+k ≤ cs 0+1) :
    let after := descendingTemplateCounters (extractionClosingStepTemplate tm false) 9 k cs
    after 2=cs 2+k ∧ after 18=cs 18+
      ((extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) k).map (fun p => p.size+1)).sum := by
  induction k generalizing cs with
  | zero => simp [descendingTemplateCounters,extractionNaturalTermRange]
  | succ k ih =>
    let next := Function.update cs (9 : ExtractionTermRegister) k
    let after := (extractionClosingStepTemplate tm false).counters next
    have hn0 : next 0=cs 0 := by simp [next]
    have hn1 : next 1=cs 1 := by simp [next]
    have hn2 : next 2=cs 2 := by simp [next]
    have hn18 : next 18=cs 18 := by simp [next]
    have hf : ∀ q ∈ ([0,1] : List ExtractionTermRegister),after q=cs q := by
      intro q hq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl
      all_goals exact ((extractionClosingStepTemplate_frame tm false next _
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans (by simp [next]))
    have h0 := hf 0 (by simp)
    have h1 := hf 1 (by simp)
    have h2 : after 2=cs 2+1 := by
      have h := (extractionClosingStepTemplate_metadata tm false next).1
      rw [hn2] at h
      exact h
    have h18 := extractionClosingStepTemplate_termBase tm e false next (by rw [hn2,hn0]; omega)
    change after 18=_ at h18
    rw [hn0,hn1,hn2,hn18] at h18
    have hi := ih after (by rw [h2,h0]; omega)
    dsimp only at hi
    rw [h0,h1,h2,h18] at hi
    simpa only [descendingTemplateCounters,next,extractionNaturalTermRange,List.map_cons,List.sum_cons,
      extractionNaturalTerm,Formula.rename_size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi

theorem extractionForwardClosingLoopTemplate_coordinates (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (cs : ExtractionTermRegister → Nat) (hlimit : cs 2+cs 9 ≤ cs 0+1) :
    (extractionForwardClosingLoopTemplate tm).counters cs 2=cs 2+cs 9 ∧
    (extractionForwardClosingLoopTemplate tm).counters cs 18=cs 18+
      ((extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) (cs 9)).map (fun p => p.size+1)).sum := by
  have h := extractionForwardClosing_descending_coordinates tm e (cs 9) cs hlimit
  simpa only [extractionForwardClosingLoopTemplate,descendingProgramTemplate,
    Function.update_of_ne (by decide : (2 : ExtractionTermRegister) ≠ 9),
    Function.update_of_ne (by decide : (18 : ExtractionTermRegister) ≠ 9)] using h

end ShiReversibleGenerator
