import ReversibleExtractionSizeStepCounters
import ReversibleDescendingTemplateFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

noncomputable def extractionSizeLoopTemplate (tm : Turing.FinTM2) : CounterProgramTemplate ExtractionSizeRegister :=
  descendingProgramTemplate (extractionSizeStepTemplate tm) 2

noncomputable def extractionSizeSum (tm : Turing.FinTM2) (j : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => extractionSizeSum tm j k+extractionSizeContribution tm k j

theorem extractionSizeLoopTemplate_embeds (tm : Turing.FinTM2) : (extractionSizeLoopTemplate tm).Embeds :=
  descendingProgramTemplate_embeds _ _ (extractionSizeStepTemplate_embeds tm)

theorem extractionSizeLoopTemplate_run (tm : Turing.FinTM2) : (extractionSizeLoopTemplate tm).Runs :=
  descendingProgramTemplate_run _ _ (extractionSizeStepTemplate_embeds tm) (extractionSizeStepTemplate_run tm)

theorem extractionSizeLoopTemplate_ready (tm : Turing.FinTM2) (cs : ExtractionSizeRegister → Nat)
    (h5 : cs 5=0) (h6 : cs 6=0) (h7 : cs 7=0) : (extractionSizeLoopTemplate tm).ready cs := by
  suffices h : ∀ k cs,cs 5=0 → cs 6=0 → cs 7=0 →
      descendingTemplateReady (extractionSizeStepTemplate tm) 2 k cs by exact h _ _ h5 h6 h7
  intro k
  induction k with
  | zero => intro cs h5 h6 h7; trivial
  | succ k ih =>
    intro cs h5 h6 h7
    have hr : (extractionSizeStepTemplate tm).ready (Function.update cs 2 k) := by
      rw [extractionSizeStepTemplate_ready]
      simpa using And.intro h5 (And.intro h6 h7)
    refine ⟨hr,?_,?_⟩
    · rw [extractionSizeStepTemplate_remaining_frame]; simp
    · have hn := extractionSizeStepTemplate_ready_preserved tm (Function.update cs 2 k) hr
      rw [extractionSizeStepTemplate_ready] at hn
      exact ih _ hn.1 hn.2.1 hn.2.2

/-- A real finite descending pass accumulates every selected-term suffix contribution. -/
theorem extractionSizeLoopTemplate_result (tm : Turing.FinTM2) (cs : ExtractionSizeRegister → Nat) :
    (extractionSizeLoopTemplate tm).counters cs 4=cs 4+extractionSizeSum tm (cs 1) (cs 2) ∧
      (extractionSizeLoopTemplate tm).counters cs 1=cs 1 ∧
      (extractionSizeLoopTemplate tm).counters cs 2=0 := by
  have h : ∀ k (t : ExtractionSizeRegister → Nat),
      descendingTemplateCounters (extractionSizeStepTemplate tm) 2 k t 4=t 4+extractionSizeSum tm (t 1) k ∧
      descendingTemplateCounters (extractionSizeStepTemplate tm) 2 k t 1=t 1 := by
    intro k
    induction k with
    | zero => intro t; simp [descendingTemplateCounters,extractionSizeSum]
    | succ k ih =>
      intro t
      rw [descendingTemplateCounters]
      obtain ⟨h4,h1⟩ := ih ((extractionSizeStepTemplate tm).counters (Function.update t 2 k))
      rw [h4,h1,extractionSizeStepTemplate_counters]
      simp [extractionSizeSum,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  obtain ⟨h4,h1⟩ := h (cs 2) cs
  refine ⟨?_,?_,?_⟩
  · simpa only [extractionSizeLoopTemplate,descendingProgramTemplate,
      Function.update_of_ne (by decide : (4 : ExtractionSizeRegister) ≠ 2)] using h4
  · simpa only [extractionSizeLoopTemplate,descendingProgramTemplate,
      Function.update_of_ne (by decide : (1 : ExtractionSizeRegister) ≠ 2)] using h1
  · simp only [extractionSizeLoopTemplate,descendingProgramTemplate,Function.update_self]

theorem extractionSizeSum_finRange (tm : Turing.FinTM2) (j k : Nat) :
    extractionSizeSum tm j k=((List.finRange k).map (fun ell => extractionSizeContribution tm ell.val j)).sum := by
  have h : ∀ k,extractionSizeSum tm j k=(List.ofFn (fun ell : Fin k => extractionSizeContribution tm ell.val j)).sum := by
    intro k
    induction k with
    | zero => simp [extractionSizeSum]
    | succ k ih =>
      simp only [extractionSizeSum,List.ofFn_succ',List.concat_eq_append,List.sum_append,
        List.sum_cons,List.sum_nil,Fin.val_castSucc,Fin.val_last,Nat.add_zero,ih]
  simpa only [List.ofFn_eq_map] using h k

/-- Initializing the accumulator to one produces the exact formula size from runtime capacity and output position. -/
theorem extractionSizeLoopTemplate_formula_size (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (cs : ExtractionSizeRegister → Nat) (capacity : Nat) (hc : cs 2=capacity+1) (hs : cs 4=1) :
    (extractionSizeLoopTemplate tm).counters cs 4=(ShiReversibleTM.extractionFormula tm e capacity (cs 1)).size := by
  rw [(extractionSizeLoopTemplate_result tm cs).1,hs,hc,extractionSizeSum_finRange,
    extractionFormula_size_exact]

end ShiReversibleGenerator
