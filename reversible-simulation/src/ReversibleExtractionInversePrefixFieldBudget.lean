import ReversibleExtractionTermNegationFieldBound
import ReversibleExtractionInversePrefixStepReady
import ReversibleExtractionTermSizeBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- The inverse body ends with bounded negation fields, independent of all old fields and counts. -/
theorem extractionInversePrefixStepTemplate_source_fields_budget (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat,∀ n (cs : ExtractionTermRegister → Nat),cs 18 ≤ bound.eval n →
      ∀ q ∈ ([13,14,15] : List ExtractionTermRegister),
        (extractionInversePrefixStepTemplate tm e stride).counters cs q ≤ budget.eval n := by
  let D := 10+Fintype.card (Option (MachineSymbol tm))*7
  refine ⟨Polynomial.C 2*bound+Polynomial.C (2*D+1),?_⟩
  intro n cs hb q hq
  let t := (extractionTermSizeProgramTemplate tm).counters cs
  let u := (extractionBoundTermPrinterTemplate tm e stride true).counters t
  let v := (extractionTermNegationPrinterTemplate true).counters u
  have ht18 : t 18=cs 18 := by simp [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  have ht12 : t 12 ≤ D := by
    change (extractionTermSizeProgramTemplate tm).counters cs 12 ≤ D
    rw [extractionTermSizeProgramTemplate_value]
    exact extractionSizeContribution_bound tm (cs 2) (cs 1)
  have hu18 : u 18=t 18 := extractionBoundTermPrinterTemplate_frame tm e stride true t 18
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hu12 : u 12=t 12 := extractionBoundTermPrinterTemplate_frame tm e stride true t 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hbase : u 18 ≤ bound.eval n := (hu18.trans ht18).trans_le hb
  have hsize : u 12 ≤ D := hu12.trans_le ht12
  have hf := extractionTermNegationPrinterTemplate_fields_bound true u (bound.eval n+D) (by omega) (by omega)
  change v 13 ≤ 2*(bound.eval n+D)+1 ∧ v 14 ≤ 2*(bound.eval n+D)+1 ∧ v 15 ≤ 2*(bound.eval n+D)+1 at hf
  change extractionPrefixAdvanceTemplate.counters v q ≤ _
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  all_goals simp only [extractionPrefixAdvanceTemplate_counters]
  all_goals simp
  all_goals omega

end ShiReversibleGenerator
