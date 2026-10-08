import ReversibleExtractionDispatchFieldBound
import ReversibleExtractionInputSetupSourceBudget
import ReversibleExtractionBoundTermPrinter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Whole setup-and-print fields depend only on bounded metadata, not old printer fields or count. -/
theorem extractionBoundTermPrinterTemplate_source_fields_budget (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat, ∀ n (cs : ExtractionTermRegister → Nat),
      (∀ q ∈ ([0,1,2,11,18] : List ExtractionTermRegister),cs q ≤ bound.eval n) →
      ∀ q ∈ ([13,14,15] : List ExtractionTermRegister),
        (extractionBoundTermPrinterTemplate tm e stride backward).counters cs q ≤ budget.eval n := by
  obtain ⟨addresses,ha⟩ := extractionInputSetupTemplate_source_budget tm stride bound
  let offset := Fintype.card (Option (MachineSymbol tm))*stride
  refine ⟨bound+addresses+Polynomial.C offset+Polynomial.C (extractionTermSchemaBudget tm e),?_⟩
  intro n cs hb q hq
  let after := (extractionInputSetupTemplate tm stride).counters cs
  have hmetadata : ∀ r ∈ ([0,1,2,11] : List ExtractionTermRegister),cs r ≤ bound.eval n := by
    intro r hr
    exact hb r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; tauto)
  have ha' : ∀ r ∈ ([19,20,21] : List ExtractionTermRegister),after r ≤ addresses.eval n := ha n cs hmetadata
  have hbase : after 18 ≤ bound.eval n := by
    change (extractionInputSetupTemplate tm stride).counters cs 18 ≤ bound.eval n
    rw [extractionInputSetupTemplate_frame tm stride cs 18
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hb 18 (by simp)
  have hinputs : ∀ i,(extractionBoundInputs tm stride i).eval after ≤ bound.eval n+addresses.eval n+offset := by
    intro i
    cases i with
    | inl i =>
      have h19 := ha' 19 (by simp)
      have h20 := ha' 20 (by simp)
      simp only [extractionBoundInputs,SymbolicWire.eval,Nat.add_zero]
      split_ifs <;> omega
    | inr a =>
      have h21 := ha' 21 (by simp)
      have ho : ((Fintype.equivFin (Option (MachineSymbol tm))) a).val*stride ≤ offset :=
        Nat.mul_le_mul_right stride (Nat.le_of_lt ((Fintype.equivFin (Option (MachineSymbol tm))) a).isLt)
      simp only [extractionBoundInputs,SymbolicWire.eval]
      omega
  have hf := extractionTermDispatchTemplate_fields_bound tm e stride backward after
    (bound.eval n+addresses.eval n+offset) (by omega) hinputs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  all_goals simp only [extractionBoundTermPrinterTemplate,sequenceProgramTemplate,Polynomial.eval_add,Polynomial.eval_C]
  · exact hf.1
  · exact hf.2.1
  · exact hf.2.2

end ShiReversibleGenerator
