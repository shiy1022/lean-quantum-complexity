import ReversibleExtractionPrefixTraversalBudget
import ReversibleExtractionForwardPrefixFieldBudget
import ReversibleExtractionForwardPrefixAddressBudget
import ReversibleExtractionForwardPrefixStepPolynomial

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- One fixed polynomial state budget bounds the real entire prefix loop, including every loop instruction. -/
theorem extractionForwardPrefixLoopTemplate_polynomial (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) :
    (extractionForwardPrefixLoopTemplate tm e stride).PolynomiallyTimed bound := by
  obtain ⟨fields,hfields⟩ := extractionForwardPrefixStepTemplate_source_fields_budget tm e stride bound
  obtain ⟨addresses,haddresses⟩ := extractionForwardPrefixStepTemplate_source_address_budget tm e stride bound
  let D := 10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7
  let L := 37*extractionTermSchemaBudget tm e+2
  let stable := Polynomial.C 2*bound+Polynomial.C D+fields+addresses
  let global := stable+bound+Polynomial.C L*bound
  have body := extractionTraversalLift_polynomial (extractionForwardPrefixStepTemplate tm e stride) global
    (extractionForwardPrefixStepTemplate_polynomial tm e stride global)
  obtain ⟨clock,hclock⟩ := body
  refine ⟨(Polynomial.C 2+clock)*bound+Polynomial.C 1,?_⟩
  intro n cs hb hr
  let B := bound.eval n
  let M := stable.eval n
  have hm : B ≤ M := by simp only [M,B,stable,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hsmall : 2*B+D ≤ M := by simp only [M,B,stable,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hfM : fields.eval n ≤ M := by simp only [M,stable,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have haM : addresses.eval n ≤ M := by simp only [M,stable,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hloop : ∀ k spent (t : ExtractionTraversalRegister → Nat),
      ExtractionPrefixTraversalBudget tm e B M spent t → spent+k ≤ B →
      descendingTemplateReady (extractionForwardPrefixTraversalStepTemplate tm e stride) 22 k t →
      descendingTemplateSteps (extractionForwardPrefixTraversalStepTemplate tm e stride) 22 k t ≤
        (2+clock.eval n)*k+1 := by
    intro k
    induction k with
    | zero => intro spent t hi hk hready; simp [descendingTemplateSteps]
    | succ k ih =>
      intro spent t hi hk hready
      let next := Function.update t (22 : ExtractionTraversalRegister) k
      let after := (extractionForwardPrefixTraversalStepTemplate tm e stride).counters next
      have hn := extractionPrefixTraversalBudget_update tm e B M spent k t hi (by omega)
      have hg : ∀ q,next q ≤ global.eval n := by
        intro q
        have hu := extractionPrefixTraversalBudget_uniform tm e B M spent next hn q
        have hs : spent ≤ B := by omega
        have hl := Nat.mul_le_mul_left L hs
        simp only [global,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
        change next q ≤ M+B+L*B
        change next q ≤ M+B+L*spent at hu
        omega
      have ht := hclock n next hg hready.1
      change (extractionForwardPrefixTraversalStepTemplate tm e stride).steps next ≤ clock.eval n at ht
      have hf : ∀ q ∈ ([13,14,15] : List ExtractionTermRegister),
          (extractionForwardPrefixStepTemplate tm e stride).counters
            (fun r => next (extractionTermToTraversalRegister r)) q ≤ M := by
        intro q hq
        exact (hfields n _ hn.inner.metadata q hq).trans hfM
      have ha : ∀ q ∈ ([19,20,21] : List ExtractionTermRegister),
          (extractionForwardPrefixStepTemplate tm e stride).counters
            (fun r => next (extractionTermToTraversalRegister r)) q ≤ M := by
        intro q hq
        apply (haddresses n _ ?_ q hq).trans haM
        intro r hr
        exact hn.inner.metadata r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; tauto)
      have hb' := extractionPrefixTraversalBudget_step tm e stride B M spent next hn hsmall hf ha
      have hj := ih (spent+1) after hb' (by omega) hready.2.2
      rw [descendingTemplateSteps]
      change 2+(extractionForwardPrefixTraversalStepTemplate tm e stride).steps next+
        descendingTemplateSteps (extractionForwardPrefixTraversalStepTemplate tm e stride) 22 k after ≤ _
      simp only [Nat.mul_succ]
      omega
  have hs := hloop (cs 22) 0 cs (extractionPrefixTraversalBudget_initial tm e B M cs hb hm)
    (by simpa using hb 22) hr
  have hm' := Nat.add_le_add_right (Nat.mul_le_mul_left (2+clock.eval n) (hb 22)) 1
  simpa only [extractionForwardPrefixLoopTemplate,descendingProgramTemplate,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C] using hs.trans hm'

end ShiReversibleGenerator
