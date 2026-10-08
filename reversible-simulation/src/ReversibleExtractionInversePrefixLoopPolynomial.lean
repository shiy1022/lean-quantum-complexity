import ReversibleExtractionInversePrefixTraversalBudget
import ReversibleExtractionInversePrefixFieldBudget
import ReversibleExtractionInversePrefixAddressBudget
import ReversibleExtractionInversePrefixStepPolynomial

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- One fixed polynomial state budget bounds the real entire prefix loop, including every loop instruction. -/
theorem extractionInversePrefixLoopTemplate_polynomial (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) :
    (extractionInversePrefixLoopTemplate tm e stride).PolynomiallyTimed bound := by
  let D := 10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7
  let G := D+37*extractionTermSchemaBudget tm e+3
  let sourceBound := Polynomial.C 2*bound
  let baseBound := Polynomial.C (1+D)*bound
  obtain ⟨fields,hfields⟩ := extractionInversePrefixStepTemplate_source_fields_budget tm e stride baseBound
  obtain ⟨addresses,haddresses⟩ := extractionInversePrefixStepTemplate_source_address_budget tm e stride sourceBound
  let stable := Polynomial.C 4*bound+baseBound+Polynomial.C (D+1)+fields+addresses
  let global := stable+bound+Polynomial.C G*bound
  have body := extractionTraversalLift_polynomial (extractionInversePrefixStepTemplate tm e stride) global
    (extractionInversePrefixStepTemplate_polynomial tm e stride global)
  obtain ⟨clock,hclock⟩ := body
  refine ⟨(Polynomial.C 2+clock)*bound+Polynomial.C 1,?_⟩
  intro n cs hb hr
  let B := bound.eval n
  let M := stable.eval n
  have hm : B ≤ M := by simp only [M,B,stable,baseBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hsmall : 4*B+(1+D)*B+D+1 ≤ M := by simp only [M,B,stable,baseBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hfM : fields.eval n ≤ M := by simp only [M,stable,baseBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have haM : addresses.eval n ≤ M := by simp only [M,stable,baseBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hloop : ∀ k spent (t : ExtractionTraversalRegister → Nat),
      ExtractionInversePrefixTraversalBudget tm e B M spent t → spent+k ≤ B →
      descendingTemplateReady (extractionInversePrefixTraversalStepTemplate tm e stride) 22 k t →
      descendingTemplateSteps (extractionInversePrefixTraversalStepTemplate tm e stride) 22 k t ≤
        (2+clock.eval n)*k+1 := by
    intro k
    induction k with
    | zero => intro spent t hi hk hready; simp [descendingTemplateSteps]
    | succ k ih =>
      intro spent t hi hk hready
      let next := Function.update t (22 : ExtractionTraversalRegister) k
      let after := (extractionInversePrefixTraversalStepTemplate tm e stride).counters next
      have hn := extractionInversePrefixTraversalBudget_update tm e B M spent k t hi (by omega)
      have hg : ∀ q,next q ≤ global.eval n := by
        intro q
        have hu := extractionInversePrefixTraversalBudget_uniform tm e B M spent next hn q
        have hs : spent ≤ B := by omega
        have hl := Nat.mul_le_mul_left G hs
        simp only [global,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
        change next q ≤ M+B+G*B
        change next q ≤ M+B+G*spent at hu
        omega
      have ht := hclock n next hg hready.1
      change (extractionInversePrefixTraversalStepTemplate tm e stride).steps next ≤ clock.eval n at ht
      have hsource := extractionInversePrefixBudget_sources tm e B M spent _ hn.inner (by omega)
      have hf : ∀ q ∈ ([13,14,15] : List ExtractionTermRegister),
          (extractionInversePrefixStepTemplate tm e stride).counters
            (fun r => next (extractionTermToTraversalRegister r)) q ≤ M := by
        intro q hq
        apply (hfields n _ ?_ q hq).trans hfM
        simpa only [baseBound,Polynomial.eval_mul,Polynomial.eval_C,B] using hsource.2
      have ha : (extractionInversePrefixStepTemplate tm e stride).counters
            (fun r => next (extractionTermToTraversalRegister r)) 20 ≤ M := by
        apply (haddresses n _ ?_).trans haM
        intro r hr
        simpa only [sourceBound,Polynomial.eval_mul,Polynomial.eval_C,B] using hsource.1 r hr
      have hb' := extractionInversePrefixTraversalBudget_step tm e stride B M spent next hn (by omega) hsmall hf ha
      have hj := ih (spent+1) after hb' (by omega) hready.2.2
      rw [descendingTemplateSteps]
      change 2+(extractionInversePrefixTraversalStepTemplate tm e stride).steps next+
        descendingTemplateSteps (extractionInversePrefixTraversalStepTemplate tm e stride) 22 k after ≤ _
      simp only [Nat.mul_succ]
      omega
  have hs := hloop (cs 22) 0 cs (extractionInversePrefixTraversalBudget_initial tm e B M cs hb hm)
    (by simpa using hb 22) hr
  have hm' := Nat.add_le_add_right (Nat.mul_le_mul_left (2+clock.eval n) (hb 22)) 1
  simpa only [extractionInversePrefixLoopTemplate,descendingProgramTemplate,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C] using hs.trans hm'

end ShiReversibleGenerator
