import ReversibleExtractionInversePrefixLoopPolynomial

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Whole-prefix execution has a polynomial real instruction clock and polynomial exit counters. -/
theorem extractionInversePrefixLoopTemplate_resources (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat,(extractionInversePrefixLoopTemplate tm e stride).PolynomiallyTimed bound ∧
      ∀ n (cs : ExtractionTraversalRegister → Nat),(∀ q,cs q ≤ bound.eval n) →
        ∀ q,(extractionInversePrefixLoopTemplate tm e stride).counters cs q ≤ budget.eval n := by
  let D := 10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7
  let G := D+37*extractionTermSchemaBudget tm e+3
  let sourceBound := Polynomial.C 2*bound
  let baseBound := Polynomial.C (1+D)*bound
  obtain ⟨fields,hfields⟩ := extractionInversePrefixStepTemplate_source_fields_budget tm e stride baseBound
  obtain ⟨addresses,haddresses⟩ := extractionInversePrefixStepTemplate_source_address_budget tm e stride sourceBound
  let stable := Polynomial.C 4*bound+baseBound+Polynomial.C (D+1)+fields+addresses
  let global := stable+bound+Polynomial.C G*bound
  refine ⟨global,extractionInversePrefixLoopTemplate_polynomial tm e stride bound,?_⟩
  intro n cs hb q
  let B := bound.eval n
  let M := stable.eval n
  have hm : B ≤ M := by simp only [M,B,stable,baseBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hsmall : 4*B+(1+D)*B+D+1 ≤ M := by simp only [M,B,stable,baseBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hfM : fields.eval n ≤ M := by simp only [M,stable,baseBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have haM : addresses.eval n ≤ M := by simp only [M,stable,baseBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hloop : ∀ k spent (t : ExtractionTraversalRegister → Nat),
      ExtractionInversePrefixTraversalBudget tm e B M spent t → spent+k ≤ B →
      ExtractionInversePrefixTraversalBudget tm e B M (spent+k)
        (descendingTemplateCounters (extractionInversePrefixTraversalStepTemplate tm e stride) 22 k t) := by
    intro k
    induction k with
    | zero => intro spent t hi hk; simpa only [descendingTemplateCounters,Nat.add_zero] using hi
    | succ k ih =>
      intro spent t hi hk
      let next := Function.update t (22 : ExtractionTraversalRegister) k
      have hn := extractionInversePrefixTraversalBudget_update tm e B M spent k t hi (by omega)
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
      have hj := ih (spent+1) ((extractionInversePrefixTraversalStepTemplate tm e stride).counters next) hb' (by omega)
      simpa only [descendingTemplateCounters,next,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hj
  have hi : ExtractionInversePrefixTraversalBudget tm e B M (cs 22)
      (descendingTemplateCounters (extractionInversePrefixTraversalStepTemplate tm e stride) 22 (cs 22) cs) := by
    simpa only [Nat.zero_add] using hloop (cs 22) 0 cs
      (extractionInversePrefixTraversalBudget_initial tm e B M cs hb hm) (by simpa using hb 22)
  have hr := extractionInversePrefixTraversalBudget_update tm e B M (cs 22) 0 _ hi (Nat.zero_le _)
  have hu := extractionInversePrefixTraversalBudget_uniform tm e B M (cs 22) _ hr q
  have hl : G*(cs 22) ≤ G*B := Nat.mul_le_mul_left G (hb 22)
  simp only [global,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  change (extractionInversePrefixLoopTemplate tm e stride).counters cs q ≤ M+B+G*B
  change (extractionInversePrefixLoopTemplate tm e stride).counters cs q ≤ M+B+G*(cs 22) at hu
  omega

end ShiReversibleGenerator
