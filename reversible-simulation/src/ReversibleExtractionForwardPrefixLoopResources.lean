import ReversibleExtractionForwardPrefixLoopPolynomial

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Whole-prefix execution has a polynomial real instruction clock and polynomial exit counters. -/
theorem extractionForwardPrefixLoopTemplate_resources (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat,(extractionForwardPrefixLoopTemplate tm e stride).PolynomiallyTimed bound ∧
      ∀ n (cs : ExtractionTraversalRegister → Nat),(∀ q,cs q ≤ bound.eval n) →
        ∀ q,(extractionForwardPrefixLoopTemplate tm e stride).counters cs q ≤ budget.eval n := by
  obtain ⟨fields,hfields⟩ := extractionForwardPrefixStepTemplate_source_fields_budget tm e stride bound
  obtain ⟨addresses,haddresses⟩ := extractionForwardPrefixStepTemplate_source_address_budget tm e stride bound
  let D := 10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7
  let L := 37*extractionTermSchemaBudget tm e+2
  let stable := Polynomial.C 2*bound+Polynomial.C D+fields+addresses
  let global := stable+bound+Polynomial.C L*bound
  refine ⟨global,extractionForwardPrefixLoopTemplate_polynomial tm e stride bound,?_⟩
  intro n cs hb q
  let B := bound.eval n
  let M := stable.eval n
  have hm : B ≤ M := by simp only [M,B,stable,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hsmall : 2*B+D ≤ M := by simp only [M,B,stable,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hfM : fields.eval n ≤ M := by simp only [M,stable,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have haM : addresses.eval n ≤ M := by simp only [M,stable,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hloop : ∀ k spent (t : ExtractionTraversalRegister → Nat),
      ExtractionPrefixTraversalBudget tm e B M spent t → spent+k ≤ B →
      ExtractionPrefixTraversalBudget tm e B M (spent+k)
        (descendingTemplateCounters (extractionForwardPrefixTraversalStepTemplate tm e stride) 22 k t) := by
    intro k
    induction k with
    | zero => intro spent t hi hk; simpa only [descendingTemplateCounters,Nat.add_zero] using hi
    | succ k ih =>
      intro spent t hi hk
      let next := Function.update t (22 : ExtractionTraversalRegister) k
      have hn := extractionPrefixTraversalBudget_update tm e B M spent k t hi (by omega)
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
      have hj := ih (spent+1) ((extractionForwardPrefixTraversalStepTemplate tm e stride).counters next) hb' (by omega)
      simpa only [descendingTemplateCounters,next,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hj
  have hi : ExtractionPrefixTraversalBudget tm e B M (cs 22)
      (descendingTemplateCounters (extractionForwardPrefixTraversalStepTemplate tm e stride) 22 (cs 22) cs) := by
    simpa only [Nat.zero_add] using hloop (cs 22) 0 cs
      (extractionPrefixTraversalBudget_initial tm e B M cs hb hm) (by simpa using hb 22)
  have hr := extractionPrefixTraversalBudget_update tm e B M (cs 22) 0 _ hi (Nat.zero_le _)
  have hu := extractionPrefixTraversalBudget_uniform tm e B M (cs 22) _ hr q
  have hl : L*(cs 22) ≤ L*B := Nat.mul_le_mul_left L (hb 22)
  simp only [global,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  change (extractionForwardPrefixLoopTemplate tm e stride).counters cs q ≤ M+B+L*B
  change (extractionForwardPrefixLoopTemplate tm e stride).counters cs q ≤ M+B+L*(cs 22) at hu
  omega

end ShiReversibleGenerator
