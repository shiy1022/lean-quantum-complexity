import ReversibleExtractionForwardPrefixLoopCount
import ReversibleExtractionNaturalTermLayerBound

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- The real accumulated prefix count has a linear polynomial bound. -/
theorem extractionForwardPrefixLoop_count_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (k : Nat) (cs : ExtractionTraversalRegister → Nat)
    (hk : k ≤ cs 0+1) (hell : cs 2=k-1) :
    descendingTemplateCounters (extractionForwardPrefixTraversalStepTemplate tm e stride) 22 k cs 16 ≤
      cs 16+k*(37*(10+Fintype.card (Option (MachineSymbol tm))*7)+2) := by
  rw [extractionForwardPrefixLoop_count tm e stride k cs hk hell]
  exact Nat.add_le_add_left
    (extractionNaturalTermRange_layers_bound tm e (cs 0) (cs 1) 0 k (by simpa using hk)) _

theorem extractionForwardPrefixLoop_count_polynomial_bound (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) (n : Nat)
    (cs : ExtractionTraversalRegister → Nat) (hb : ∀ q,cs q ≤ bound.eval n)
    (hk : cs 22 ≤ cs 0+1) (hell : cs 2=cs 22-1) :
    (extractionForwardPrefixLoopTemplate tm e stride).counters cs 16 ≤
      (Polynomial.C (1+(37*(10+Fintype.card (Option (MachineSymbol tm))*7)+2))*bound).eval n := by
  change Function.update (descendingTemplateCounters (extractionForwardPrefixTraversalStepTemplate tm e stride)
    22 (cs 22) cs) 22 0 16 ≤ _
  rw [Function.update_of_ne (by decide : (16 : ExtractionTraversalRegister) ≠ 22)]
  have h := extractionForwardPrefixLoop_count_bound tm e stride (cs 22) cs hk hell
  have h16 := hb 16
  have h22 := hb 22
  simp only [Polynomial.eval_mul,Polynomial.eval_C]
  nlinarith

end ShiReversibleGenerator
