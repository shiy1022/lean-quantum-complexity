import ReversibleStridedSharedEmitterPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R : Type} [DecidableEq R] [Fintype R]

/-- Every final counter of the actual strided bind/print/clear program has a polynomial bound. -/
theorem stridedBindingPrinterTemplate_counter_bound (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (inputStride : Nat) (tasks : List (CoordinateBindingTask tm R))
    (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) (clear : List R) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat, ∀ n (cs : R → Nat), (∀ q, cs q ≤ bound.eval n) →
      ∀ q, (stridedBindingPrinterTemplate tm env inputStride tasks r ts clear).counters cs q ≤ budget.eval n := by
  classical
  obtain ⟨bindBudget, bindClock, hb⟩ := stridedCoordinateBindingSequence_polynomial tm env inputStride tasks hv bound
  let sizes : R → Polynomial Nat := fun _ => bindBudget
  let final := fixedPrinterCounterPolynomials r ts sizes
  refine ⟨∑ q, final q, ?_⟩
  intro n cs hc q
  let after := stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs
  have ha : ∀ z, after z ≤ bindBudget.eval n := (hb n cs hc).1
  have hm := fixedNodeCounters_mono r ts after (fun z => (sizes z).eval n) ha q
  have he := congrFun (fixedPrinterCounterPolynomials_eval r ts sizes n) q
  have hs : (final q).eval n ≤ (∑ z, final z).eval n := by
    rw [Polynomial.eval_finsetSum]
    exact Finset.single_le_sum (fun z _ => Nat.zero_le ((final z).eval n)) (Finset.mem_univ q)
  change cleanupCounters clear (fixedNodeCounters r ts after) q ≤ _
  rw [cleanupCounters_apply]
  split
  · exact Nat.zero_le _
  · exact (hm.trans (by simpa only [final] using he.ge)).trans hs

end ShiReversibleGenerator
