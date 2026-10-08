import ReversibleLeafPaddedFormulaPrinter
import ReversibleFixedPrinterCounterPolynomials

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R : Type} [DecidableEq R]

/-- Bounds the exact clock of binding, printing and clearing any finite list of private slots. -/
theorem coordinateBindingPrinterCleanup_polynomial (tm : Turing.FinTM2)
    (env : CoordinateBindingRegisters R) (tasks : List (CoordinateBindingTask tm R))
    (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) (bound : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : R → Nat), (∀ q, cs q ≤ bound.eval n) →
      let after := coordinateBindingSequenceCounters tm env tasks cs
      coordinateBindingSequenceSteps tm env tasks cs + fixedNodeSteps r ts after +
        cleanupSteps clear (fixedNodeCounters r ts after) ≤ clock.eval n := by
  obtain ⟨budget, bindClock, hb⟩ := coordinateBindingSequence_polynomial tm env tasks hv bound
  let sizes : R → Polynomial Nat := fun _ => budget
  let finalSizes := fixedPrinterCounterPolynomials r ts sizes
  refine ⟨bindClock + fixedNodeClock r ts sizes + cleanupClock clear finalSizes, ?_⟩
  intro n cs hcs
  obtain ⟨hafter, hbind⟩ := hb n cs hcs
  have hprint := fixedNodeSteps_polynomial_bound r ts sizes n
    (coordinateBindingSequenceCounters tm env tasks cs) hafter
  have hfinal := fixedNodeCounters_mono r ts
    (coordinateBindingSequenceCounters tm env tasks cs) (fun q => (sizes q).eval n) hafter
  have hclear := cleanupSteps_mono clear _ _ hfinal
  have he := fixedPrinterCounterPolynomials_eval r ts sizes n
  have hcleanclock : cleanupSteps clear (fixedNodeCounters r ts (fun q => (sizes q).eval n)) =
      (cleanupClock clear finalSizes).eval n := by
    rw [cleanupClock_eval]
    dsimp only [finalSizes]
    rw [he]
  rw [hcleanclock] at hclear
  simpa only [Polynomial.eval_add] using Nat.add_le_add (Nat.add_le_add hbind hprint) hclear

end ShiReversibleGenerator
