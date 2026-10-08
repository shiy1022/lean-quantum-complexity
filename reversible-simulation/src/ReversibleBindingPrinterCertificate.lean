import ReversibleBindingPrinterCleanup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R L : Type} [DecidableEq R]

/-- Fixed finite control, actual polynomial-time emission, and zero private registers in one certificate. -/
theorem bindingPrinterCleanupCode_certificate [Fintype L] (tm : Turing.FinTM2)
    (env : CoordinateBindingRegisters R) (tasks : List (CoordinateBindingTask tm R))
    (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) (clear : List R)
    (caller : L → CounterInstr R L) (stop : L) (hr : r.Valid)
    (hops : ∀ t ∈ ts, ∀ op ∈ t.ops r, op.Valid r.buf r.tmp) (bound : Polynomial Nat) :
    ∃ _finite : Fintype (BindingPrinterCleanupLabels tm env tasks r ts clear L), ∃ clock : Polynomial Nat,
      ∀ n (cs : R → Nat) (ys : List Bool), (∀ q, cs q ≤ bound.eval n) →
        cs env.query = 0 → cs env.tmp = 0 →
        coordinateBindingSequenceCounters tm env tasks cs r.buf = 0 →
        coordinateBindingSequenceCounters tm env tasks cs r.tmp = 0 →
        let after := coordinateBindingSequenceCounters tm env tasks cs
        let final := cleanupCounters clear (fixedNodeCounters r ts after)
        ∃ steps, CounterRun (bindingPrinterCleanupCode tm env tasks r ts clear caller stop)
          ⟨some (bindingPrinterCleanupEntry tm env tasks r ts clear stop), cs, ys⟩ steps
          ⟨some (bindingPrinterCleanupExit tm env tasks r ts clear stop), final,
            fixedNodeBytes r ts after ++ ys⟩ ∧ steps ≤ clock.eval n ∧ ∀ q ∈ clear, final q = 0 := by
  obtain ⟨clock, hc⟩ := coordinateBindingPrinterCleanup_polynomial tm env tasks hv r ts clear bound
  refine ⟨inferInstance, clock, ?_⟩
  intro n cs ys hb hq hx hbuf htmp
  dsimp only
  refine ⟨_, bindingPrinterCleanupCode_run tm env tasks hv r ts clear caller stop hr hops cs hq hx hbuf htmp ys,
    hc n cs hb, ?_⟩
  intro q hq
  exact bindingPrinterCleanup_zero clear _ q hq

end ShiReversibleGenerator
