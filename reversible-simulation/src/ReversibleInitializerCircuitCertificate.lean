import ReversibleInitializerQuantumEncoding
import ReversibleRankedInitializerPrelude

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- One actual finite program has the correct circuit bytes, exact circuit length, and a polynomial clock. -/
theorem rankedInitializer_circuit_certificate (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (time : Polynomial Nat) (backward : Bool) :
    ∃ clock : Polynomial Nat, ∀ n (ys : List Bool),
      let capacity := (initializationCapacityPolynomial tm time).eval n
      let cs := initializationPreludeCounters tm time n
      let layers := initializationQuantumLayers tm e capacity n backward
      let count := initializerSequenceSteps (rankedInitializerComponents tm e backward) n cs ys
      let counters := initializerSequenceCounters (rankedInitializerComponents tm e backward) n cs ys
      CounterRun (rankedInitializerCode tm e backward)
        ⟨some (initializerSequenceEntry (rankedInitializerComponents tm e backward)), cs, ys⟩ count
        ⟨some (initializerSequenceExit (rankedInitializerComponents tm e backward)), counters,
          (layers.map ShiBQP.encLayer).flatten ++ ys⟩ ∧
      count ≤ clock.eval n ∧ counters (.inr 10) = layers.length := by
  obtain ⟨clock, hc⟩ := rankedInitializer_prelude_clock tm e backward time
  refine ⟨clock, ?_⟩
  intro n ys
  dsimp only
  have hn : initializationPreludeCounters tm time n (.inl 0) = n := by
    simp [initializationPreludeCounters, resourceResult_raw]
  have hcap : initializationPreludeCounters tm time n (.inl 2) =
      (initializationCapacityPolynomial tm time).eval n := by
    simp [initializationPreludeCounters, initializationCapacityPolynomial, resourceResult_capacity]
  have he := rankedInitializer_quantum_encoding tm e
    ((initializationCapacityPolynomial tm time).eval n) n backward
    (initializationPreludeCounters tm time n) ys hn hcap
  have hr := rankedInitializer_run tm e backward n (initializationPreludeCounters tm time n) ys hn
    (by simp [initializationPreludeCounters, workspaceResult_buffer])
    (by simp [initializationPreludeCounters, workspaceResult_scratch])
  rw [he.1] at hr
  refine ⟨hr, hc n ys, ?_⟩
  simpa [initializationPreludeCounters] using he.2

end ShiReversibleGenerator
