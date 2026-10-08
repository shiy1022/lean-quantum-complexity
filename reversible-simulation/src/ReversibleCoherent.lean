import ReversibleCircuitTheorem

set_option autoImplicit false

namespace ShiReversible

/-- Clean simulation preserves coherence across arbitrary superpositions of classical inputs. -/
theorem SingleAssignmentCircuit.coherent_clean_correct {n k m : Nat}
    (c : SingleAssignmentCircuit n k m) (amplitude : Bits n → ℂ) :
    quantumRun c.reversible
        (fun z => ∑ x, amplitude x * basis (inputMemory x, fun _ => false) z) =
      (fun z => ∑ x, amplitude x * basis (inputMemory x, c.eval x) z) := by
  funext z
  change (∑ x, amplitude x *
    quantumRun c.reversible (basis (inputMemory x, fun _ => false)) z) = _
  apply Finset.sum_congr rfl
  intro x hx
  rw [c.quantum_clean_correct]

end ShiReversible
