import ReversibleRegisterFlattening
import ReversibleRawOutputCircuit

set_option autoImplicit false
namespace ShiReversibleGateBridge
open ShiReversible ShiReversibleTM

def flatBasis {n m : Nat} (s : Registers n m) : ShiShallow.QState (n + m) :=
  fun x => basis s ((registerEquiv n m).symm x)

theorem flatBasis_eq {n m : Nat} (s : Registers n m) :
    flatBasis s = fun x => if x = registerEquiv n m s then 1 else 0 := by
  funext x
  simp [flatBasis, basis, Equiv.symm_apply_eq]

noncomputable def machineQuantumCircuit (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :=
  substitute ((rawOutputCircuit tm e₀ e₁ n budget).reversible.map flatInstruction)

/-- Clean exact string computation in the established H/S/T/X/CNOT state semantics. -/
theorem polyTime_machineQuantumCircuit_clean {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f)
    (n : Nat) (x : Bits n) :
    ShiShallow.runLayered
      (machineQuantumCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n))
      (flatBasis (inputMemory x, fun _ => false)) =
      flatBasis (inputMemory x, fun i => (outputCode (n + M.time.eval n * machinePushBound M.tm + 1)
        (f (List.ofFn x)))[i.val]?.getD false) := by
  unfold machineQuantumCircuit flatBasis
  rw [flatQuantum_correct, polyTime_rawOutputCircuit_quantum_clean_correct]

theorem machineQuantumCircuit_layerOk (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :
    ∀ l ∈ machineQuantumCircuit tm e₀ e₁ n budget, ShiShallow.LayerOk l :=
  substitute_layerOk _

theorem machineQuantumCircuit_depth_polynomial (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n : Nat,
      ShiShallow.depth (machineQuantumCircuit tm e₀ e₁ n (time.eval n)) ≤ p.eval n := by
  obtain ⟨q, hq⟩ := rawOutputCircuit_gates_polynomial tm e₀ e₁ time
  refine ⟨Polynomial.C 37 * q, ?_⟩
  intro n
  apply (substitute_depth _).trans
  simpa only [List.length_map, Polynomial.eval_mul, Polynomial.eval_C] using
    Nat.mul_le_mul_left 37 (hq n)

theorem machineQuantumCircuit_gates_polynomial (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n : Nat,
      (machineQuantumCircuit tm e₀ e₁ n (time.eval n)).flatten.length ≤ p.eval n := by
  obtain ⟨p, hp⟩ := machineQuantumCircuit_depth_polynomial tm e₀ e₁ time
  refine ⟨p, ?_⟩
  intro n
  rw [machineQuantumCircuit, substitute_gateCount]
  exact hp n

end ShiReversibleGateBridge
