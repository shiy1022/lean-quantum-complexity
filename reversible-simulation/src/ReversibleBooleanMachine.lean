import ReversibleMachineQuantum

set_option autoImplicit false
namespace ShiReversible

/-- Select external outputs before compute-copy-uncompute; unselected results stay in workspace. -/
def SingleAssignmentCircuit.selectOutputs {n k m j : Nat} (c : SingleAssignmentCircuit n k m)
    (select : Fin j → Fin m) : SingleAssignmentCircuit n k j where
  nodes := c.nodes
  targets_distinct := c.targets_distinct
  targets_auxiliary := c.targets_auxiliary
  nodes_length := c.nodes_length
  read := c.read ∘ select

@[simp] theorem SingleAssignmentCircuit.selectOutputs_eval {n k m j : Nat}
    (c : SingleAssignmentCircuit n k m) (select : Fin j → Fin m) (x : Bits n) (i : Fin j) :
    (c.selectOutputs select).eval x i = c.eval x (select i) := rfl

end ShiReversible

namespace ShiReversibleTM
open ShiReversible ShiReversibleFormula

/-- A singleton Boolean string has payload index two, after its length bit and delimiter. -/
def booleanPayloadIndex (tm : Turing.FinTM2) (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :
    Fin (extractionForest tm e₁ (n + budget * machinePushBound tm + 1)).length :=
  ⟨2, by rw [extractionForest_length]; omega⟩

noncomputable def rawBooleanCircuit (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :=
  (rawOutputCircuit tm e₀ e₁ n budget).selectOutputs
    (fun _ : Fin 1 => booleanPayloadIndex tm e₁ n budget)

theorem polyTime_rawBooleanCircuit_eval {f : List Bool → Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun xs => [f xs])) (n : Nat) (x : Bits n) (i : Fin 1) :
    (rawBooleanCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n)).eval x i =
      f (List.ofFn x) := by
  have he := polyTime_rawOutputCircuit_output M n x
  have hp := congrArg (fun xs : List Bool => xs[2]?.getD false) he
  have hidx : 2 < (extractionForest M.tm M.outputAlphabet
      (n + M.time.eval n * machinePushBound M.tm + 1)).length := by
    simpa only [booleanPayloadIndex] using
      (booleanPayloadIndex M.tm M.outputAlphabet n (M.time.eval n)).isLt
  rw [List.getElem?_ofFn, dif_pos hidx] at hp
  simpa [rawBooleanCircuit, SingleAssignmentCircuit.selectOutputs_eval,
    booleanPayloadIndex, outputCode, List.append_assoc] using hp

/-- The single external output is the Boolean value; all markers and other targets are uncomputed. -/
theorem polyTime_rawBooleanCircuit_clean {f : List Bool → Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun xs => [f xs])) (n : Nat) (x : Bits n) :
    quantumRun (rawBooleanCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n)).reversible
      (basis (inputMemory x, fun _ => false)) =
      basis (inputMemory x, fun _ : Fin 1 => f (List.ofFn x)) := by
  have he : (rawBooleanCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n)).eval x =
      (fun _ : Fin 1 => f (List.ofFn x)) := by
    funext i
    exact polyTime_rawBooleanCircuit_eval M n x i
  simpa only [he] using
    (rawBooleanCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n)).quantum_clean_correct x

end ShiReversibleTM

namespace ShiReversibleGateBridge
open ShiReversible ShiReversibleTM

noncomputable def booleanMachineQuantumCircuit (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :=
  substitute ((rawBooleanCircuit tm e₀ e₁ n budget).reversible.map flatInstruction)

/-- Exact one-output-qubit machine simulation in the established gate semantics. -/
theorem polyTime_booleanMachineQuantumCircuit_clean {f : List Bool → Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun xs => [f xs])) (n : Nat) (x : Bits n) :
    ShiShallow.runLayered
      (booleanMachineQuantumCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n))
      (flatBasis (inputMemory x, fun _ => false)) =
      flatBasis (inputMemory x, fun _ : Fin 1 => f (List.ofFn x)) := by
  unfold booleanMachineQuantumCircuit flatBasis
  rw [flatQuantum_correct, polyTime_rawBooleanCircuit_clean]

theorem booleanMachineQuantumCircuit_layerOk (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :
    ∀ l ∈ booleanMachineQuantumCircuit tm e₀ e₁ n budget, ShiShallow.LayerOk l :=
  substitute_layerOk _

theorem booleanMachineQuantumCircuit_depth_polynomial (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      ShiShallow.depth (booleanMachineQuantumCircuit tm e₀ e₁ n (time.eval n)) ≤ p.eval n := by
  obtain ⟨q, hq⟩ := rawOutputCircuit_workspace_polynomial tm e₀ e₁ time
  refine ⟨Polynomial.C 37 * (Polynomial.C 4 * q + Polynomial.C 1), ?_⟩
  intro n
  have hg := (rawBooleanCircuit tm e₀ e₁ n (time.eval n)).size_bound
  have hs : (rawBooleanCircuit tm e₀ e₁ n (time.eval n)).reversible.length ≤ 4 * q.eval n + 1 := by
    have h := hq n
    exact hg.trans (by omega)
  apply (substitute_depth _).trans
  simpa only [List.length_map, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C] using
    Nat.mul_le_mul_left 37 hs

theorem booleanMachineQuantumCircuit_gates_polynomial (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      (booleanMachineQuantumCircuit tm e₀ e₁ n (time.eval n)).flatten.length ≤ p.eval n := by
  obtain ⟨p, hp⟩ := booleanMachineQuantumCircuit_depth_polynomial tm e₀ e₁ time
  refine ⟨p, ?_⟩
  intro n
  rw [booleanMachineQuantumCircuit, substitute_gateCount]
  exact hp n

end ShiReversibleGateBridge
