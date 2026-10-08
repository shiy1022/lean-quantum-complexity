import ReversibleRawSubstitutionLayers
import ReversibleRankedInitializerExactLayers
import ReversibleRankedInitializerForest

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula ShiReversible ShiReversibleGateBridge

noncomputable def initializationRawNodes (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) : List RawAssignment :=
  paddedForestCompile (fun i : Fin n => i.val) n 17 (initialForest tm e capacity n)

noncomputable def initializationCircuitWires (tm : Turing.FinTM2) (capacity n : Nat) : Nat :=
  n + configurationWidth tm capacity * 18

theorem initializationRawNodes_bounded (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) :
    ∀ a ∈ initializationRawNodes tm e capacity n, a.target < initializationCircuitWires tm capacity n := by
  intro a ha
  have h := (paddedForestCompile_interval (initialForest tm e capacity n) (fun i : Fin n => i.val)
    n 17 (initialForest_size tm e capacity n) a ha).2
  simpa only [initialForest_length, initializationCircuitWires] using h

theorem initializationRawNodes_topological (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) : ∀ a ∈ initializationRawNodes tm e capacity n, a.Topological :=
  paddedForestCompile_topological (initialForest tm e capacity n) (fun i : Fin n => i.val) n 17
    (initialForest_size tm e capacity n) (fun i => i.isLt)

noncomputable def initializationQuantumLayers (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) : ShiShallow.Layered (initializationCircuitWires tm capacity n) :=
  let gates := compileAssignments (boundProgram (initializationCircuitWires tm capacity n)
    (initializationRawNodes tm e capacity n) (initializationRawNodes_bounded tm e capacity n)
    (initializationRawNodes_topological tm e capacity n))
  substitute (if backward then gates.reverse else gates)

/-- The emitted bytes are exactly the established singleton quantum-layer encoding. -/
theorem initializationQuantumLayers_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) :
    ((if backward then (initializationRawNodes tm e capacity n).reverse
      else initializationRawNodes tm e capacity n).map (rawAssignmentPayload backward)).flatten =
      ((initializationQuantumLayers tm e capacity n backward).map ShiBQP.encLayer).flatten := by
  exact rawProgramPayload_substitute _ _ (initializationRawNodes_bounded tm e capacity n)
    (initializationRawNodes_topological tm e capacity n)
    (paddedForestCompile_distinct_controls _ _ _ _) backward

theorem initializationQuantumLayers_length (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) :
    (initializationQuantumLayers tm e capacity n backward).length =
      initializationForestLayerCount tm e capacity n := by
  rw [initializationForestLayerCount_raw]
  exact rawProgram_substitute_length_both _ (initializationRawNodes_bounded tm e capacity n)
    (initializationRawNodes_topological tm e capacity n)
    (paddedForestCompile_distinct_controls _ _ _ _) backward

/-- The actual initializer output and its actual layer counter refer to the same quantum circuit. -/
theorem rankedInitializer_quantum_encoding (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) (cs : InitializationRegister → Nat) (ys : List Bool)
    (hn : cs (.inl 0) = n) (hcap : cs (.inl 2) = capacity) :
    initializerSequenceOutput (rankedInitializerComponents tm e backward) n cs ys =
        ((initializationQuantumLayers tm e capacity n backward).map ShiBQP.encLayer).flatten ++ ys ∧
      initializerSequenceCounters (rankedInitializerComponents tm e backward) n cs ys (.inr 10) =
        cs (.inr 10) + (initializationQuantumLayers tm e capacity n backward).length := by
  constructor
  · rw [rankedInitializer_output_forest tm e backward capacity n cs ys hn hcap]
    exact congrArg (fun bytes => bytes ++ ys) (initializationQuantumLayers_payload tm e capacity n backward)
  · rw [initializationQuantumLayers_length]
    exact rankedInitializer_exact_layers tm e capacity n backward cs ys hn hcap

end ShiReversibleGenerator
