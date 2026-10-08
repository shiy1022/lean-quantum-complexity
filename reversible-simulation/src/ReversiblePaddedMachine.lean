import ReversiblePaddedFinished
import ReversibleMachineQuantum

set_option autoImplicit false
namespace ShiReversibleTM
open ShiReversible ShiReversibleFormula

/-- The exact fixed-stride workspace, suitable for the generator's scalar header. -/
noncomputable def paddedMachineWorkspace (tm : Turing.FinTM2) (n budget : Nat) : Nat :=
  let cap := n + budget * machinePushBound tm + 1
  configurationWidth tm cap * 18 +
    budget * (configurationWidth tm cap * (tickSizeBound tm + 1)) +
    (2 * cap + 1) * (extractionBitBound tm cap + 1)

noncomputable def paddedRawOutputCircuit (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :=
  let cap := n + budget * machinePushBound tm + 1
  paddedFinishedCircuit (initialForest tm e₀ cap n) (initialForest_length _ _ _ _)
    (tickForest tm cap) (extractionForest tm e₁ cap) (tickForest_length _ _)
    17 (tickSizeBound tm) (extractionBitBound tm cap) budget
    (initialForest_size _ _ _ _) (tickForest_size _ _) (extractionForest_size _ _ _)

theorem paddedRawOutputCircuit_workspace (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :
    paddedFinishedSize (initialForest tm e₀ (n + budget * machinePushBound tm + 1) n)
      (tickForest tm (n + budget * machinePushBound tm + 1))
      (extractionForest tm e₁ (n + budget * machinePushBound tm + 1))
      17 (tickSizeBound tm) (extractionBitBound tm (n + budget * machinePushBound tm + 1)) budget =
      paddedMachineWorkspace tm n budget := by
  simp [paddedFinishedSize, paddedMachineWorkspace]

theorem paddedRawOutputCircuit_eval (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) (x : Bits n)
    (i : Fin (extractionForest tm e₁ (n + budget * machinePushBound tm + 1)).length) :
    (paddedRawOutputCircuit tm e₀ e₁ n budget).eval x i =
      (outputCode (n + budget * machinePushBound tm + 1)
        (((rawTrace tm e₀ n budget budget x (Nat.le_refl _)).cfg.stk tm.k₁).map e₁))[i.val]?.getD false := by
  rw [paddedRawOutputCircuit, paddedFinishedCircuit_eval, forestEvaluate_initial,
    ← rawTrace_initial tm e₀ n budget x, rawTrace_forestAdvance _ _ _ _ _ _ (Nat.le_refl _)]
  exact extractionForest_eval _ e₁ i

theorem paddedRawOutputCircuit_output (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) (x : Bits n) :
    List.ofFn ((paddedRawOutputCircuit tm e₀ e₁ n budget).eval x) =
      outputCode (n + budget * machinePushBound tm + 1)
        (((rawTrace tm e₀ n budget budget x (Nat.le_refl _)).cfg.stk tm.k₁).map e₁) := by
  have hw := outputCode_width (n + budget * machinePushBound tm + 1)
    (((rawTrace tm e₀ n budget budget x (Nat.le_refl _)).cfg.stk tm.k₁).map e₁)
    (by simpa using (rawTrace tm e₀ n budget budget x (Nat.le_refl _)).length_bound tm.k₁)
  apply List.ext_getElem
  · simp only [List.length_ofFn, extractionForest_length, hw]
  · intro j hj hk
    rw [List.getElem_ofFn, paddedRawOutputCircuit_eval]
    simp [List.getElem?_eq_getElem hk]

theorem polyTime_paddedRawOutputCircuit_output {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f)
    (n : Nat) (x : Bits n) :
    List.ofFn ((paddedRawOutputCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n)).eval x) =
      outputCode (n + M.time.eval n * machinePushBound M.tm + 1) (f (List.ofFn x)) := by
  rw [paddedRawOutputCircuit_output]
  have h : (rawTrace M.tm M.inputAlphabet n (M.time.eval n) (M.time.eval n) x (Nat.le_refl _)).cfg =
      Turing.haltList M.tm ((f (List.ofFn x)).map M.outputAlphabet.invFun) := by
    simpa [rawTrace, List.map_ofFn, Function.comp_def] using polyTime_padded_run M (List.ofFn x)
  rw [h]
  simp [Turing.haltList, List.map_map, Function.comp_def]

theorem polyTime_paddedRawOutputCircuit_decoded {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f)
    (n : Nat) (x : Bits n) :
    outputDecode (List.ofFn ((paddedRawOutputCircuit M.tm M.inputAlphabet M.outputAlphabet n
      (M.time.eval n)).eval x)) = f (List.ofFn x) := by
  rw [polyTime_paddedRawOutputCircuit_output, outputDecode_code]

theorem polyTime_paddedRawOutputCircuit_quantum_clean {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f)
    (n : Nat) (x : Bits n) :
    quantumRun (paddedRawOutputCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n)).reversible
      (basis (inputMemory x, fun _ => false)) =
      basis (inputMemory x, fun i => (outputCode (n + M.time.eval n * machinePushBound M.tm + 1)
        (f (List.ofFn x)))[i.val]?.getD false) := by
  have he : (paddedRawOutputCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n)).eval x =
      (fun i => (outputCode (n + M.time.eval n * machinePushBound M.tm + 1)
        (f (List.ofFn x)))[i.val]?.getD false) := by
    funext i
    have h := congrArg (fun xs : List Bool => xs[i.val]?.getD false)
      (polyTime_paddedRawOutputCircuit_output M n x)
    simpa only [List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some] using h
  simpa only [he] using
    (paddedRawOutputCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n)).quantum_clean_correct x

/-- Exact workspace is polynomial, not just bounded by an uncomputed forest-size sum. -/
theorem paddedMachineWorkspace_polynomial (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n, paddedMachineWorkspace tm n (time.eval n) = p.eval n := by
  classical
  obtain ⟨q, hq⟩ := clockedConfigurationWidth_polynomial tm time
  let cap : Polynomial Nat := Polynomial.X + time * Polynomial.C (machinePushBound tm) + Polynomial.C 1
  have hc (n : Nat) : cap.eval n = n + time.eval n * machinePushBound tm + 1 := by simp [cap]
  let eb : Polynomial Nat := Polynomial.C 1 + (cap + Polynomial.C 1) *
    Polynomial.C (10 + Fintype.card (Option (MachineSymbol tm)) * 7)
  refine ⟨q * Polynomial.C 18 + time * (q * Polynomial.C (tickSizeBound tm + 1)) +
    (Polynomial.C 2 * cap + Polynomial.C 1) * (eb + Polynomial.C 1), ?_⟩
  intro n
  simp [paddedMachineWorkspace, hq n, eb, hc, extractionBitBound]


theorem paddedRawOutputCircuit_gates_polynomial (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      (paddedRawOutputCircuit tm e₀ e₁ n (time.eval n)).reversible.length ≤ p.eval n := by
  obtain ⟨q, hq⟩ := paddedMachineWorkspace_polynomial tm time
  let cap : Polynomial Nat := Polynomial.X + time * Polynomial.C (machinePushBound tm) + Polynomial.C 1
  refine ⟨Polynomial.C 4 * q + Polynomial.C 2 * cap + Polynomial.C 1, ?_⟩
  intro n
  apply ((paddedRawOutputCircuit tm e₀ e₁ n (time.eval n)).size_bound).trans
  simp only [paddedRawOutputCircuit, paddedRawOutputCircuit_workspace, hq, extractionForest_length]
  simp [cap, Nat.add_assoc]

theorem paddedRawOutputCircuit_wires_polynomial (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      n + paddedMachineWorkspace tm n (time.eval n) +
        (2 * (n + time.eval n * machinePushBound tm + 1) + 1) = p.eval n := by
  obtain ⟨q, hq⟩ := paddedMachineWorkspace_polynomial tm time
  let cap : Polynomial Nat := Polynomial.X + time * Polynomial.C (machinePushBound tm) + Polynomial.C 1
  refine ⟨Polynomial.X + q + (Polynomial.C 2 * cap + Polynomial.C 1), ?_⟩
  intro n
  simp [hq, cap]

end ShiReversibleTM

namespace ShiReversibleGateBridge
open ShiReversible ShiReversibleTM

noncomputable def paddedMachineQuantumCircuit (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :=
  substitute ((paddedRawOutputCircuit tm e₀ e₁ n budget).reversible.map flatInstruction)

theorem polyTime_paddedMachineQuantumCircuit_clean {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f)
    (n : Nat) (x : Bits n) :
    ShiShallow.runLayered
      (paddedMachineQuantumCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n))
      (flatBasis (inputMemory x, fun _ => false)) =
      flatBasis (inputMemory x, fun i => (outputCode (n + M.time.eval n * machinePushBound M.tm + 1)
        (f (List.ofFn x)))[i.val]?.getD false) := by
  unfold paddedMachineQuantumCircuit flatBasis
  rw [flatQuantum_correct, polyTime_paddedRawOutputCircuit_quantum_clean]

theorem paddedMachineQuantumCircuit_layerOk (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :
    ∀ l ∈ paddedMachineQuantumCircuit tm e₀ e₁ n budget, ShiShallow.LayerOk l :=
  substitute_layerOk _


theorem paddedMachineQuantumCircuit_depth_polynomial (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      ShiShallow.depth (paddedMachineQuantumCircuit tm e₀ e₁ n (time.eval n)) ≤ p.eval n := by
  obtain ⟨q, hq⟩ := paddedRawOutputCircuit_gates_polynomial tm e₀ e₁ time
  refine ⟨Polynomial.C 37 * q, ?_⟩
  intro n
  apply (substitute_depth _).trans
  simpa only [List.length_map, Polynomial.eval_mul, Polynomial.eval_C] using
    Nat.mul_le_mul_left 37 (hq n)

theorem paddedMachineQuantumCircuit_gates_polynomial (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      (paddedMachineQuantumCircuit tm e₀ e₁ n (time.eval n)).flatten.length ≤ p.eval n := by
  obtain ⟨p, hp⟩ := paddedMachineQuantumCircuit_depth_polynomial tm e₀ e₁ time
  refine ⟨p, ?_⟩
  intro n
  rw [paddedMachineQuantumCircuit, substitute_gateCount]
  exact hp n

end ShiReversibleGateBridge
