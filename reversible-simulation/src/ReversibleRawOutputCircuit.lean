import ReversibleMachineExtraction
import ReversibleFinishedIteration
import ReversibleRawInputCircuit

set_option autoImplicit false
namespace ShiReversibleTM
open ShiReversible ShiReversibleFormula

/-- Initialization, all clocked steps, and string extraction share one assignment program. -/
noncomputable def rawOutputCircuit (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :=
  finishedCircuit (initialForest tm e₀ (n + budget * machinePushBound tm + 1) n)
    (initialForest_length _ _ _ _) (tickForest tm (n + budget * machinePushBound tm + 1))
    (tickForest_length _ _) budget (extractionForest tm e₁ (n + budget * machinePushBound tm + 1))

theorem rawOutputCircuit_eval (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) (x : Bits n)
    (i : Fin (extractionForest tm e₁ (n + budget * machinePushBound tm + 1)).length) :
    (rawOutputCircuit tm e₀ e₁ n budget).eval x i =
      (outputCode (n + budget * machinePushBound tm + 1)
        (((rawTrace tm e₀ n budget budget x (Nat.le_refl _)).cfg.stk tm.k₁).map e₁))[i.val]?.getD false := by
  rw [rawOutputCircuit, finishedCircuit_eval, forestEvaluate_initial,
    ← rawTrace_initial tm e₀ n budget x,
    rawTrace_forestAdvance _ _ _ _ _ _ (Nat.le_refl _)]
  exact extractionForest_eval _ e₁ i

theorem rawOutputCircuit_output (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) (x : Bits n) :
    List.ofFn ((rawOutputCircuit tm e₀ e₁ n budget).eval x) =
      outputCode (n + budget * machinePushBound tm + 1)
        (((rawTrace tm e₀ n budget budget x (Nat.le_refl _)).cfg.stk tm.k₁).map e₁) := by
  have hw := outputCode_width (n + budget * machinePushBound tm + 1)
    (((rawTrace tm e₀ n budget budget x (Nat.le_refl _)).cfg.stk tm.k₁).map e₁)
    (by simpa using (rawTrace tm e₀ n budget budget x (Nat.le_refl _)).length_bound tm.k₁)
  apply List.ext_getElem
  · simp only [List.length_ofFn, extractionForest_length, hw]
  · intro j hj hk
    rw [List.getElem_ofFn, rawOutputCircuit_eval]
    simp [List.getElem?_eq_getElem hk]

/-- The generated output bits are exactly the established serialization of the original function. -/
theorem polyTime_rawOutputCircuit_output {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f)
    (n : Nat) (x : Bits n) :
    List.ofFn ((rawOutputCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n)).eval x) =
      outputCode (n + M.time.eval n * machinePushBound M.tm + 1) (f (List.ofFn x)) := by
  rw [rawOutputCircuit_output]
  have h : (rawTrace M.tm M.inputAlphabet n (M.time.eval n) (M.time.eval n) x (Nat.le_refl _)).cfg =
      Turing.haltList M.tm ((f (List.ofFn x)).map M.outputAlphabet.invFun) := by
    simpa [rawTrace, List.map_ofFn, Function.comp_def] using polyTime_padded_run M (List.ofFn x)
  rw [h]
  simp [Turing.haltList, List.map_map, Function.comp_def]

theorem polyTime_rawOutputCircuit_decoded {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f)
    (n : Nat) (x : Bits n) :
    outputDecode (List.ofFn ((rawOutputCircuit M.tm M.inputAlphabet M.outputAlphabet n
      (M.time.eval n)).eval x)) = f (List.ofFn x) := by
  rw [polyTime_rawOutputCircuit_output, outputDecode_code]

/-- Input is preserved and every initialization, time-slice, and extraction ancilla is cleared. -/
theorem polyTime_rawOutputCircuit_quantum_clean_correct {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f)
    (n : Nat) (x : Bits n) :
    quantumRun (rawOutputCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n)).reversible
      (basis (inputMemory x, fun _ => false)) =
      basis (inputMemory x, fun i => (outputCode (n + M.time.eval n * machinePushBound M.tm + 1)
        (f (List.ofFn x)))[i.val]?.getD false) := by
  have he : (rawOutputCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n)).eval x =
      (fun i => (outputCode (n + M.time.eval n * machinePushBound M.tm + 1)
        (f (List.ofFn x)))[i.val]?.getD false) := by
    funext i
    have h := congrArg (fun xs : List Bool => xs[i.val]?.getD false)
      (polyTime_rawOutputCircuit_output M n x)
    simpa only [List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some] using h
  simpa only [he] using
    (rawOutputCircuit M.tm M.inputAlphabet M.outputAlphabet n (M.time.eval n)).quantum_clean_correct x

theorem rawOutputCircuit_workspace_bound (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :
    finishedSize (initialForest tm e₀ (n + budget * machinePushBound tm + 1) n)
      (tickForest tm (n + budget * machinePushBound tm + 1))
      (extractionForest tm e₁ (n + budget * machinePushBound tm + 1)) budget ≤
    configurationWidth tm (n + budget * machinePushBound tm + 1) * 17 +
      budget * (configurationWidth tm (n + budget * machinePushBound tm + 1) * tickSizeBound tm) +
      (2 * (n + budget * machinePushBound tm + 1) + 1) *
        extractionBitBound tm (n + budget * machinePushBound tm + 1) :=
  Nat.add_le_add (rawInputCircuit_workspace_bound tm e₀ n budget) (extractionForest_workspace tm e₁ _)

theorem rawOutputCircuit_workspace_polynomial (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n : Nat,
      finishedSize (initialForest tm e₀ (n + time.eval n * machinePushBound tm + 1) n)
        (tickForest tm (n + time.eval n * machinePushBound tm + 1))
        (extractionForest tm e₁ (n + time.eval n * machinePushBound tm + 1)) (time.eval n) ≤ p.eval n := by
  classical
  obtain ⟨q, hq⟩ := clockedConfigurationWidth_polynomial tm time
  let cap : Polynomial Nat := Polynomial.X + time * Polynomial.C (machinePushBound tm) + Polynomial.C 1
  have hc (n : Nat) : cap.eval n = n + time.eval n * machinePushBound tm + 1 := by simp [cap]
  refine ⟨Polynomial.C 17 * q + time * q * Polynomial.C (tickSizeBound tm) +
    (Polynomial.C 2 * cap + Polynomial.C 1) * (Polynomial.C 1 + (cap + Polynomial.C 1) *
      Polynomial.C (10 + Fintype.card (Option (MachineSymbol tm)) * 7)), ?_⟩
  intro n
  apply (rawOutputCircuit_workspace_bound tm e₀ e₁ n (time.eval n)).trans
  rw [hq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hc, extractionBitBound]
  ring_nf <;> exact le_rfl

theorem rawOutputCircuit_gates_polynomial (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n : Nat,
      (rawOutputCircuit tm e₀ e₁ n (time.eval n)).reversible.length ≤ p.eval n := by
  obtain ⟨q, hq⟩ := rawOutputCircuit_workspace_polynomial tm e₀ e₁ time
  let cap : Polynomial Nat := Polynomial.X + time * Polynomial.C (machinePushBound tm) + Polynomial.C 1
  refine ⟨Polynomial.C 4 * q + Polynomial.C 2 * cap + Polynomial.C 1, ?_⟩
  intro n
  apply ((rawOutputCircuit tm e₀ e₁ n (time.eval n)).size_bound).trans
  have h := Nat.mul_le_mul_left 4 (hq n)
  simp only [rawOutputCircuit, extractionForest_length]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  simpa [cap, Nat.add_assoc] using Nat.add_le_add_right h (2 * (n + time.eval n * machinePushBound tm + 1) + 1)

theorem rawOutputCircuit_wires_polynomial (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (e₁ : tm.Γ tm.k₁ ≃ Bool) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n : Nat,
      n + finishedSize (initialForest tm e₀ (n + time.eval n * machinePushBound tm + 1) n)
        (tickForest tm (n + time.eval n * machinePushBound tm + 1))
        (extractionForest tm e₁ (n + time.eval n * machinePushBound tm + 1)) (time.eval n) +
        (extractionForest tm e₁ (n + time.eval n * machinePushBound tm + 1)).length ≤ p.eval n := by
  obtain ⟨q, hq⟩ := rawOutputCircuit_workspace_polynomial tm e₀ e₁ time
  let cap : Polynomial Nat := Polynomial.X + time * Polynomial.C (machinePushBound tm) + Polynomial.C 1
  refine ⟨Polynomial.X + q + Polynomial.C 2 * cap + Polynomial.C 1, ?_⟩
  intro n
  have h := Nat.add_le_add_left (hq n) n
  simp only [extractionForest_length, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  simpa [cap, Nat.add_assoc] using Nat.add_le_add_right h (2 * (n + time.eval n * machinePushBound tm + 1) + 1)

end ShiReversibleTM
