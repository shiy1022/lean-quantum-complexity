import ReversibleInitialization
import ReversiblePreparedIteration
import ReversibleClockedCircuit

set_option autoImplicit false
namespace ShiReversibleTM
open ShiReversible ShiReversibleFormula

/-- The trace has a width determined by the declared input length, never by the input values. -/
noncomputable def rawTrace (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (n budget t : Nat) (x : Bits n) (ht : t ≤ budget) :
    BoundedCfg tm (n + budget * machinePushBound tm + 1) where
  cfg := advance tm t (Turing.initList tm (List.ofFn (fun i => e.symm (x i))))
  length_bound k := by
    have hs := initial_trace_stack_length tm t (List.ofFn (fun i => e.symm (x i))) k
    simp only [List.length_ofFn] at hs
    have hm := Nat.mul_le_mul_right (machinePushBound tm) ht
    omega
  alphabet := advance_alphabet tm t _

theorem rawTrace_initial (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (n budget : Nat) (x : Bits n) :
    (rawTrace tm e n budget 0 x (Nat.zero_le _)).encode =
      initialFiniteCfg tm (n + budget * machinePushBound tm + 1) (List.ofFn (fun i => e.symm (x i))) := by
  have h : (List.ofFn (fun i => e.symm (x i))).length ≤ n + budget * machinePushBound tm + 1 := by simp; omega
  have he := initialBoundedCfg_encode tm (n + budget * machinePushBound tm + 1) _ h
  have hc : rawTrace tm e n budget 0 x (Nat.zero_le _) = initialBoundedCfg tm _ _ h := by
    apply BoundedCfg.ext
    rfl
  rw [hc]
  exact he

theorem rawTrace_tickRoom (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (n budget t : Nat) (x : Bits n) (ht : t < budget) :
    TickRoom (n + budget * machinePushBound tm + 1) (rawTrace tm e n budget t x (Nat.le_of_lt ht)).cfg := by
  intro k
  have hs := initial_trace_stack_length tm t (List.ofFn (fun i => e.symm (x i))) k
  simp only [List.length_ofFn] at hs
  have hm := Nat.mul_le_mul_right (machinePushBound tm) (Nat.succ_le_of_lt ht)
  rw [Nat.succ_mul] at hm
  change ((advance tm t (Turing.initList tm _)).stk k).length + machinePushBound tm ≤ _
  omega

theorem forestEvaluate_initial (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (x : Bits n) :
    forestEvaluate (initialForest tm e capacity n) (initialForest_length _ _ _ _) x =
      (initialFiniteCfg tm capacity (List.ofFn (fun i => e.symm (x i)))).bitEncode := by
  funext i
  exact initialForest_eval tm e capacity n x ⟨i.val, by simpa using i.isLt⟩

theorem rawTrace_forestAdvance (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (n budget t : Nat) (x : Bits n) (ht : t ≤ budget) :
    forestAdvance (tickForest tm (n + budget * machinePushBound tm + 1)) (tickForest_length _ _) t
      (rawTrace tm e n budget 0 x (Nat.zero_le _)).encode.bitEncode =
      (rawTrace tm e n budget t x ht).encode.bitEncode := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hl : t < budget := by omega
    rw [forestAdvance_succ_last, ih (Nat.le_of_lt hl)]
    funext i
    have h := tickForest_eval (rawTrace tm e n budget t x (Nat.le_of_lt hl))
      (rawTrace_tickRoom tm e n budget t x hl) ⟨i.val, by simpa using i.isLt⟩
    have hd : (rawTrace tm e n budget t x (Nat.le_of_lt hl)).tick
        (rawTrace_tickRoom tm e n budget t x hl) = rawTrace tm e n budget (t + 1) x ht := by
      apply BoundedCfg.ext
      rfl
    rw [hd] at h
    exact h

noncomputable def rawInputCircuit (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (n budget : Nat) :=
  preparedCircuit (initialForest tm e (n + budget * machinePushBound tm + 1) n) (initialForest_length _ _ _ _)
    (tickForest tm (n + budget * machinePushBound tm + 1)) (tickForest_length _ _) budget

theorem rawInputCircuit_eval (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (n budget : Nat) (x : Bits n) :
    (rawInputCircuit tm e n budget).eval x = (rawTrace tm e n budget budget x (Nat.le_refl _)).encode.bitEncode := by
  rw [rawInputCircuit, preparedCircuit_eval, forestEvaluate_initial, ← rawTrace_initial tm e n budget x,
    rawTrace_forestAdvance _ _ _ _ _ _ (Nat.le_refl _)]

/-- Raw input is preserved; all initialization and time-slice workspace returns to zero. -/
theorem rawInputCircuit_quantum_clean_correct (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (n budget : Nat) (x : Bits n) :
    quantumRun (rawInputCircuit tm e n budget).reversible
      (basis (inputMemory x, fun _ => false)) =
      basis (inputMemory x, (rawTrace tm e n budget budget x (Nat.le_refl _)).encode.bitEncode) := by
  simpa only [rawInputCircuit_eval] using (rawInputCircuit tm e n budget).quantum_clean_correct x

/-- The actual raw-input circuit computes the certificate's final configuration. -/
theorem polyTime_rawInputCircuit_output {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f)
    (n : Nat) (x : Bits n) :
    (FiniteCfg.bitParse M.tm (n + M.time.eval n * machinePushBound M.tm + 1)
      ((rawInputCircuit M.tm M.inputAlphabet n (M.time.eval n)).eval x)).decode =
      Turing.haltList M.tm ((f (List.ofFn x)).map M.outputAlphabet.invFun) := by
  rw [rawInputCircuit_eval, BoundedCfg.bitDecode_encode]
  simpa [rawTrace, List.map_ofFn, Function.comp_def] using polyTime_padded_run M (List.ofFn x)

theorem rawInputCircuit_workspace_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (n budget : Nat) :
    preparedSize (initialForest tm e (n + budget * machinePushBound tm + 1) n)
      (tickForest tm (n + budget * machinePushBound tm + 1)) budget ≤
    configurationWidth tm (n + budget * machinePushBound tm + 1) * 17 +
      budget * (configurationWidth tm (n + budget * machinePushBound tm + 1) * tickSizeBound tm) :=
  preparedSize_bound _ (initialForest_length _ _ _ _) _ (tickForest_length _ _) budget 17 (tickSizeBound tm)
    (initialForest_size _ _ _ _) (tickForest_size _ _)

theorem rawInputCircuit_workspace_polynomial (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n : Nat,
      preparedSize (initialForest tm e (n + time.eval n * machinePushBound tm + 1) n)
        (tickForest tm (n + time.eval n * machinePushBound tm + 1)) (time.eval n) ≤ p.eval n := by
  obtain ⟨q, hq⟩ := clockedConfigurationWidth_polynomial tm time
  refine ⟨Polynomial.C 17 * q + Polynomial.C (tickSizeBound tm) * time * q, ?_⟩
  intro n
  apply (rawInputCircuit_workspace_bound tm e n (time.eval n)).trans
  rw [hq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  ring_nf <;> exact le_rfl

theorem rawInputCircuit_size_polynomial (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n : Nat,
      (rawInputCircuit tm e n (time.eval n)).reversible.length ≤ p.eval n := by
  obtain ⟨q, hq⟩ := clockedConfigurationWidth_polynomial tm time
  obtain ⟨p, hp⟩ := rawInputCircuit_workspace_polynomial tm e time
  refine ⟨Polynomial.C 4 * p + q, ?_⟩
  intro n
  apply (rawInputCircuit tm e n (time.eval n)).size_bound.trans
  have hs := Nat.add_le_add (Nat.mul_le_mul_left 4 (hp n)) (Nat.le_of_eq (hq n))
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using hs

theorem rawInputCircuit_clean_correct (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (n budget : Nat) (x : Bits n) (y : Bits (configurationWidth tm (n + budget * machinePushBound tm + 1))) :
    execute (rawInputCircuit tm e n budget).reversible (inputMemory x, y) =
      (inputMemory x, fun i => xor (y i) ((rawTrace tm e n budget budget x (Nat.le_refl _)).encode.bitEncode i)) := by
  simpa only [rawInputCircuit_eval] using (rawInputCircuit tm e n budget).clean_correct x y

theorem rawInputCircuit_wires_polynomial (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n : Nat,
      n + preparedSize (initialForest tm e (n + time.eval n * machinePushBound tm + 1) n)
        (tickForest tm (n + time.eval n * machinePushBound tm + 1)) (time.eval n) +
        configurationWidth tm (n + time.eval n * machinePushBound tm + 1) ≤ p.eval n := by
  obtain ⟨q, hq⟩ := clockedConfigurationWidth_polynomial tm time
  obtain ⟨p, hp⟩ := rawInputCircuit_workspace_polynomial tm e time
  refine ⟨Polynomial.X + p + q, ?_⟩
  intro n
  have hs := Nat.add_le_add (Nat.add_le_add_left (hp n) n) (Nat.le_of_eq (hq n))
  simpa only [Polynomial.eval_add, Polynomial.eval_X] using hs

end ShiReversibleTM
