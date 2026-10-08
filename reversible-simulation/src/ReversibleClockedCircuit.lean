import ReversibleFiniteRun
import ReversibleIterationCircuit
import ReversibleConfigurationCodec

set_option autoImplicit false
namespace ShiReversibleTM
open ShiReversible ShiReversibleFormula

/-- One concrete formula slice agrees with the next state of the original bounded trace. -/
theorem forestStep_boundedTrace (tm : Turing.FinTM2) (budget t : Nat)
    (xs : List (tm.Γ tm.k₀)) (ht : t < budget) :
    forestStep (tickForest tm (xs.length + budget * machinePushBound tm + 1)) (tickForest_length _ _)
      (boundedTrace tm budget t xs (Nat.le_of_lt ht)).encode.bitEncode =
      (boundedTrace tm budget (t + 1) xs (Nat.succ_le_of_lt ht)).encode.bitEncode := by
  funext i
  have h := tickForest_eval (boundedTrace tm budget t xs (Nat.le_of_lt ht))
    (boundedTrace_tickRoom tm budget t xs ht) ⟨i.val, by simpa using i.isLt⟩
  have hd : (boundedTrace tm budget t xs (Nat.le_of_lt ht)).tick
      (boundedTrace_tickRoom tm budget t xs ht) =
      boundedTrace tm budget (t + 1) xs (Nat.succ_le_of_lt ht) := by
    apply BoundedCfg.ext
    rfl
  rw [hd] at h
  exact h

/-- The actual shared-wire circuit's Boolean iteration equals every time slice of the real trace. -/
theorem forestAdvance_boundedTrace (tm : Turing.FinTM2) (budget t : Nat)
    (xs : List (tm.Γ tm.k₀)) (ht : t ≤ budget) :
    forestAdvance (tickForest tm (xs.length + budget * machinePushBound tm + 1)) (tickForest_length _ _) t
      (boundedTrace tm budget 0 xs (Nat.zero_le budget)).encode.bitEncode =
      (boundedTrace tm budget t xs ht).encode.bitEncode := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hl : t < budget := by omega
    rw [forestAdvance_succ_last, ih (Nat.le_of_lt hl)]
    exact forestStep_boundedTrace tm budget t xs hl

/-- A single clean circuit simulates the whole budgeted run from its encoded initial configuration. -/
theorem clockedCircuit_quantum_clean_correct (tm : Turing.FinTM2) (budget : Nat)
    (xs : List (tm.Γ tm.k₀)) :
    quantumRun (iterationCircuit (tickForest tm (xs.length + budget * machinePushBound tm + 1))
        (tickForest_length _ _) budget).reversible
      (basis (inputMemory (k := budget * forestSize (tickForest tm (xs.length + budget * machinePushBound tm + 1)))
        (boundedTrace tm budget 0 xs (Nat.zero_le budget)).encode.bitEncode, fun _ => false)) =
      basis (inputMemory (k := budget * forestSize (tickForest tm (xs.length + budget * machinePushBound tm + 1)))
        (boundedTrace tm budget 0 xs (Nat.zero_le budget)).encode.bitEncode,
        (boundedTrace tm budget budget xs (Nat.le_refl budget)).encode.bitEncode) := by
  simpa only [forestAdvance_boundedTrace tm budget budget xs (Nat.le_refl budget)] using
    iterationCircuit_quantum_clean_correct
      (tickForest tm (xs.length + budget * machinePushBound tm + 1)) (tickForest_length _ _) budget
      (boundedTrace tm budget 0 xs (Nat.zero_le budget)).encode.bitEncode

/-- Decoding the circuit result gives the original computation certificate's output. -/
theorem polyTime_clockedCircuit_output {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f)
    (xs : List Bool) :
    (FiniteCfg.bitParse M.tm ((xs.map M.inputAlphabet.invFun).length +
      M.time.eval xs.length * machinePushBound M.tm + 1)
      ((iterationCircuit (tickForest M.tm ((xs.map M.inputAlphabet.invFun).length +
        M.time.eval xs.length * machinePushBound M.tm + 1)) (tickForest_length _ _) (M.time.eval xs.length)).eval
        (boundedTrace M.tm (M.time.eval xs.length) 0 (xs.map M.inputAlphabet.invFun) (Nat.zero_le _)).encode.bitEncode)).decode =
      Turing.haltList M.tm ((f xs).map M.outputAlphabet.invFun) := by
  rw [iterationCircuit_eval, forestAdvance_boundedTrace _ _ _ _ (Nat.le_refl _),
    FiniteCfg.bitParse_encode, BoundedCfg.decode_encode]
  exact polyTime_padded_run M xs

/-- Polynomial gate count for the whole clocked run; constants depend only on the fixed machine. -/
theorem clockedCircuit_size_polynomial (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n : Nat,
      (iterationCircuit (tickForest tm (n + time.eval n * machinePushBound tm + 1))
        (tickForest_length _ _) (time.eval n)).reversible.length ≤ p.eval n := by
  obtain ⟨q, hq⟩ := clockedConfigurationWidth_polynomial tm time
  refine ⟨Polynomial.C (4 * tickSizeBound tm) * time * q + q, ?_⟩
  intro n
  have hs := iterationCircuit_size (tickForest tm (n + time.eval n * machinePushBound tm + 1))
    (tickForest_length _ _) (time.eval n) (tickSizeBound tm) (tickForest_size _ _)
  calc
    _ ≤ 4 * time.eval n * configurationWidth tm (n + time.eval n * machinePushBound tm + 1) *
      tickSizeBound tm + configurationWidth tm (n + time.eval n * machinePushBound tm + 1) := hs
    _ = (Polynomial.C (4 * tickSizeBound tm) * time * q + q).eval n := by
      rw [hq]
      simp
      ring

/-- Polynomial workspace for the addressed unrolling, including a zero-step clock. -/
theorem clockedCircuit_workspace_polynomial (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n : Nat,
      time.eval n * forestSize (tickForest tm (n + time.eval n * machinePushBound tm + 1)) ≤ p.eval n := by
  obtain ⟨q, hq⟩ := clockedConfigurationWidth_polynomial tm time
  refine ⟨Polynomial.C (tickSizeBound tm) * time * q, ?_⟩
  intro n
  have hs := Nat.mul_le_mul_left (time.eval n) (tickCircuit_workspace tm
    (n + time.eval n * machinePushBound tm + 1))
  calc
    _ ≤ time.eval n * (configurationWidth tm (n + time.eval n * machinePushBound tm + 1) * tickSizeBound tm) := hs
    _ = (Polynomial.C (tickSizeBound tm) * time * q).eval n := by
      rw [hq]
      simp
      ring

/-- Both configuration registers and all temporary qubits fit a polynomial wire budget. -/
theorem clockedCircuit_wires_polynomial (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n : Nat,
      2 * configurationWidth tm (n + time.eval n * machinePushBound tm + 1) +
        time.eval n * forestSize (tickForest tm (n + time.eval n * machinePushBound tm + 1)) ≤ p.eval n := by
  obtain ⟨q, hq⟩ := clockedConfigurationWidth_polynomial tm time
  obtain ⟨p, hp⟩ := clockedCircuit_workspace_polynomial tm time
  refine ⟨Polynomial.C 2 * q + p, ?_⟩
  intro n
  apply (Nat.add_le_add_left (hp n)
    (2 * configurationWidth tm (n + time.eval n * machinePushBound tm + 1))).trans
  rw [hq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  exact le_rfl

end ShiReversibleTM
