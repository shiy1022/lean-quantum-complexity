import ReversibleTickCircuit
import ReversibleMachineExecution

set_option autoImplicit false
namespace ShiReversibleTM

/-- Fixed-width iteration; the encoding capacity is unchanged across all clocked steps. -/
noncomputable def finiteAdvance {tm : Turing.FinTM2} {capacity : Nat} :
    Nat → FiniteCfg tm capacity → FiniteCfg tm capacity
  | 0, c => c
  | t + 1, c => finiteTick (finiteAdvance t c)

theorem boundedTrace_tickRoom (tm : Turing.FinTM2) (budget t : Nat)
    (xs : List (tm.Γ tm.k₀)) (ht : t < budget) :
    TickRoom (xs.length + budget * machinePushBound tm + 1)
      (boundedTrace tm budget t xs (Nat.le_of_lt ht)).cfg := by
  intro k
  have hs := initial_trace_stack_length tm t xs k
  have hm := Nat.mul_le_mul_right (machinePushBound tm) (Nat.succ_le_of_lt ht)
  rw [Nat.succ_mul] at hm
  change ((advance tm t (Turing.initList tm xs)).stk k).length + machinePushBound tm ≤ _
  omega

theorem finiteTick_boundedTrace (tm : Turing.FinTM2) (budget t : Nat)
    (xs : List (tm.Γ tm.k₀)) (ht : t < budget) :
    finiteTick (boundedTrace tm budget t xs (Nat.le_of_lt ht)).encode =
      (boundedTrace tm budget (t + 1) xs (Nat.succ_le_of_lt ht)).encode := by
  rw [BoundedCfg.finiteTick_encode _ (boundedTrace_tickRoom tm budget t xs ht)]
  congr 1

/-- Every clocked finite-buffer execution equals the untruncated original trace, not just its last state. -/
theorem finiteAdvance_trace (tm : Turing.FinTM2) (budget t : Nat)
    (xs : List (tm.Γ tm.k₀)) (ht : t ≤ budget) :
    finiteAdvance t (boundedTrace tm budget 0 xs (Nat.zero_le budget)).encode =
      (boundedTrace tm budget t xs ht).encode := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hl : t < budget := by omega
    change finiteTick (finiteAdvance t _) = _
    rw [ih (Nat.le_of_lt hl)]
    exact finiteTick_boundedTrace tm budget t xs hl

theorem finiteAdvance_decode (tm : Turing.FinTM2) (budget : Nat) (xs : List (tm.Γ tm.k₀)) :
    (finiteAdvance budget (boundedTrace tm budget 0 xs (Nat.zero_le budget)).encode).decode =
      advance tm budget (Turing.initList tm xs) := by
  rw [finiteAdvance_trace tm budget budget xs (Nat.le_refl budget), BoundedCfg.decode_encode]
  rfl

/-- The bounded run recovers the original polynomial-time certificate's actual output. -/
theorem polyTime_finite_run {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) f) (xs : List Bool) :
    (finiteAdvance (M.time.eval xs.length)
      (boundedTrace M.tm (M.time.eval xs.length) 0 (xs.map M.inputAlphabet.invFun)
        (Nat.zero_le _)).encode).decode =
      Turing.haltList M.tm ((f xs).map M.outputAlphabet.invFun) := by
  rw [finiteAdvance_decode, polyTime_padded_run]

end ShiReversibleTM
