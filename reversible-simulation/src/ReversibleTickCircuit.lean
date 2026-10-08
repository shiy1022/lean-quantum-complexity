import ReversibleTickFormulas

set_option autoImplicit false
namespace ShiReversibleTM
open ShiReversible ShiReversibleFormula

noncomputable def tickForest (tm : Turing.FinTM2) (capacity : Nat) :
    List (Formula (Fin (configurationWidth tm capacity))) :=
  List.ofFn (tickFormulas (FormulaCfg.inputs tm capacity)).bitFormula

@[simp] theorem tickForest_length (tm : Turing.FinTM2) (capacity : Nat) :
    (tickForest tm capacity).length = configurationWidth tm capacity := by simp [tickForest]

theorem tickForest_eval {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (hr : TickRoom capacity c.cfg)
    (i : Fin (tickForest tm capacity).length) :
    ((tickForest tm capacity)[i.val]).eval c.encode.bitEncode =
      (c.tick hr).encode.bitEncode ⟨i.val, by simpa using i.isLt⟩ := by
  have h := tickFormulas_denotes (FormulaCfg.inputs tm capacity) c.encode.bitEncode c.encode
    (FormulaCfg.inputs_denotes c.encode)
  rw [c.finiteTick_encode hr] at h
  simpa [tickForest] using FormulaCfg.bitFormula_eval _ _ _ h ⟨i.val, by simpa using i.isLt⟩

theorem tickForest_size (tm : Turing.FinTM2) (capacity : Nat) :
    ∀ p ∈ tickForest tm capacity, p.size ≤ tickSizeBound tm := by
  have h := tickFormulas_size tm capacity
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  unfold FormulaCfg.bitFormula
  cases (configurationBitEquiv tm capacity).symm i with
  | inl z => cases z with
    | inl l => exact h.2.1 l
    | inr v => exact h.2.2.1 v
  | inr z => exact h.2.2.2 z.1.1 z.1.2 z.2

/-- The actual full machine tick has a clean quantum circuit, including absorbing halting. -/
theorem tickCircuit_quantum_clean_correct {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (hr : TickRoom capacity c.cfg) :
    quantumRun (forestCircuit (tickForest tm capacity)).reversible
      (basis (inputMemory (k := forestSize (tickForest tm capacity)) c.encode.bitEncode,
        fun _ => false)) =
      basis (inputMemory (k := forestSize (tickForest tm capacity)) c.encode.bitEncode,
        fun i => (c.tick hr).encode.bitEncode ⟨i.val, by simpa using i.isLt⟩) := by
  simpa only [tickForest_eval c hr] using forestCircuit_quantum_clean_correct
    (tickForest tm capacity) c.encode.bitEncode

theorem tickCircuit_clean_correct {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (hr : TickRoom capacity c.cfg)
    (y : Bits (tickForest tm capacity).length) :
    execute (forestCircuit (tickForest tm capacity)).reversible
      (inputMemory (k := forestSize (tickForest tm capacity)) c.encode.bitEncode, y) =
      (inputMemory (k := forestSize (tickForest tm capacity)) c.encode.bitEncode,
        fun i => xor (y i) ((c.tick hr).encode.bitEncode ⟨i.val, by simpa using i.isLt⟩)) := by
  simpa only [tickForest_eval c hr] using forestCircuit_clean_correct
    (tickForest tm capacity) c.encode.bitEncode y

theorem tickCircuit_size (tm : Turing.FinTM2) (capacity : Nat) :
    (forestCircuit (tickForest tm capacity)).reversible.length ≤
      4 * configurationWidth tm capacity * tickSizeBound tm + configurationWidth tm capacity := by
  simpa only [tickForest_length] using forestCircuit_size_bound
    (tickForest tm capacity) (tickSizeBound tm) (tickForest_size tm capacity)

theorem tickCircuit_workspace (tm : Turing.FinTM2) (capacity : Nat) :
    forestSize (tickForest tm capacity) ≤ configurationWidth tm capacity * tickSizeBound tm := by
  simpa only [tickForest_length] using forestSize_bound
    (tickForest tm capacity) (tickSizeBound tm) (tickForest_size tm capacity)

end ShiReversibleTM
