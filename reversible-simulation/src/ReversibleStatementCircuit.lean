import ReversibleStatementBridge
import ReversibleForestCircuit

set_option autoImplicit false
namespace ShiReversibleTM
open ShiReversible ShiReversibleFormula ShiReversibleCoding

local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _

noncomputable def FormulaCfg.bitFormula {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (i : Fin (configurationWidth tm capacity)) : Formula ι :=
  match (configurationBitEquiv tm capacity).symm i with
  | .inl (.inl l) => p.label l
  | .inl (.inr v) => p.memory v
  | .inr ((k, j), a) => p.cells k j a

theorem FormulaCfg.bitFormula_eval {tm : Turing.FinTM2} {capacity : Nat} {ι : Type}
    (p : FormulaCfg tm capacity ι) (x : ι → Bool) (c : FiniteCfg tm capacity)
    (h : p.Denotes x c) (i : Fin (configurationWidth tm capacity)) :
    (p.bitFormula i).eval x = c.bitEncode i := by
  unfold FormulaCfg.bitFormula FiniteCfg.bitEncode
  cases (configurationBitEquiv tm capacity).symm i with
  | inl z => cases z with
    | inl l => exact h.1 l
    | inr v => exact h.2.1 v
  | inr z => exact h.2.2 z.1.1 z.1.2 z.2

noncomputable def statementForest {tm : Turing.FinTM2} (capacity : Nat)
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : pushSymbols q ⊆ machineSymbols tm) :
    List (Formula (Fin (configurationWidth tm capacity))) :=
  List.ofFn (statementFormulas q hq (FormulaCfg.inputs tm capacity)).bitFormula

@[simp] theorem statementForest_length {tm : Turing.FinTM2} (capacity : Nat)
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : pushSymbols q ⊆ machineSymbols tm) :
    (statementForest capacity q hq).length = configurationWidth tm capacity := by
  simp [statementForest]

/-- Every output bit of the concrete formula forest is the actual TM2 statement result. -/
theorem statementForest_eval {tm : Turing.FinTM2} {capacity : Nat}
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : pushSymbols q ⊆ machineSymbols tm)
    (c : BoundedCfg tm capacity) (hr : StackRoom capacity q c.cfg.stk)
    (i : Fin (statementForest capacity q hq).length) :
    ((statementForest capacity q hq)[i.val]).eval c.encode.bitEncode =
      (c.execute q hq hr).encode.bitEncode ⟨i.val, by simpa using i.isLt⟩ := by
  have h := statementFormulas_denotes q hq (FormulaCfg.inputs tm capacity)
    c.encode.bitEncode c.encode (FormulaCfg.inputs_denotes c.encode)
  rw [c.finiteStatement_encode q hq hr] at h
  simpa [statementForest] using FormulaCfg.bitFormula_eval _ _ _ h
    ⟨i.val, by simpa using i.isLt⟩

/-- Concrete clean quantum simulation of a whole actual TM2 statement, in reversible basis semantics. -/
theorem statementCircuit_quantum_clean_correct {tm : Turing.FinTM2} {capacity : Nat}
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : pushSymbols q ⊆ machineSymbols tm)
    (c : BoundedCfg tm capacity) (hr : StackRoom capacity q c.cfg.stk) :
    quantumRun (forestCircuit (statementForest capacity q hq)).reversible
      (basis (inputMemory (k := forestSize (statementForest capacity q hq)) c.encode.bitEncode,
        fun _ => false)) =
      basis (inputMemory (k := forestSize (statementForest capacity q hq)) c.encode.bitEncode,
        fun i => (c.execute q hq hr).encode.bitEncode ⟨i.val, by simpa using i.isLt⟩) := by
  simpa only [statementForest_eval q hq c hr] using
    forestCircuit_quantum_clean_correct (statementForest capacity q hq) c.encode.bitEncode

end ShiReversibleTM
