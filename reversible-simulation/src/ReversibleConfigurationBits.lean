import ReversibleMachinePrimitives
import ReversibleFiniteCodec
import ReversibleCore

set_option autoImplicit false

namespace ShiReversibleTM

open ShiReversibleCoding ShiReversible

local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.σ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _

abbrev ConfigurationBit (tm : Turing.FinTM2) (capacity : Nat) :=
  (Option tm.Λ ⊕ tm.σ) ⊕ ((tm.K × Fin capacity) × Option (MachineSymbol tm))

/-- Fixed machine-dependent enumerations, with arithmetic sum/product offsets for stack capacity. -/
noncomputable def configurationBitEquiv (tm : Turing.FinTM2) (capacity : Nat) :
    ConfigurationBit tm capacity ≃ Fin (configurationWidth tm capacity) :=
  (Equiv.sumCongr
    ((Equiv.sumCongr (Fintype.equivFin (Option tm.Λ)) (Fintype.equivFin tm.σ)).trans finSumFinEquiv)
    ((Equiv.prodCongr (stackCellEquiv tm capacity)
      (Fintype.equivFin (Option (MachineSymbol tm)))).trans finProdFinEquiv)).trans finSumFinEquiv

noncomputable def FiniteCfg.indicators {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) : ConfigurationBit tm capacity → Bool
  | .inl (.inl l) => oneHot c.label l
  | .inl (.inr v) => oneHot c.memory v
  | .inr ((k, i), a) => oneHot (c.cells k i) a

noncomputable def FiniteCfg.bitEncode {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) : Bits (configurationWidth tm capacity) :=
  fun i => c.indicators ((configurationBitEquiv tm capacity).symm i)

@[simp] theorem FiniteCfg.bitEncode_read {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) (a : ConfigurationBit tm capacity) :
    c.bitEncode (configurationBitEquiv tm capacity a) = c.indicators a := by
  simp [FiniteCfg.bitEncode]

noncomputable def FiniteCfg.bitParse (tm : Turing.FinTM2) (capacity : Nat)
    (x : Bits (configurationWidth tm capacity)) : FiniteCfg tm capacity where
  label := (oneHotDecode (fun l => x (configurationBitEquiv tm capacity (.inl (.inl l))))).getD none
  memory := (oneHotDecode (fun v => x (configurationBitEquiv tm capacity (.inl (.inr v))))).getD tm.initialState
  cells k i := (oneHotDecode (fun a => x (configurationBitEquiv tm capacity (.inr ((k, i), a))))).getD none

@[simp] theorem FiniteCfg.bitParse_encode {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) : FiniteCfg.bitParse tm capacity c.bitEncode = c := by
  apply FiniteCfg.ext
  · simp [FiniteCfg.bitParse, FiniteCfg.indicators]
  · simp [FiniteCfg.bitParse, FiniteCfg.indicators]
  · funext k i
    simp [FiniteCfg.bitParse, FiniteCfg.indicators]

theorem FiniteCfg.bitEncode_injective {tm : Turing.FinTM2} {capacity : Nat} :
    Function.Injective (FiniteCfg.bitEncode (tm := tm) (capacity := capacity)) := by
  intro c d h
  simpa using congrArg (FiniteCfg.bitParse tm capacity) h

@[simp] theorem BoundedCfg.bitDecode_encode {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) :
    (FiniteCfg.bitParse tm capacity c.encode.bitEncode).decode = c.cfg := by simp

end ShiReversibleTM
