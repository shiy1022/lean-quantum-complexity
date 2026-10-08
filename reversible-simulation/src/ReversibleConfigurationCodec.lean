import ReversibleMachineEncoding
import ReversibleFixedBlocks

set_option autoImplicit false

namespace ShiReversibleTM

open ShiReversibleCoding

local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.σ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) :=
  Classical.decEq _

/-- Total parsing by fixed block offsets and finite alphabet searches. -/
noncomputable def FiniteCfg.parse (tm : Turing.FinTM2) (capacity : Nat)
    (bits : List Bool) : FiniteCfg tm capacity := by
  classical
  exact {
    label := (oneHotListDecode (α := Option tm.Λ)
      (bits.take (Fintype.card (Option tm.Λ)))).getD none
    memory := (oneHotListDecode (α := tm.σ)
      ((bits.drop (Fintype.card (Option tm.Λ))).take (Fintype.card tm.σ))).getD tm.initialState
    cells := fun k i => (oneHotListDecode (α := Option (MachineSymbol tm))
      (((bits.drop (Fintype.card (Option tm.Λ) + Fintype.card tm.σ)).drop
        (((stackCellEquiv tm capacity) (k, i)).val *
          Fintype.card (Option (MachineSymbol tm)))).take
            (Fintype.card (Option (MachineSymbol tm))))).getD none }

theorem FiniteCfg.serialize_label {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) :
    c.serialize.take (Fintype.card (Option tm.Λ)) = oneHotList c.label := by
  classical
  unfold FiniteCfg.serialize
  rw [List.append_assoc]
  exact List.take_left' (oneHotList_length c.label)

theorem FiniteCfg.serialize_memory {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) :
    (c.serialize.drop (Fintype.card (Option tm.Λ))).take (Fintype.card tm.σ) =
      oneHotList c.memory := by
  classical
  unfold FiniteCfg.serialize
  rw [List.append_assoc, ← oneHotList_length c.label, List.drop_append_length]
  exact List.take_left' (oneHotList_length c.memory)

theorem FiniteCfg.serialize_cells {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) :
    c.serialize.drop (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) =
      c.cellList.flatMap oneHotList := by
  classical
  have h : (oneHotList c.label ++ oneHotList c.memory).length =
      Fintype.card (Option tm.Λ) + Fintype.card tm.σ := by simp
  unfold FiniteCfg.serialize
  rw [← h, List.drop_append_length]

@[simp] theorem FiniteCfg.parse_serialize {tm : Turing.FinTM2} {capacity : Nat}
    (c : FiniteCfg tm capacity) : FiniteCfg.parse tm capacity c.serialize = c := by
  classical
  apply FiniteCfg.ext
  · simp only [FiniteCfg.parse, FiniteCfg.serialize_label, oneHotListDecode_encode,
      Option.getD_some]
  · simp only [FiniteCfg.parse, FiniteCfg.serialize_memory, oneHotListDecode_encode,
      Option.getD_some]
  · funext k i
    simp only [FiniteCfg.parse, FiniteCfg.serialize_cells, FiniteCfg.cellList]
    rw [oneHotBlock_decode]
    simp only [Equiv.symm_apply_apply, Option.getD_some]

theorem FiniteCfg.serialize_injective {tm : Turing.FinTM2} {capacity : Nat} :
    Function.Injective (FiniteCfg.serialize (tm := tm) (capacity := capacity)) := by
  intro c d h
  simpa using congrArg (FiniteCfg.parse tm capacity) h

noncomputable def BoundedCfg.serialize {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) : List Bool := c.encode.serialize

noncomputable def decodeConfiguration (tm : Turing.FinTM2) (capacity : Nat)
    (bits : List Bool) : tm.Cfg := (FiniteCfg.parse tm capacity bits).decode

@[simp] theorem BoundedCfg.decode_serialize {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) : decodeConfiguration tm capacity c.serialize = c.cfg := by
  simp [decodeConfiguration, BoundedCfg.serialize]

theorem BoundedCfg.serialize_length {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) : c.serialize.length = configurationWidth tm capacity :=
  FiniteCfg.serialize_length c.encode

theorem BoundedCfg.serialize_injective {tm : Turing.FinTM2} {capacity : Nat} :
    Function.Injective (BoundedCfg.serialize (tm := tm) (capacity := capacity)) := by
  intro c d h
  apply BoundedCfg.encode_injective
  exact FiniteCfg.serialize_injective h

/-- The real run's configuration codes have a polynomial width, including at input length zero. -/
theorem clockedConfigurationWidth_polynomial (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ q : Polynomial Nat, ∀ n : Nat,
      configurationWidth tm (n + time.eval n * machinePushBound tm + 1) = q.eval n := by
  rcases configurationWidth_affine tm with ⟨a, b, hab⟩
  refine ⟨Polynomial.C a * (Polynomial.X + time * Polynomial.C (machinePushBound tm) +
    Polynomial.C 1) + Polynomial.C b, ?_⟩
  intro n
  rw [hab]
  simp

end ShiReversibleTM
