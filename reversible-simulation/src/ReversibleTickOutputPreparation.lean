import ReversibleProgramTemplateReentry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

noncomputable def tickOutputAddressParameters (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (bound : Nat) : Nat × Nat × Nat :=
  match kind with
  | .inl (.inl l) => (((Fintype.equivFin (Option tm.Λ)) l).val * (bound + 1), 0, 0)
  | .inl (.inr v) => ((Fintype.card (Option tm.Λ) + ((Fintype.equivFin tm.σ) v).val) * (bound + 1), 0, 0)
  | .inr (k, a) => ((Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
      ((Fintype.equivFin (Option (MachineSymbol tm))) a).val) * (bound + 1),
      ((Fintype.equivFin tm.K) k).val, Fintype.card (Option (MachineSymbol tm)) * (bound + 1))

noncomputable def tickPreparedOutputAddress (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) : Nat :=
  let v := tickOutputAddressParameters tm kind bound
  symbolicCellAddress .position (tickTraversalSpare tm 2) (.inl 1) (.inl 2) v.1 v.2.1 v.2.2 cs

noncomputable def TickOutputPreparationLabels (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (bound : Nat) (L : Type) : Type :=
  let v := tickOutputAddressParameters tm kind bound
  SymbolicCellBindingLabels .position (tickTraversalSpare tm 2) (.inl 1) (.inl 3) (.inl 12)
    v.1 v.2.1 v.2.2 (AddressBindingLabels bound 1 0 L)

noncomputable def tickOutputPreparationEntry (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (bound : Nat) (L : Type) : TickOutputPreparationLabels tm kind bound L := .inl 0

noncomputable def tickOutputPreparationExit {L : Type} (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (bound : Nat) (l : L) : TickOutputPreparationLabels tm kind bound L :=
  let v := tickOutputAddressParameters tm kind bound
  symbolicCellBindingExit .position (tickTraversalSpare tm 2) (.inl 1) (.inl 3) (.inl 12)
    v.1 v.2.1 v.2.2 (.inr (.inr (.inr (.inr l))))

noncomputable def tickOutputPreparationCode {L : Type} (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (bound : Nat) (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop : L) :
    TickOutputPreparationLabels tm kind bound L →
      CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) (TickOutputPreparationLabels tm kind bound L) :=
  let v := tickOutputAddressParameters tm kind bound
  symbolicCellBindingCode .position
    (addressBindingCode caller (.inl 12) (.inl 13) (.inl 5) bound 1 0 stop)
    (tickTraversalSpare tm 2) (.inl 1) (.inl 2) (.inl 3) (.inl 12) (.inl 5) v.1 v.2.1 v.2.2 (.inl 0)

noncomputable def tickOutputPreparationCounters (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) : FixedLeafRegister (tickTraversalSupply tm) → Nat :=
  Function.update (Function.update cs (.inl 12) (tickPreparedOutputAddress tm kind bound cs))
    (.inl 13) (tickPreparedOutputAddress tm kind bound cs + bound)

noncomputable def tickOutputPreparationSteps (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) : Nat :=
  let v := tickOutputAddressParameters tm kind bound
  symbolicCellBindingSteps .position (tickTraversalSpare tm 2) (.inl 1) (.inl 2) (.inl 3) (.inl 12)
    v.1 v.2.1 v.2.2 cs +
    ((2 * cs (.inl 13) + 1) + (7 * tickPreparedOutputAddress tm kind bound cs + 2 + bound))

noncomputable instance tickOutputPreparationFintype (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (bound : Nat) (L : Type) [Fintype L] : Fintype (TickOutputPreparationLabels tm kind bound L) := by
  unfold TickOutputPreparationLabels
  infer_instance

theorem tickOutputPreparationCode_embed {L : Type} (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat)
    (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop l : L) :
    tickOutputPreparationCode tm kind bound caller stop (tickOutputPreparationExit tm kind bound l) =
      (caller l).relabel (tickOutputPreparationExit tm kind bound) := by
  unfold tickOutputPreparationCode tickOutputPreparationExit
  rw [symbolicCellBindingCode_embed, addressBindingCode_embed]
  cases caller l <;> rfl

theorem tickOutputPreparationCode_run {L : Type} (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat)
    (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop : L)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hq : cs (.inl 3) = 0) (hx : cs (.inl 5) = 0)
    (ys : List Bool) :
    CounterRun (tickOutputPreparationCode tm kind bound caller stop)
      ⟨some (tickOutputPreparationEntry tm kind bound L), cs, ys⟩ (tickOutputPreparationSteps tm kind bound cs)
      ⟨some (tickOutputPreparationExit tm kind bound stop), tickOutputPreparationCounters tm kind bound cs, ys⟩ := by
  let v := tickOutputAddressParameters tm kind bound
  let after := Function.update cs (.inl 12 : FixedLeafRegister (tickTraversalSupply tm))
    (tickPreparedOutputAddress tm kind bound cs)
  let inner := addressBindingCode caller (.inl 12) (.inl 13) (.inl 5) bound 1 0 stop
  let code := tickOutputPreparationCode tm kind bound caller stop
  have h₁ := symbolicCellBindingCode_run .position inner (tickTraversalSpare tm 2)
    (.inl 1) (.inl 2) (.inl 3) (.inl 12) (.inl 5) v.1 v.2.1 v.2.2 (.inl 0)
    (by simp) (by simp) (by simp [tickTraversalSpare]) (by simp) (by simp)
    (by simp [tickTraversalSpare]) (by simp) (by simp) (by simp [tickTraversalSpare])
    (by simp) (by simp) cs hq hx ys
  have h₂ := addressBindingCode_run caller (.inl 12) (.inl 13) (.inl 5) bound 1 0 stop
    (by simp) (by simp) (by simp) after (by simp [after, hx]) ys
  have h₂' := CounterRun.relabel inner code
    (symbolicCellBindingExit .position (tickTraversalSpare tm 2) (.inl 1) (.inl 3) (.inl 12) v.1 v.2.1 v.2.2)
    (fun l => symbolicCellBindingCode_embed _ _ _ _ _ _ _ _ _ _ _ _ _) h₂
  have h := CounterRun.trans code h₁ h₂'
  simpa [code, inner, after, v, tickOutputPreparationEntry, tickOutputPreparationExit,
    tickOutputPreparationCounters, tickOutputPreparationSteps, tickPreparedOutputAddress,
    CounterCfg.relabel] using h

end ShiReversibleGenerator
