import ReversibleInitializationAddresses
import ReversibleConfigurationCoordinates

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding

/-- Fixed ranks are literals in the control graph; capacity and index are counters. -/
def cellCoordinateOperations (header stackRank symbolCard symbolRank : Nat) :
    List (GeneratorOperation InitializationRegister) :=
  [.affine ⟨.inl 2, .inr 1, header + symbolRank, stackRank * symbolCard⟩,
    .affine ⟨.inr 0, .inr 1, 0, symbolCard⟩]

def cellCoordinateResult (header stackRank symbolCard symbolRank : Nat)
    (cs : InitializationRegister → Nat) :=
  operationResult (cellCoordinateOperations header stackRank symbolCard symbolRank)
    (cleanupCounters [(Sum.inr 1 : InitializationRegister)] cs)

theorem cellCoordinateOperations_valid (header stackRank symbolCard symbolRank : Nat) :
    ∀ op ∈ cellCoordinateOperations header stackRank symbolCard symbolRank,
      op.Valid (.inl 6) (.inl 5) := by
  simp [cellCoordinateOperations, GeneratorOperation.Valid, AffineAtom.Valid]

theorem cellCoordinateResult_eq (header stackRank symbolCard symbolRank : Nat)
    (cs : InitializationRegister → Nat) :
    cellCoordinateResult header stackRank symbolCard symbolRank cs =
      Function.update cs (.inr 1)
        (header + (stackRank * cs (.inl 2) + cs (.inr 0)) * symbolCard + symbolRank) := by
  funext r
  by_cases h : r = (.inr 1 : InitializationRegister)
  · subst r
    simp [cellCoordinateResult, cellCoordinateOperations, operationResult,
      GeneratorOperation.apply, AffineAtom.apply, cleanupCounters]
    ring
  · simp [cellCoordinateResult, cellCoordinateOperations, operationResult,
      GeneratorOperation.apply, AffineAtom.apply, cleanupCounters, h]

abbrev CellCoordinateLabels (header stackRank symbolCard symbolRank : Nat) (L : Type) :=
  CleanupLabels [(Sum.inr 1 : InitializationRegister)]
    (GeneratorOperationLabels (cellCoordinateOperations header stackRank symbolCard symbolRank) L)

def cellCoordinateCode {L : Type} (header stackRank symbolCard symbolRank : Nat)
    (caller : L → CounterInstr InitializationRegister L) (stop : L) :
    CellCoordinateLabels header stackRank symbolCard symbolRank L →
      CounterInstr InitializationRegister (CellCoordinateLabels header stackRank symbolCard symbolRank L) :=
  cleanupCode [(Sum.inr 1 : InitializationRegister)]
    (operationCode (cellCoordinateOperations header stackRank symbolCard symbolRank) caller (.inl 6) (.inl 5) stop)
    (operationEntry (cellCoordinateOperations header stackRank symbolCard symbolRank) stop)

theorem cellCoordinate_run {L : Type} (header stackRank symbolCard symbolRank : Nat)
    (caller : L → CounterInstr InitializationRegister L) (stop : L)
    (cs : InitializationRegister → Nat) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (ys : List Bool) :
    let ops := cellCoordinateOperations header stackRank symbolCard symbolRank
    CounterRun (cellCoordinateCode header stackRank symbolCard symbolRank caller stop)
      ⟨some (cleanupEntry [(Sum.inr 1 : InitializationRegister)] (operationEntry ops stop)), cs, ys⟩
      (cleanupSteps [(Sum.inr 1 : InitializationRegister)] cs + operationSteps ops (cleanupCounters [(Sum.inr 1 : InitializationRegister)] cs))
      ⟨some (cleanupExit [(Sum.inr 1 : InitializationRegister)] (operationExit ops stop)),
        cellCoordinateResult header stackRank symbolCard symbolRank cs, ys⟩ := by
  let ops := cellCoordinateOperations header stackRank symbolCard symbolRank
  let inner := operationCode ops caller (.inl 6) (.inl 5) stop
  let code := cellCoordinateCode header stackRank symbolCard symbolRank caller stop
  have hc := cleanupCode_run [(Sum.inr 1 : InitializationRegister)] inner (operationEntry ops stop) cs ys
  have hp := operationCode_run ops caller (.inl 6) (.inl 5) stop
    (cellCoordinateOperations_valid header stackRank symbolCard symbolRank) (by decide)
    (cleanupCounters [(Sum.inr 1 : InitializationRegister)] cs)
    (by simpa [cleanupCounters] using hb) (by simpa [cleanupCounters] using ht) ys
  have hp' := CounterRun.relabel inner code (cleanupExit [(Sum.inr 1 : InitializationRegister)])
    (cleanupCode_embed [(Sum.inr 1 : InitializationRegister)] inner (operationEntry ops stop)) hp
  exact CounterRun.trans code hc hp'

local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

/-- Specializing the fixed literals gives the exact established configuration address. -/
theorem cellCoordinateResult_machine (tm : Turing.FinTM2) (capacity : Nat) (k : tm.K)
    (i : Fin capacity) (a : Option (MachineSymbol tm)) (cs : InitializationRegister → Nat)
    (hc : cs (.inl 2) = capacity) (hi : cs (.inr 0) = i.val) :
    cellCoordinateResult (Fintype.card (Option tm.Λ) + Fintype.card tm.σ)
      ((Fintype.equivFin tm.K) k).val (Fintype.card (Option (MachineSymbol tm)))
      ((Fintype.equivFin (Option (MachineSymbol tm))) a).val cs (.inr 1) =
        (configurationBitEquiv tm capacity (.inr ((k, i), a))).val := by
  classical
  rw [cellCoordinateResult_eq, Function.update_self, hc, hi, configurationBitEquiv_cell_val]

end ShiReversibleGenerator
