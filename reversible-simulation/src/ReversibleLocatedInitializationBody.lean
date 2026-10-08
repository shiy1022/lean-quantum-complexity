import ReversibleInitializationCoordinatePreparation
import ReversibleInitializationLoopControl

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding

abbrev LocatedInitializationLabels (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (a : Option (MachineSymbol tm))
    (backward : Bool) (L : Type) :=
  CellCoordinateLabels header stackRank symbolCard symbolRank
    (InitializationInputBodyLabels tm e a backward L)

noncomputable def locatedInitializationExit {L : Type} (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (a : Option (MachineSymbol tm))
    (backward : Bool) (l : L) : LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward L :=
  cleanupExit [(Sum.inr 1 : InitializationRegister)] (operationExit (cellCoordinateOperations header stackRank symbolCard symbolRank)
    (initializationBodyExit tm e a backward l))

noncomputable def locatedInitializationEntry {L : Type} (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (a : Option (MachineSymbol tm))
    (backward : Bool) : LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward L :=
  cleanupEntry [(Sum.inr 1 : InitializationRegister)] (operationEntry (cellCoordinateOperations header stackRank symbolCard symbolRank)
    (initializationBodyEntry tm e a backward))

noncomputable def locatedInitializationCode {L : Type} (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (a : Option (MachineSymbol tm))
    (backward : Bool) (caller : L → CounterInstr InitializationRegister L) (stop : L) :
    LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward L →
      CounterInstr InitializationRegister (LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward L) :=
  cellCoordinateCode header stackRank symbolCard symbolRank
    (initializationInputBodyCode tm e a backward caller stop) (initializationBodyEntry tm e a backward)

noncomputable def locatedInitializationCounters (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (a : Option (MachineSymbol tm))
    (backward : Bool) (cs : InitializationRegister → Nat) :=
  initializationInputBodyCounters tm e a backward (cellCoordinateResult header stackRank symbolCard symbolRank cs)

noncomputable def locatedInitializationSteps (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (a : Option (MachineSymbol tm))
    (backward : Bool) (cs : InitializationRegister → Nat) :=
  (cleanupSteps [(Sum.inr 1 : InitializationRegister)] cs + operationSteps (cellCoordinateOperations header stackRank symbolCard symbolRank)
    (cleanupCounters [(Sum.inr 1 : InitializationRegister)] cs)) +
      initializationInputBodySteps tm e a backward (cellCoordinateResult header stackRank symbolCard symbolRank cs)

theorem locatedInitialization_run {L : Type} (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (capacity n : Nat) (i : Fin capacity)
    (a : Option (MachineSymbol tm)) (backward : Bool)
    (caller : L → CounterInstr InitializationRegister L) (stop : L) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hi : cs (.inr 0) = i.val)
    (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (locatedInitializationCode header stackRank symbolCard symbolRank tm e a backward caller stop)
      ⟨some (locatedInitializationEntry header stackRank symbolCard symbolRank tm e a backward), cs, ys⟩
      (locatedInitializationSteps header stackRank symbolCard symbolRank tm e a backward cs)
      ⟨some (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward stop),
        locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs,
        initializationCellPayload tm e capacity n i a backward
          (n + 18 * (header + (stackRank * cs (.inl 2) + i.val) * symbolCard + symbolRank)) ++ ys⟩ := by
  let inner := initializationInputBodyCode tm e a backward caller stop
  let code := locatedInitializationCode header stackRank symbolCard symbolRank tm e a backward caller stop
  let ops := cellCoordinateOperations header stackRank symbolCard symbolRank
  let prepared := cellCoordinateResult header stackRank symbolCard symbolRank cs
  have hc := cellCoordinate_run header stackRank symbolCard symbolRank inner
    (initializationBodyEntry tm e a backward) cs hb ht ys
  have hp := initializationInputBody_run tm e capacity n i a backward caller stop prepared
    (by simpa [prepared, cellCoordinateResult_eq] using hn)
    (by simpa [prepared, cellCoordinateResult_eq] using hi)
    (by simpa [prepared, cellCoordinateResult_eq] using hb)
    (by simpa [prepared, cellCoordinateResult_eq] using ht) ys
  dsimp only at hp
  have hp' := CounterRun.relabel inner code (fun l => cleanupExit [(Sum.inr 1 : InitializationRegister)] (operationExit ops l))
    (by
      intro l
      simp only [code, locatedInitializationCode, cellCoordinateCode, ops, inner, cleanupCode_embed, operationCode_embed]
      exact CounterInstr.relabel_comp (operationExit ops) (cleanupExit [(Sum.inr 1 : InitializationRegister)]) (inner l)) hp
  dsimp only [CounterCfg.relabel, Option.map] at hp'
  simpa [locatedInitializationSteps, locatedInitializationCounters, locatedInitializationEntry,
    locatedInitializationExit, prepared, cellCoordinateResult_eq, hi, initializationBodyEntry,
    initializationBodyExit, code, ops] using CounterRun.trans code hc hp'

theorem locatedInitialization_preserves_metadata (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (a : Option (MachineSymbol tm))
    (backward : Bool) (cs : InitializationRegister → Nat) (r : WorkspaceRegister) :
    locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs (.inl r) = cs (.inl r) := by
  rw [locatedInitializationCounters, initializationInputBody_preserves_metadata, cellCoordinateResult_eq]
  simp

theorem locatedInitialization_preserves_index (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (a : Option (MachineSymbol tm))
    (backward : Bool) (cs : InitializationRegister → Nat) :
    locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs (.inr 0) = cs (.inr 0) := by
  rw [locatedInitializationCounters, initializationInputBody_preserves_index, cellCoordinateResult_eq]
  simp

end ShiReversibleGenerator
