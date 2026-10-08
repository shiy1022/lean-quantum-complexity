import ReversibleLocatedInitializationBody

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
variable (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool)

abbrev LocatedCellLoopLabels :=
  LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward (Fin 3)

noncomputable instance locatedCellLoopFintype :
    Fintype (LocatedCellLoopLabels header stackRank symbolCard symbolRank tm e a backward) := inferInstance

theorem locatedInitializationExit_injective {L : Type} :
    Function.Injective (locatedInitializationExit (L := L) header stackRank symbolCard symbolRank tm e a backward) := by
  intro l k h
  exact initializationBodyExit_injective tm e a backward
    (operationExit_injective _ (cleanupExit_injective _ h))

theorem locatedInitializationExit_halt {L : Type} (stop l : L) :
    locatedInitializationCode header stackRank symbolCard symbolRank tm e a backward
      (fun _ => .halt) stop (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward l) = .halt := by
  simp only [locatedInitializationCode, cellCoordinateCode, locatedInitializationExit,
    cleanupCode_embed, operationCode_embed, initializationBodyExit_halt, CounterInstr.relabel]

noncomputable def locatedCellLoopCode :
    LocatedCellLoopLabels header stackRank symbolCard symbolRank tm e a backward →
      CounterInstr InitializationRegister (LocatedCellLoopLabels header stackRank symbolCard symbolRank tm e a backward) := by
  classical
  exact reentryCode (locatedInitializationCode header stackRank symbolCard symbolRank tm e a backward (fun _ => .halt) 0)
    (.inr 0) (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0)
    (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 1)
    (locatedInitializationEntry header stackRank symbolCard symbolRank tm e a backward)
    (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 2)

theorem locatedCellLoop_test :
    locatedCellLoopCode header stackRank symbolCard symbolRank tm e a backward
      (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0) =
    .branch (.inr 0) (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 2)
      (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 1) := by
  classical
  exact reentryCode_loop _ _ _ _ _ _

theorem locatedCellLoop_pop :
    locatedCellLoopCode header stackRank symbolCard symbolRank tm e a backward
      (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 1) =
    .dec (.inr 0) (locatedInitializationEntry header stackRank symbolCard symbolRank tm e a backward) := by
  classical
  apply reentryCode_pop
  intro h
  exact (by decide : (1 : Fin 3) ≠ 0)
    (locatedInitializationExit_injective header stackRank symbolCard symbolRank tm e a backward h)

theorem locatedCellLoop_body (capacity n : Nat) (i : Fin capacity)
    (cs : InitializationRegister → Nat) (hn : cs (.inl 0) = n) (hi : cs (.inr 0) = i.val)
    (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (locatedCellLoopCode header stackRank symbolCard symbolRank tm e a backward)
      ⟨some (locatedInitializationEntry header stackRank symbolCard symbolRank tm e a backward), cs, ys⟩
      (locatedInitializationSteps header stackRank symbolCard symbolRank tm e a backward cs)
      ⟨some (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward (0 : Fin 3)),
        locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs,
        initializationCellPayload tm e capacity n i a backward
          (n + 18 * (header + (stackRank * cs (.inl 2) + i.val) * symbolCard + symbolRank)) ++ ys⟩ := by
  classical
  have h := locatedInitialization_run header stackRank symbolCard symbolRank tm e capacity n i a backward
    (fun (_ : Fin 3) => .halt) 0 cs hn hi hb ht ys
  exact reentryCode_preserves_run _ _ _ _ _ _
    (locatedInitializationExit_halt header stackRank symbolCard symbolRank tm e a backward 0 0)
    (locatedInitializationExit_halt header stackRank symbolCard symbolRank tm e a backward 0 1) h (by simp)

end ShiReversibleGenerator
