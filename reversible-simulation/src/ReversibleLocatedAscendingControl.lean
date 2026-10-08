import ReversibleLocatedBodyBounds
import ReversibleLocatedInitializationLoop

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
variable (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool)

/-- A separate remaining counter permits ascending cell visits in one fixed finite graph. -/
noncomputable def locatedAscendingCode : (LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward (Fin 4)) → CounterInstr InitializationRegister (LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward (Fin 4)) := by
  classical
  exact fun q => if q = locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0 then .branch (.inr 11) (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 3) (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 1)
    else if q = locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 1 then .dec (.inr 11) (locatedInitializationEntry header stackRank symbolCard symbolRank tm e a backward)
    else if q = locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 2 then .inc (.inr 0) (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0)
    else locatedInitializationCode header stackRank symbolCard symbolRank tm e a backward (fun (_ : Fin 4) => .halt) 2 q

theorem locatedAscending_test :
    locatedAscendingCode header stackRank symbolCard symbolRank tm e a backward (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0) = .branch (.inr 11) (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 3) (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 1) := by
  classical
  simp [locatedAscendingCode]

theorem locatedAscending_pop :
    locatedAscendingCode header stackRank symbolCard symbolRank tm e a backward (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 1) = .dec (.inr 11) (locatedInitializationEntry header stackRank symbolCard symbolRank tm e a backward) := by
  classical
  have h10 : locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward (1 : Fin 4) ≠ locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0 :=
    fun h => (by decide : (1 : Fin 4) ≠ 0) (locatedInitializationExit_injective header stackRank symbolCard symbolRank tm e a backward h)
  simp [locatedAscendingCode, h10]

theorem locatedAscending_advance :
    locatedAscendingCode header stackRank symbolCard symbolRank tm e a backward (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 2) = .inc (.inr 0) (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0) := by
  classical
  have h20 : locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward (2 : Fin 4) ≠ locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0 :=
    fun h => (by decide : (2 : Fin 4) ≠ 0) (locatedInitializationExit_injective header stackRank symbolCard symbolRank tm e a backward h)
  have h21 : locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward (2 : Fin 4) ≠ locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 1 :=
    fun h => (by decide : (2 : Fin 4) ≠ 1) (locatedInitializationExit_injective header stackRank symbolCard symbolRank tm e a backward h)
  simp [locatedAscendingCode, h20, h21]

/-- The private printer run is unchanged when its exits become ascending loop control. -/
theorem locatedAscending_preserves_run {s t : CounterCfg InitializationRegister (LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward (Fin 4))} {count : Nat}
    (h : CounterRun (locatedInitializationCode header stackRank symbolCard symbolRank tm e a backward (fun (_ : Fin 4) => .halt) 2) s count t) (ht : t.pc ≠ none) :
    CounterRun (locatedAscendingCode header stackRank symbolCard symbolRank tm e a backward) s count t := by
  classical
  apply CounterRun.modify_halts _ _ _ h ht
  intro q hn
  have h0 : q ≠ locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0 := by
    intro he
    exact hn (he ▸ locatedInitializationExit_halt header stackRank symbolCard symbolRank tm e a backward 2 0)
  have h1 : q ≠ locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 1 := by
    intro he
    exact hn (he ▸ locatedInitializationExit_halt header stackRank symbolCard symbolRank tm e a backward 2 1)
  have h2 : q ≠ locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 2 := by
    intro he
    exact hn (he ▸ locatedInitializationExit_halt header stackRank symbolCard symbolRank tm e a backward 2 2)
  simp [locatedAscendingCode, h0, h1, h2]

/-- One ascending body prints the current cell and executes the actual index increment. -/
theorem locatedAscending_body (capacity n : Nat) (i : Fin capacity)
    (cs : InitializationRegister → Nat) (hn : cs (.inl 0) = n) (hi : cs (.inr 0) = i.val)
    (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (locatedAscendingCode header stackRank symbolCard symbolRank tm e a backward) ⟨some (locatedInitializationEntry header stackRank symbolCard symbolRank tm e a backward), cs, ys⟩ (locatedInitializationSteps header stackRank symbolCard symbolRank tm e a backward cs + 1)
      ⟨some (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward (0 : Fin 4)), Function.update (locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs) (.inr 0) (i.val + 1),
        initializationCellPayload tm e capacity n i a backward
          (n + 18 * (header + (stackRank * cs (.inl 2) + i.val) * symbolCard + symbolRank)) ++ ys⟩ := by
  have hp := locatedInitialization_run header stackRank symbolCard symbolRank tm e capacity n i a backward
    (fun (_ : Fin 4) => .halt) 2 cs hn hi hb ht ys
  have hp' := locatedAscending_preserves_run header stackRank symbolCard symbolRank tm e a backward hp (by simp)
  have hinc := CounterRun.one (locatedAscendingCode header stackRank symbolCard symbolRank tm e a backward)
    ⟨some (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 2), locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs,
      initializationCellPayload tm e capacity n i a backward
        (n + 18 * (header + (stackRank * cs (.inl 2) + i.val) * symbolCard + symbolRank)) ++ ys⟩
    (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 2) rfl
  rw [locatedAscending_advance] at hinc
  simpa [CounterInstr.eval, locatedInitialization_preserves_index, hi] using CounterRun.trans _ hp' hinc

end ShiReversibleGenerator
