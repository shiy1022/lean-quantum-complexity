import ReversibleInitializationSymbolSequence

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
variable (header stackRank symbolCard : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

/-- A separate remaining counter permits ascending cell visits in one fixed finite graph. -/
noncomputable def symbolAscendingCode : (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)) → CounterInstr InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)) := by
  classical
  exact fun q => if q = symbolSequenceExit header stackRank symbolCard tm e backward ars 0 then .branch (.inr 11) (symbolSequenceExit header stackRank symbolCard tm e backward ars 3) (symbolSequenceExit header stackRank symbolCard tm e backward ars 1)
    else if q = symbolSequenceExit header stackRank symbolCard tm e backward ars 1 then .dec (.inr 11) (symbolSequenceEntry header stackRank symbolCard tm e backward ars 2)
    else if q = symbolSequenceExit header stackRank symbolCard tm e backward ars 2 then .inc (.inr 0) (symbolSequenceExit header stackRank symbolCard tm e backward ars 0)
    else symbolSequenceCode header stackRank symbolCard tm e backward ars (fun (_ : Fin 4) => .halt) 2 q

theorem symbolAscending_test :
    symbolAscendingCode header stackRank symbolCard tm e backward ars (symbolSequenceExit header stackRank symbolCard tm e backward ars 0) = .branch (.inr 11) (symbolSequenceExit header stackRank symbolCard tm e backward ars 3) (symbolSequenceExit header stackRank symbolCard tm e backward ars 1) := by
  classical
  simp [symbolAscendingCode]

theorem symbolAscending_pop :
    symbolAscendingCode header stackRank symbolCard tm e backward ars (symbolSequenceExit header stackRank symbolCard tm e backward ars 1) = .dec (.inr 11) (symbolSequenceEntry header stackRank symbolCard tm e backward ars 2) := by
  classical
  have h10 : symbolSequenceExit header stackRank symbolCard tm e backward ars (1 : Fin 4) ≠ symbolSequenceExit header stackRank symbolCard tm e backward ars 0 :=
    fun h => (by decide : (1 : Fin 4) ≠ 0) (symbolSequenceExit_injective header stackRank symbolCard tm e backward ars h)
  simp [symbolAscendingCode, h10]

theorem symbolAscending_advance :
    symbolAscendingCode header stackRank symbolCard tm e backward ars (symbolSequenceExit header stackRank symbolCard tm e backward ars 2) = .inc (.inr 0) (symbolSequenceExit header stackRank symbolCard tm e backward ars 0) := by
  classical
  have h20 : symbolSequenceExit header stackRank symbolCard tm e backward ars (2 : Fin 4) ≠ symbolSequenceExit header stackRank symbolCard tm e backward ars 0 :=
    fun h => (by decide : (2 : Fin 4) ≠ 0) (symbolSequenceExit_injective header stackRank symbolCard tm e backward ars h)
  have h21 : symbolSequenceExit header stackRank symbolCard tm e backward ars (2 : Fin 4) ≠ symbolSequenceExit header stackRank symbolCard tm e backward ars 1 :=
    fun h => (by decide : (2 : Fin 4) ≠ 1) (symbolSequenceExit_injective header stackRank symbolCard tm e backward ars h)
  simp [symbolAscendingCode, h20, h21]

/-- The private printer run is unchanged when its exits become ascending loop control. -/
theorem symbolAscending_preserves_run {s t : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4))} {count : Nat}
    (h : CounterRun (symbolSequenceCode header stackRank symbolCard tm e backward ars (fun (_ : Fin 4) => .halt) 2) s count t) (ht : t.pc ≠ none) :
    CounterRun (symbolAscendingCode header stackRank symbolCard tm e backward ars) s count t := by
  classical
  apply CounterRun.modify_halts _ _ _ h ht
  intro q hn
  have h0 : q ≠ symbolSequenceExit header stackRank symbolCard tm e backward ars 0 := by
    intro he
    exact hn (he ▸ (by rw [symbolSequenceCode_embed]; rfl))
  have h1 : q ≠ symbolSequenceExit header stackRank symbolCard tm e backward ars 1 := by
    intro he
    exact hn (he ▸ (by rw [symbolSequenceCode_embed]; rfl))
  have h2 : q ≠ symbolSequenceExit header stackRank symbolCard tm e backward ars 2 := by
    intro he
    exact hn (he ▸ (by rw [symbolSequenceCode_embed]; rfl))
  simp [symbolAscendingCode, h0, h1, h2]

/-- One complete symbol-dispatch body executes the actual cell-index increment. -/
theorem symbolAscending_body (capacity n : Nat) (i : Fin capacity)
    (cs : InitializationRegister → Nat) (hn : cs (.inl 0) = n)
    (hc : cs (.inl 2) = capacity) (hi : cs (.inr 0) = i.val)
    (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (symbolAscendingCode header stackRank symbolCard tm e backward ars)
      ⟨some (symbolSequenceEntry header stackRank symbolCard tm e backward ars (2 : Fin 4)), cs, ys⟩
      (symbolSequenceSteps header stackRank symbolCard tm e backward ars cs + 1)
      ⟨some (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 4)),
        Function.update (symbolSequenceCounters header stackRank symbolCard tm e backward ars cs)
          (.inr 0) (i.val + 1),
        symbolSequencePayload header stackRank symbolCard tm e backward ars capacity n i.val ++ ys⟩ := by
  have hp := symbolSequence_run header stackRank symbolCard tm e backward ars
    (fun (_ : Fin 4) => .halt) 2 capacity n i cs hn hc hi hb ht ys
  have hp' := symbolAscending_preserves_run header stackRank symbolCard tm e backward ars hp (by simp)
  have hinc := CounterRun.one (symbolAscendingCode header stackRank symbolCard tm e backward ars)
    ⟨some (symbolSequenceExit header stackRank symbolCard tm e backward ars (2 : Fin 4)),
      symbolSequenceCounters header stackRank symbolCard tm e backward ars cs,
      symbolSequencePayload header stackRank symbolCard tm e backward ars capacity n i.val ++ ys⟩
    (symbolSequenceExit header stackRank symbolCard tm e backward ars 2) rfl
  rw [symbolAscending_advance] at hinc
  simpa [CounterInstr.eval, symbolSequenceCounters_index, hi] using CounterRun.trans _ hp' hinc

end ShiReversibleGenerator
