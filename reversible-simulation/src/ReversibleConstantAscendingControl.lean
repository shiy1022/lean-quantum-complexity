import ReversibleConstantSequenceControl

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard : Nat)
    (backward : Bool) (ars : List (Bool × Nat))

/-- A separate remaining counter permits ascending cell visits in one fixed finite graph. -/
noncomputable def constantAscendingCode : (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)) → CounterInstr InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)) := by
  classical
  exact fun q => if q = constantSequenceExit header stackRank symbolCard backward ars 0 then .branch (.inr 11) (constantSequenceExit header stackRank symbolCard backward ars 3) (constantSequenceExit header stackRank symbolCard backward ars 1)
    else if q = constantSequenceExit header stackRank symbolCard backward ars 1 then .dec (.inr 11) (constantSequenceEntry header stackRank symbolCard backward ars 2)
    else if q = constantSequenceExit header stackRank symbolCard backward ars 2 then .inc (.inr 0) (constantSequenceExit header stackRank symbolCard backward ars 0)
    else constantSequenceCode header stackRank symbolCard backward ars (fun (_ : Fin 4) => .halt) 2 q

theorem constantAscending_test :
    constantAscendingCode header stackRank symbolCard backward ars (constantSequenceExit header stackRank symbolCard backward ars 0) = .branch (.inr 11) (constantSequenceExit header stackRank symbolCard backward ars 3) (constantSequenceExit header stackRank symbolCard backward ars 1) := by
  classical
  simp [constantAscendingCode]

theorem constantAscending_pop :
    constantAscendingCode header stackRank symbolCard backward ars (constantSequenceExit header stackRank symbolCard backward ars 1) = .dec (.inr 11) (constantSequenceEntry header stackRank symbolCard backward ars 2) := by
  classical
  have h10 : constantSequenceExit header stackRank symbolCard backward ars (1 : Fin 4) ≠ constantSequenceExit header stackRank symbolCard backward ars 0 :=
    fun h => (by decide : (1 : Fin 4) ≠ 0) (constantSequenceExit_injective header stackRank symbolCard backward ars h)
  simp [constantAscendingCode, h10]

theorem constantAscending_advance :
    constantAscendingCode header stackRank symbolCard backward ars (constantSequenceExit header stackRank symbolCard backward ars 2) = .inc (.inr 0) (constantSequenceExit header stackRank symbolCard backward ars 0) := by
  classical
  have h20 : constantSequenceExit header stackRank symbolCard backward ars (2 : Fin 4) ≠ constantSequenceExit header stackRank symbolCard backward ars 0 :=
    fun h => (by decide : (2 : Fin 4) ≠ 0) (constantSequenceExit_injective header stackRank symbolCard backward ars h)
  have h21 : constantSequenceExit header stackRank symbolCard backward ars (2 : Fin 4) ≠ constantSequenceExit header stackRank symbolCard backward ars 1 :=
    fun h => (by decide : (2 : Fin 4) ≠ 1) (constantSequenceExit_injective header stackRank symbolCard backward ars h)
  simp [constantAscendingCode, h20, h21]

/-- The private printer run is unchanged when its exits become ascending loop control. -/
theorem constantAscending_preserves_run {s t : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4))} {count : Nat}
    (h : CounterRun (constantSequenceCode header stackRank symbolCard backward ars (fun (_ : Fin 4) => .halt) 2) s count t) (ht : t.pc ≠ none) :
    CounterRun (constantAscendingCode header stackRank symbolCard backward ars) s count t := by
  classical
  apply CounterRun.modify_halts _ _ _ h ht
  intro q hn
  have h0 : q ≠ constantSequenceExit header stackRank symbolCard backward ars 0 := by
    intro he
    exact hn (he ▸ (by rw [constantSequenceCode_embed]; rfl))
  have h1 : q ≠ constantSequenceExit header stackRank symbolCard backward ars 1 := by
    intro he
    exact hn (he ▸ (by rw [constantSequenceCode_embed]; rfl))
  have h2 : q ≠ constantSequenceExit header stackRank symbolCard backward ars 2 := by
    intro he
    exact hn (he ▸ (by rw [constantSequenceCode_embed]; rfl))
  simp [constantAscendingCode, h0, h1, h2]

/-- One complete symbol-dispatch body executes the actual cell-index increment. -/
theorem constantAscending_body (cs : InitializationRegister → Nat)
    (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (constantAscendingCode header stackRank symbolCard backward ars)
      ⟨some (constantSequenceEntry header stackRank symbolCard backward ars (2 : Fin 4)), cs, ys⟩
      (constantSequenceSteps header stackRank symbolCard backward ars cs + 1)
      ⟨some (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 4)),
        Function.update (constantSequenceCounters header stackRank symbolCard backward ars cs)
          (.inr 0) (cs (.inr 0) + 1),
        constantSequencePayload header stackRank symbolCard backward ars cs ++ ys⟩ := by
  have hp := constantSequence_run header stackRank symbolCard backward ars
    (fun (_ : Fin 4) => .halt) 2 cs hb ht ys
  have hp' := constantAscending_preserves_run header stackRank symbolCard backward ars hp (by simp)
  have hinc := CounterRun.one (constantAscendingCode header stackRank symbolCard backward ars)
    ⟨some (constantSequenceExit header stackRank symbolCard backward ars (2 : Fin 4)),
      constantSequenceCounters header stackRank symbolCard backward ars cs,
      constantSequencePayload header stackRank symbolCard backward ars cs ++ ys⟩
    (constantSequenceExit header stackRank symbolCard backward ars 2) rfl
  rw [constantAscending_advance] at hinc
  simpa [CounterInstr.eval, constantSequenceCounters_index] using CounterRun.trans _ hp' hinc

end ShiReversibleGenerator
