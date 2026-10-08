import ReversibleConstantCoordinateSequence
import ReversibleSymbolCellTraversal

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

theorem constantSequenceExit_injective {L : Type} :
    Function.Injective (constantSequenceExit header stackRank symbolCard backward ars (L := L)) := by
  induction ars with
  | nil => exact Function.injective_id
  | cons ar ars ih =>
      intro l k h
      exact ih (locatedConstantExit_injective header stackRank symbolCard ar.2 ar.1 backward h)

theorem constantSequenceCounters_remaining (cs : InitializationRegister → Nat) :
    constantSequenceCounters header stackRank symbolCard backward ars cs (.inr 11) = cs (.inr 11) := by
  induction ars generalizing cs with
  | nil => rfl
  | cons ar ars ih => rw [constantSequenceCounters, ih, locatedConstant_preserves_remaining]

noncomputable def constantCellLoopCode :
    ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3) →
      CounterInstr InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3)) := by
  classical
  exact reentryCode (constantSequenceCode header stackRank symbolCard backward ars (fun (_ : Fin 3) => .halt) 0)
    (.inr 0) (constantSequenceExit header stackRank symbolCard backward ars 0)
    (constantSequenceExit header stackRank symbolCard backward ars 1)
    (constantSequenceEntry header stackRank symbolCard backward ars 0)
    (constantSequenceExit header stackRank symbolCard backward ars 2)

theorem constantCellLoop_test :
    constantCellLoopCode header stackRank symbolCard backward ars
      (constantSequenceExit header stackRank symbolCard backward ars 0) =
    .branch (.inr 0) (constantSequenceExit header stackRank symbolCard backward ars 2)
      (constantSequenceExit header stackRank symbolCard backward ars 1) := by
  classical
  exact reentryCode_loop _ _ _ _ _ _

theorem constantCellLoop_pop :
    constantCellLoopCode header stackRank symbolCard backward ars
      (constantSequenceExit header stackRank symbolCard backward ars 1) =
    .dec (.inr 0) (constantSequenceEntry header stackRank symbolCard backward ars 0) := by
  classical
  apply reentryCode_pop
  intro h
  exact (by decide : (1 : Fin 3) ≠ 0)
    (constantSequenceExit_injective header stackRank symbolCard backward ars h)

/-- Output bytes at a fixed cell coordinate, independent of the printer's private counters. -/
def constantCellPayload (capacity n index : Nat) : List Bool :=
  ars.reverse.flatMap (fun ar => constantInitializationPayload ar.1 backward
    (n + 18 * (header + (stackRank * capacity + index) * symbolCard + ar.2)))

theorem constantSequencePayload_eq (capacity n index : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hc : cs (.inl 2) = capacity) (hi : cs (.inr 0) = index) :
    constantSequencePayload header stackRank symbolCard backward ars cs =
      constantCellPayload header stackRank symbolCard backward ars capacity n index := by
  simp [constantSequencePayload, constantCellPayload, hn, hc, hi]

end ShiReversibleGenerator
