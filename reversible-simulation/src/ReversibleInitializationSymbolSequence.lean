import ReversibleLocatedBodyBounds
import ReversibleLocatedCaller
import ReversibleLocatedCellTraversal

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool)

def SymbolSequenceLabels : List (Option (MachineSymbol tm) × Nat) → Type → Type
  | [], L => L
  | ar :: ars, L => LocatedInitializationLabels header stackRank symbolCard ar.2 tm e ar.1 backward (SymbolSequenceLabels ars L)

noncomputable instance symbolSequenceFintype {L : Type} [Fintype L]
    (ars : List (Option (MachineSymbol tm) × Nat)) : Fintype (SymbolSequenceLabels header stackRank symbolCard tm e backward ars L) := by
  induction ars with
  | nil => exact inferInstanceAs (Fintype L)
  | cons ar ars ih =>
      letI := ih
      exact inferInstanceAs (Fintype (LocatedInitializationLabels header stackRank symbolCard ar.2 tm e ar.1 backward
        (SymbolSequenceLabels header stackRank symbolCard tm e backward ars L)))

noncomputable def symbolSequenceEntry {L : Type} (ars : List (Option (MachineSymbol tm) × Nat)) (stop : L) :
    SymbolSequenceLabels header stackRank symbolCard tm e backward ars L :=
  match ars with
  | [] => stop
  | ar :: _ => locatedInitializationEntry header stackRank symbolCard ar.2 tm e ar.1 backward

noncomputable def symbolSequenceExit {L : Type} (ars : List (Option (MachineSymbol tm) × Nat)) (stop : L) :
    SymbolSequenceLabels header stackRank symbolCard tm e backward ars L :=
  match ars with
  | [] => stop
  | ar :: ars => locatedInitializationExit header stackRank symbolCard ar.2 tm e ar.1 backward (symbolSequenceExit ars stop)

noncomputable def symbolSequenceCode {L : Type} (ars : List (Option (MachineSymbol tm) × Nat))
    (caller : L → CounterInstr InitializationRegister L) (stop : L) :
    SymbolSequenceLabels header stackRank symbolCard tm e backward ars L → CounterInstr InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars L) :=
  match ars with
  | [] => caller
  | ar :: ars => locatedInitializationCode header stackRank symbolCard ar.2 tm e ar.1 backward (symbolSequenceCode ars caller stop) (symbolSequenceEntry header stackRank symbolCard tm e backward ars stop)

noncomputable def symbolSequenceCounters (ars : List (Option (MachineSymbol tm) × Nat)) (cs : InitializationRegister → Nat) :
    InitializationRegister → Nat :=
  match ars with
  | [] => cs
  | ar :: ars => symbolSequenceCounters ars (locatedInitializationCounters header stackRank symbolCard ar.2 tm e ar.1 backward cs)

noncomputable def symbolSequenceSteps (ars : List (Option (MachineSymbol tm) × Nat)) (cs : InitializationRegister → Nat) : Nat :=
  match ars with
  | [] => 0
  | ar :: ars => locatedInitializationSteps header stackRank symbolCard ar.2 tm e ar.1 backward cs +
      symbolSequenceSteps ars (locatedInitializationCounters header stackRank symbolCard ar.2 tm e ar.1 backward cs)

noncomputable def symbolSequencePayload (ars : List (Option (MachineSymbol tm) × Nat)) (capacity n index : Nat) :=
  ars.reverse.flatMap (fun ar => locatedCellPayload header stackRank symbolCard ar.2 tm e ar.1 backward capacity n index)

theorem symbolSequenceCode_embed {L : Type} (ars : List (Option (MachineSymbol tm) × Nat))
    (caller : L → CounterInstr InitializationRegister L) (stop l : L) :
    symbolSequenceCode header stackRank symbolCard tm e backward ars caller stop (symbolSequenceExit header stackRank symbolCard tm e backward ars l) =
      (caller l).relabel (symbolSequenceExit header stackRank symbolCard tm e backward ars) := by
  induction ars with
  | nil =>
      change caller l = (caller l).relabel (fun l => l)
      cases caller l <;> rfl
  | cons ar ars ih =>
      rw [symbolSequenceCode, symbolSequenceExit, locatedInitializationCode_embed, ih]
      exact CounterInstr.relabel_comp (symbolSequenceExit header stackRank symbolCard tm e backward ars)
        (locatedInitializationExit header stackRank symbolCard ar.2 tm e ar.1 backward) (caller l)

theorem symbolSequenceCounters_metadata (ars : List (Option (MachineSymbol tm) × Nat))
    (cs : InitializationRegister → Nat) (r : WorkspaceRegister) :
    symbolSequenceCounters header stackRank symbolCard tm e backward ars cs (.inl r) = cs (.inl r) := by
  induction ars generalizing cs with
  | nil => rfl
  | cons ar ars ih => rw [symbolSequenceCounters, ih, locatedInitialization_preserves_metadata]

theorem symbolSequenceCounters_index (ars : List (Option (MachineSymbol tm) × Nat))
    (cs : InitializationRegister → Nat) :
    symbolSequenceCounters header stackRank symbolCard tm e backward ars cs (.inr 0) = cs (.inr 0) := by
  induction ars generalizing cs with
  | nil => rfl
  | cons ar ars ih => rw [symbolSequenceCounters, ih, locatedInitialization_preserves_index]

theorem symbolSequenceExit_injective {L : Type} (ars : List (Option (MachineSymbol tm) × Nat)) :
    Function.Injective (symbolSequenceExit header stackRank symbolCard tm e backward ars (L := L)) := by
  induction ars with
  | nil => exact fun _ _ h => h
  | cons ar ars ih =>
      exact fun _ _ h => ih (locatedInitializationExit_injective header stackRank symbolCard ar.2 tm e ar.1 backward h)

theorem symbolSequenceCounters_remaining (ars : List (Option (MachineSymbol tm) × Nat))
    (cs : InitializationRegister → Nat) :
    symbolSequenceCounters header stackRank symbolCard tm e backward ars cs (.inr 11) = cs (.inr 11) := by
  induction ars generalizing cs with
  | nil => rfl
  | cons ar ars ih => rw [symbolSequenceCounters, ih, locatedInitialization_preserves_remaining]

/-- Fixed symbol dispatch prints all symbols of one runtime cell without changing its index. -/
theorem symbolSequence_run {L : Type} (ars : List (Option (MachineSymbol tm) × Nat))
    (caller : L → CounterInstr InitializationRegister L) (stop : L) (capacity n : Nat) (i : Fin capacity)
    (cs : InitializationRegister → Nat) (hn : cs (.inl 0) = n) (hc : cs (.inl 2) = capacity)
    (hi : cs (.inr 0) = i.val) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (symbolSequenceCode header stackRank symbolCard tm e backward ars caller stop)
      ⟨some (symbolSequenceEntry header stackRank symbolCard tm e backward ars stop), cs, ys⟩ (symbolSequenceSteps header stackRank symbolCard tm e backward ars cs)
      ⟨some (symbolSequenceExit header stackRank symbolCard tm e backward ars stop), symbolSequenceCounters header stackRank symbolCard tm e backward ars cs,
        symbolSequencePayload header stackRank symbolCard tm e backward ars capacity n i.val ++ ys⟩ := by
  induction ars generalizing cs ys with
  | nil =>
      change CounterRun caller ⟨some stop, cs, ys⟩ 0 ⟨some stop, cs, ys⟩
      exact CounterRun.refl _
  | cons ar ars ih =>
      let inner := symbolSequenceCode header stackRank symbolCard tm e backward ars caller stop
      let code := symbolSequenceCode header stackRank symbolCard tm e backward (ar :: ars) caller stop
      let next := locatedInitializationCounters header stackRank symbolCard ar.2 tm e ar.1 backward cs
      let bytes := initializationCellPayload tm e capacity n i ar.1 backward
        (n + 18 * (header + (stackRank * capacity + i.val) * symbolCard + ar.2))
      have hp := locatedInitialization_run header stackRank symbolCard ar.2 tm e capacity n i ar.1 backward
        inner (symbolSequenceEntry header stackRank symbolCard tm e backward ars stop) cs hn hi hb ht ys
      have hp' := ih next
        (by simpa [next, locatedInitialization_preserves_metadata] using hn)
        (by simpa [next, locatedInitialization_preserves_metadata] using hc)
        (by simpa [next, locatedInitialization_preserves_index] using hi)
        (by simpa [next, locatedInitialization_preserves_metadata] using hb)
        (by simpa [next, locatedInitialization_preserves_metadata] using ht) (bytes ++ ys)
      have htail := CounterRun.relabel inner code (locatedInitializationExit header stackRank symbolCard ar.2 tm e ar.1 backward)
        (locatedInitializationCode_embed header stackRank symbolCard ar.2 tm e ar.1 backward inner (symbolSequenceEntry header stackRank symbolCard tm e backward ars stop)) hp'
      dsimp only [CounterCfg.relabel, Option.map] at htail
      have hpbytes : CounterRun code
          ⟨some (symbolSequenceEntry header stackRank symbolCard tm e backward (ar :: ars) stop), cs, ys⟩
          (locatedInitializationSteps header stackRank symbolCard ar.2 tm e ar.1 backward cs)
          ⟨some (locatedInitializationExit header stackRank symbolCard ar.2 tm e ar.1 backward (symbolSequenceEntry header stackRank symbolCard tm e backward ars stop)), next, bytes ++ ys⟩ := by
        simpa [SymbolSequenceLabels, code, inner, symbolSequenceCode, symbolSequenceEntry, next, bytes, hc] using hp
      simpa [symbolSequenceSteps, symbolSequenceCounters, symbolSequenceExit, symbolSequencePayload,
        List.reverse_cons, List.flatMap_append, locatedCellPayload, i.isLt, bytes,
        List.append_assoc, next, code] using CounterRun.trans code hpbytes htail

end ShiReversibleGenerator
