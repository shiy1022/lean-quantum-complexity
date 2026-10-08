import ReversibleLocatedConstantPolynomials

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard : Nat) (backward : Bool)

def ConstantSequenceLabels : List (Bool × Nat) → Type → Type
  | [], L => L
  | ar :: ars, L => LocatedConstantLabels header stackRank symbolCard ar.2 ar.1 backward (ConstantSequenceLabels ars L)

noncomputable instance constantSequenceFintype {L : Type} [Fintype L] (ars : List (Bool × Nat)) :
    Fintype (ConstantSequenceLabels header stackRank symbolCard backward ars L) := by
  induction ars with
  | nil => exact inferInstanceAs (Fintype L)
  | cons ar ars ih =>
      letI := ih
      exact inferInstanceAs (Fintype (LocatedConstantLabels header stackRank symbolCard ar.2 ar.1 backward
        (ConstantSequenceLabels header stackRank symbolCard backward ars L)))

def constantSequenceEntry {L : Type} (ars : List (Bool × Nat)) (stop : L) :
    ConstantSequenceLabels header stackRank symbolCard backward ars L :=
  match ars with
  | [] => stop
  | ar :: ars => locatedConstantEntry header stackRank symbolCard ar.2 ar.1 backward (constantSequenceEntry ars stop)

def constantSequenceExit {L : Type} (ars : List (Bool × Nat)) (stop : L) :
    ConstantSequenceLabels header stackRank symbolCard backward ars L :=
  match ars with
  | [] => stop
  | ar :: ars => locatedConstantExit header stackRank symbolCard ar.2 ar.1 backward (constantSequenceExit ars stop)

def constantSequenceCode {L : Type} (ars : List (Bool × Nat))
    (caller : L → CounterInstr InitializationRegister L) (stop : L) :
    ConstantSequenceLabels header stackRank symbolCard backward ars L →
      CounterInstr InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars L) :=
  match ars with
  | [] => caller
  | ar :: ars => locatedConstantCode header stackRank symbolCard ar.2 ar.1 backward
      (constantSequenceCode ars caller stop) (constantSequenceEntry header stackRank symbolCard backward ars stop)

def constantSequenceCounters (ars : List (Bool × Nat)) (cs : InitializationRegister → Nat) : InitializationRegister → Nat :=
  match ars with
  | [] => cs
  | ar :: ars => constantSequenceCounters ars (locatedConstantCounters header stackRank symbolCard ar.2 ar.1 backward cs)

def constantSequenceSteps (ars : List (Bool × Nat)) (cs : InitializationRegister → Nat) : Nat :=
  match ars with
  | [] => 0
  | ar :: ars => locatedConstantSteps header stackRank symbolCard ar.2 ar.1 backward cs +
      constantSequenceSteps ars (locatedConstantCounters header stackRank symbolCard ar.2 ar.1 backward cs)

def constantSequencePayload (ars : List (Bool × Nat)) (cs : InitializationRegister → Nat) :=
  ars.reverse.flatMap (fun ar => constantInitializationPayload ar.1 backward
    (cs (.inl 0) + 18 * (header + (stackRank * cs (.inl 2) + cs (.inr 0)) * symbolCard + ar.2)))

theorem constantSequenceCode_embed {L : Type} (ars : List (Bool × Nat))
    (caller : L → CounterInstr InitializationRegister L) (stop l : L) :
    constantSequenceCode header stackRank symbolCard backward ars caller stop
      (constantSequenceExit header stackRank symbolCard backward ars l) =
      (caller l).relabel (constantSequenceExit header stackRank symbolCard backward ars) := by
  induction ars with
  | nil =>
      change caller l = (caller l).relabel (fun l => l)
      cases caller l <;> rfl
  | cons ar ars ih =>
      rw [constantSequenceCode, constantSequenceExit, locatedConstantCode_embed, ih]
      exact CounterInstr.relabel_comp (constantSequenceExit header stackRank symbolCard backward ars)
        (locatedConstantExit header stackRank symbolCard ar.2 ar.1 backward) (caller l)

theorem constantSequenceCounters_metadata (ars : List (Bool × Nat))
    (cs : InitializationRegister → Nat) (r : WorkspaceRegister) :
    constantSequenceCounters header stackRank symbolCard backward ars cs (.inl r) = cs (.inl r) := by
  induction ars generalizing cs with
  | nil => rfl
  | cons ar ars ih => rw [constantSequenceCounters, ih, locatedConstant_preserves_metadata]

theorem constantSequenceCounters_index (ars : List (Bool × Nat)) (cs : InitializationRegister → Nat) :
    constantSequenceCounters header stackRank symbolCard backward ars cs (.inr 0) = cs (.inr 0) := by
  induction ars generalizing cs with
  | nil => rfl
  | cons ar ars ih => rw [constantSequenceCounters, ih, locatedConstant_preserves_index]

/-- Concrete fixed coordinate literals dispatch actual constant printers, preserving all sources. -/
theorem constantSequence_run {L : Type} (ars : List (Bool × Nat))
    (caller : L → CounterInstr InitializationRegister L) (stop : L)
    (cs : InitializationRegister → Nat) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (constantSequenceCode header stackRank symbolCard backward ars caller stop)
      ⟨some (constantSequenceEntry header stackRank symbolCard backward ars stop), cs, ys⟩
      (constantSequenceSteps header stackRank symbolCard backward ars cs)
      ⟨some (constantSequenceExit header stackRank symbolCard backward ars stop),
        constantSequenceCounters header stackRank symbolCard backward ars cs,
        constantSequencePayload header stackRank symbolCard backward ars cs ++ ys⟩ := by
  induction ars generalizing cs ys with
  | nil => exact CounterRun.refl _
  | cons ar ars ih =>
      let inner := constantSequenceCode header stackRank symbolCard backward ars caller stop
      let code := constantSequenceCode header stackRank symbolCard backward (ar :: ars) caller stop
      let next := locatedConstantCounters header stackRank symbolCard ar.2 ar.1 backward cs
      let bytes := constantInitializationPayload ar.1 backward
        (cs (.inl 0) + 18 * (header + (stackRank * cs (.inl 2) + cs (.inr 0)) * symbolCard + ar.2))
      have hp := locatedConstant_run header stackRank symbolCard ar.2 ar.1 backward inner
        (constantSequenceEntry header stackRank symbolCard backward ars stop) cs hb ht ys
      have hp' := ih next
        (by simpa [next, locatedConstant_preserves_metadata] using hb)
        (by simpa [next, locatedConstant_preserves_metadata] using ht) (bytes ++ ys)
      have htail := CounterRun.relabel inner code (locatedConstantExit header stackRank symbolCard ar.2 ar.1 backward)
        (locatedConstantCode_embed header stackRank symbolCard ar.2 ar.1 backward inner
          (constantSequenceEntry header stackRank symbolCard backward ars stop)) hp'
      dsimp only [CounterCfg.relabel, Option.map] at htail
      set_option backward.isDefEq.respectTransparency false in
        simpa [constantSequenceCode, constantSequenceEntry, constantSequenceExit,
          constantSequenceSteps, constantSequenceCounters, constantSequencePayload,
          List.reverse_cons, List.flatMap_append, List.append_assoc, next, bytes, inner, code,
          locatedConstant_preserves_metadata, locatedConstant_preserves_index] using CounterRun.trans code hp htail

/-- Finite dispatch has an actual polynomial instruction clock from arbitrary polynomial counter bounds. -/
theorem constantSequence_polynomial_bound (ars : List (Bool × Nat))
    (sizes : InitializationRegister → Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat),
      (∀ r, cs r ≤ (sizes r).eval n) →
      constantSequenceSteps header stackRank symbolCard backward ars cs ≤ clock.eval n := by
  induction ars generalizing sizes with
  | nil => exact ⟨0, by intros; simp [constantSequenceSteps]⟩
  | cons ar ars ih =>
      let nextSizes := locatedConstantCounterPolynomials header stackRank symbolCard ar.2 ar.1 backward sizes
      obtain ⟨first, hf⟩ := locatedConstant_polynomial_bound header stackRank symbolCard ar.2 ar.1 backward sizes
      obtain ⟨rest, hr⟩ := ih nextSizes
      refine ⟨first + rest, ?_⟩
      intro n cs h
      have hn : ∀ r, locatedConstantCounters header stackRank symbolCard ar.2 ar.1 backward cs r ≤ (nextSizes r).eval n := by
        intro r
        change locatedConstantCounters header stackRank symbolCard ar.2 ar.1 backward cs r ≤
          (locatedConstantCounterPolynomials header stackRank symbolCard ar.2 ar.1 backward sizes r).eval n
        rw [congrFun (locatedConstantCounterPolynomials_eval header stackRank symbolCard ar.2 ar.1 backward sizes n) r]
        exact locatedConstantCounters_mono header stackRank symbolCard ar.2 ar.1 backward cs _ h r
      have hrest := hr n (locatedConstantCounters header stackRank symbolCard ar.2 ar.1 backward cs) hn
      simpa only [constantSequenceSteps, Polynomial.eval_add] using Nat.add_le_add (hf n cs h) hrest

end ShiReversibleGenerator
