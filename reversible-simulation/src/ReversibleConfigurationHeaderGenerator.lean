import ReversibleConstantCoordinateSequence
import ReversibleInitializationStart

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding ShiReversibleFormula
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

/-- Fixed label/memory values and their exact configuration-coordinate ranks. -/
noncomputable def initializationHeaderRanks (tm : Turing.FinTM2) : List (Bool × Nat) := by
  classical
  exact List.ofFn (fun j : Fin (Fintype.card (Option tm.Λ)) =>
    (oneHot (some tm.main) ((Fintype.equivFin (Option tm.Λ)).symm j), j.val)) ++
    List.ofFn (fun j : Fin (Fintype.card tm.σ) =>
      (oneHot tm.initialState ((Fintype.equivFin tm.σ).symm j), Fintype.card (Option tm.Λ) + j.val))

noncomputable def initializationHeaderSchedule (tm : Turing.FinTM2) (backward : Bool) :=
  if backward then initializationHeaderRanks tm else (initializationHeaderRanks tm).reverse

noncomputable def configurationHeaderCode {L : Type} (tm : Turing.FinTM2) (backward : Bool)
    (caller : L → CounterInstr InitializationRegister L) (stop : L) :=
  constantSequenceCode 0 0 0 backward (initializationHeaderSchedule tm backward) caller stop

noncomputable def configurationHeaderPayload (tm : Turing.FinTM2) (backward : Bool) (n : Nat) :=
  (if backward then (initializationHeaderRanks tm).reverse else initializationHeaderRanks tm).flatMap
    (fun ar => constantInitializationPayload ar.1 backward (n + 18 * ar.2))

theorem configurationHeader_payload (tm : Turing.FinTM2) (backward : Bool)
    (cs : InitializationRegister → Nat) :
    constantSequencePayload 0 0 0 backward (initializationHeaderSchedule tm backward) cs =
      configurationHeaderPayload tm backward (cs (.inl 0)) := by
  cases backward <;> simp [constantSequencePayload, initializationHeaderSchedule, configurationHeaderPayload]

/-- Fixed label/memory dispatch is an actual finite counter program in both directions. -/
theorem configurationHeader_run {L : Type} (tm : Turing.FinTM2) (backward : Bool)
    (caller : L → CounterInstr InitializationRegister L) (stop : L)
    (cs : InitializationRegister → Nat) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (configurationHeaderCode tm backward caller stop)
      ⟨some (constantSequenceEntry 0 0 0 backward (initializationHeaderSchedule tm backward) stop), cs, ys⟩
      (constantSequenceSteps 0 0 0 backward (initializationHeaderSchedule tm backward) cs)
      ⟨some (constantSequenceExit 0 0 0 backward (initializationHeaderSchedule tm backward) stop),
        constantSequenceCounters 0 0 0 backward (initializationHeaderSchedule tm backward) cs,
        configurationHeaderPayload tm backward (cs (.inl 0)) ++ ys⟩ := by
  have h := constantSequence_run 0 0 0 backward (initializationHeaderSchedule tm backward) caller stop cs hb ht ys
  rw [configurationHeader_payload] at h
  exact h

/-- The actual resource-prelude counters have exact polynomial evaluations. -/
noncomputable def initializationPreludePolynomials (tm : Turing.FinTM2) (time : Polynomial Nat) :
    InitializationRegister → Polynomial Nat :=
  Sum.elim (resourceCounterPolynomials tm time) (fun _ => 0)

theorem initializationPreludePolynomials_eval (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat) :
    (fun r => (initializationPreludePolynomials tm time r).eval n) = initializationPreludeCounters tm time n := by
  funext r
  cases r with
  | inl r => exact congrFun (resourceCounterPolynomials_eval tm time n) r
  | inr r => simp [initializationPreludePolynomials, initializationPreludeCounters]

/-- The header clock bounds execution from the concrete prelude, rather than an assumed state. -/
theorem configurationHeader_clock (tm : Turing.FinTM2) (backward : Bool) (time : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n,
      constantSequenceSteps 0 0 0 backward (initializationHeaderSchedule tm backward)
        (initializationPreludeCounters tm time n) ≤ clock.eval n := by
  obtain ⟨clock, hc⟩ := constantSequence_polynomial_bound 0 0 0 backward (initializationHeaderSchedule tm backward)
    (initializationPreludePolynomials tm time)
  refine ⟨clock, ?_⟩
  intro n
  apply hc
  intro r
  exact (congrFun (initializationPreludePolynomials_eval tm time n) r).ge

end ShiReversibleGenerator
