import ReversibleCounterMacros
import ReversibleCounterTM2
import ReversibleCounterRelabel

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

abbrev ClearLabel (L : Type) := Fin 2 ⊕ L

def clearCode (r : R) (caller : L → CounterInstr R L) (stop : L) :
    ClearLabel L → CounterInstr R (ClearLabel L)
  | .inl j => if j.val = 0 then .branch r (.inr stop) (.inl 1) else .dec r (.inl 0)
  | .inr l => (caller l).relabel Sum.inr

theorem clearCode_run (r : R) (caller : L → CounterInstr R L) (stop : L)
    (cs : R → Nat) (ys : List Bool) :
    CounterRun (clearCode r caller stop) ⟨some (.inl 0), cs, ys⟩ (2 * cs r + 1)
      ⟨some (.inr stop), Function.update cs r 0, ys⟩ := by
  have h := clear_counter_run (clearCode r caller stop) r (.inl 0) (.inl 1) (.inr stop)
    rfl rfl ⟨none, cs, ys⟩ (cs r)
  simpa [withCounter] using h

def CleanupLabels : List R → Type → Type
  | [], L => L
  | _ :: rs, L => ClearLabel (CleanupLabels rs L)

def cleanupEntry (rs : List R) (stop : L) : CleanupLabels rs L :=
  match rs with
  | [] => stop
  | _ :: _ => .inl 0

def cleanupExit (rs : List R) (l : L) : CleanupLabels rs L :=
  match rs with
  | [] => l
  | _ :: rs => .inr (cleanupExit rs l)

def cleanupCode (rs : List R) (caller : L → CounterInstr R L) (stop : L) :
    CleanupLabels rs L → CounterInstr R (CleanupLabels rs L) :=
  match rs with
  | [] => caller
  | r :: rs => clearCode r (cleanupCode rs caller stop) (cleanupEntry rs stop)

def cleanupCounters (rs : List R) (cs : R → Nat) : R → Nat :=
  match rs with
  | [] => cs
  | r :: rs => cleanupCounters rs (Function.update cs r 0)

def cleanupSteps (rs : List R) (cs : R → Nat) : Nat :=
  match rs with
  | [] => 0
  | r :: rs => 2 * cs r + 1 + cleanupSteps rs (Function.update cs r 0)

theorem cleanupCode_run (rs : List R) (caller : L → CounterInstr R L) (stop : L)
    (cs : R → Nat) (ys : List Bool) :
    CounterRun (cleanupCode rs caller stop) ⟨some (cleanupEntry rs stop), cs, ys⟩
      (cleanupSteps rs cs) ⟨some (cleanupExit rs stop), cleanupCounters rs cs, ys⟩ := by
  induction rs generalizing cs with
  | nil => exact CounterRun.refl _
  | cons r rs ih =>
      let inner := cleanupCode rs caller stop
      let outer := cleanupCode (r :: rs) caller stop
      have hc := clearCode_run r inner (cleanupEntry rs stop) cs ys
      have hn := ih (Function.update cs r 0)
      have hn' := CounterRun.relabel inner outer Sum.inr (fun _ => rfl) hn
      change CounterRun outer ⟨some (.inr (cleanupEntry rs stop)), Function.update cs r 0, ys⟩
        (cleanupSteps rs (Function.update cs r 0))
        ⟨some (.inr (cleanupExit rs stop)), cleanupCounters rs (Function.update cs r 0), ys⟩ at hn'
      exact CounterRun.trans outer hc hn'

theorem cleanupCode_embed (rs : List R) (caller : L → CounterInstr R L) (stop l : L) :
    cleanupCode rs caller stop (cleanupExit rs l) = (caller l).relabel (cleanupExit rs) := by
  induction rs with
  | nil => change caller l = (caller l).relabel (fun l => l); cases caller l <;> rfl
  | cons r rs ih =>
      change (cleanupCode rs caller stop (cleanupExit rs l)).relabel Sum.inr = _
      rw [ih]
      cases caller l <;> rfl

theorem cleanupCounters_apply (rs : List R) (cs : R → Nat) (r : R) :
    cleanupCounters rs cs r = if r ∈ rs then 0 else cs r := by
  induction rs generalizing cs with
  | nil => simp [cleanupCounters]
  | cons q rs ih =>
      rw [cleanupCounters, ih]
      by_cases h : r ∈ rs <;> by_cases he : r = q <;> simp [h, he]

noncomputable instance cleanupLabelsFintype (rs : List R) [Fintype L] :
    Fintype (CleanupLabels rs L) := by
  induction rs with
  | nil => exact inferInstanceAs (Fintype L)
  | cons r rs ih => letI := ih; exact inferInstanceAs (Fintype (ClearLabel (CleanupLabels rs L)))

/-- Clear every counter, including the original input stack, then actually halt. -/
theorem finalCleanup_run [Fintype R] (cs : R → Nat) (ys : List Bool) :
    let rs := (Finset.univ : Finset R).toList
    CounterRun (cleanupCode rs (fun (_ : Unit) => .halt) ())
      ⟨some (cleanupEntry rs ()), cs, ys⟩ (cleanupSteps rs cs + 1)
      ⟨none, fun _ => 0, ys⟩ := by
  classical
  let rs := (Finset.univ : Finset R).toList
  let code := cleanupCode rs (fun (_ : Unit) => .halt) ()
  have hz : cleanupCounters rs cs = fun _ => 0 := by
    funext r
    simp [cleanupCounters_apply, rs]
  have hc := cleanupCode_run rs (fun (_ : Unit) => .halt) () cs ys
  rw [hz] at hc
  have he : CounterRun code ⟨some (cleanupExit rs ()), fun _ => 0, ys⟩ 1
      ⟨none, fun _ => 0, ys⟩ := by
    have h := CounterRun.one code
      (⟨some (cleanupExit rs ()), fun _ => 0, ys⟩ : CounterCfg R (CleanupLabels rs Unit))
      (cleanupExit rs ()) rfl
    simpa [code, cleanupCode_embed, CounterInstr.relabel, CounterInstr.eval] using h
  exact CounterRun.trans code hc he

noncomputable def cleanupClock (rs : List R) (sizes : R → Polynomial Nat) : Polynomial Nat :=
  match rs with
  | [] => 0
  | r :: rs => Polynomial.C 2 * sizes r + Polynomial.C 1 + cleanupClock rs (Function.update sizes r 0)

theorem cleanupClock_eval (rs : List R) (sizes : R → Polynomial Nat) (n : Nat) :
    (cleanupClock rs sizes).eval n = cleanupSteps rs (fun r => (sizes r).eval n) := by
  induction rs generalizing sizes with
  | nil => simp [cleanupClock, cleanupSteps]
  | cons r rs ih =>
      simp only [cleanupClock, cleanupSteps, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, ih]
      congr 2
      funext j
      by_cases hj : j = r <;> simp [hj]

end ShiReversibleGenerator
