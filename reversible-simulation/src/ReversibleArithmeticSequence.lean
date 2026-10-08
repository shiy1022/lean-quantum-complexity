import ReversibleAffineFragment

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

/-- Fixed coefficients and register names; values are obtained at runtime. -/
structure AffineAtom (R : Type) where
  source : R
  target : R
  offset : Nat
  coefficient : Nat

def AffineAtom.apply (a : AffineAtom R) (cs : R → Nat) : R → Nat :=
  Function.update cs a.target (cs a.target + a.coefficient * cs a.source + a.offset)

def AffineAtom.Valid (a : AffineAtom R) (tmp : R) : Prop :=
  a.source ≠ a.target ∧ a.source ≠ tmp ∧ a.target ≠ tmp

def AffineAtom.steps (a : AffineAtom R) (cs : R → Nat) : Nat :=
  a.coefficient * (7 * cs a.source + 2) + a.offset

theorem AffineAtom.run (a : AffineAtom R) (caller : L → CounterInstr R L)
    (tmp : R) (stop : L) (ha : a.Valid tmp) (cs : R → Nat) (ht : cs tmp = 0)
    (ys : List Bool) :
    CounterRun (affineCode caller a.offset a.coefficient a.source a.target tmp stop)
      ⟨some (affineStart a.offset a.coefficient stop), cs, ys⟩ (a.steps cs)
      ⟨some (.inr (.inr stop)), a.apply cs, ys⟩ := by
  let base : CounterCfg R (AffineLabel a.offset a.coefficient L) := ⟨none, cs, ys⟩
  have h := affineCode_run caller a.offset a.coefficient a.source a.target tmp stop
    ha.1 ha.2.1 ha.2.2 base (cs a.source) (cs a.target)
  have hi : copyState base a.source a.target tmp (cs a.source) (cs a.target) 0
      (affineStart a.offset a.coefficient stop) =
      ⟨some (affineStart a.offset a.coefficient stop), cs, ys⟩ := by
    apply CounterCfg.ext
    · rfl
    · funext r
      by_cases hr : r = tmp
      · subst r; simp [copyState, base, ht]
      · simp [copyState, base, hr]
    · rfl
  have ho : copyState base a.source a.target tmp (cs a.source)
      (cs a.target + a.coefficient * cs a.source + a.offset) 0 (.inr (.inr stop)) =
      ⟨some (.inr (.inr stop)), a.apply cs, ys⟩ := by
    apply CounterCfg.ext
    · rfl
    · funext r
      by_cases hr : r = tmp
      · subst r; simp [copyState, base, AffineAtom.apply, ht, Ne.symm ha.2.2]
      · simp [copyState, base, AffineAtom.apply, hr]
    · rfl
  simpa only [hi, ho, AffineAtom.steps] using h

@[simp] theorem AffineAtom.apply_scratch (a : AffineAtom R) (tmp : R)
    (ha : a.Valid tmp) (cs : R → Nat) : a.apply cs tmp = cs tmp := by
  simp [AffineAtom.apply, Ne.symm ha.2.2]

def ArithmeticLabels : List (AffineAtom R) → Type → Type
  | [], L => L
  | a :: atoms, L => AffineLabel a.offset a.coefficient (ArithmeticLabels atoms L)

def arithmeticEntry (atoms : List (AffineAtom R)) (stop : L) : ArithmeticLabels atoms L :=
  match atoms with
  | [] => stop
  | a :: atoms => affineStart a.offset a.coefficient (arithmeticEntry atoms stop)

def arithmeticExit (atoms : List (AffineAtom R)) (stop : L) : ArithmeticLabels atoms L :=
  match atoms with
  | [] => stop
  | _ :: atoms => .inr (.inr (arithmeticExit atoms stop))

def arithmeticCode (atoms : List (AffineAtom R)) (caller : L → CounterInstr R L)
    (tmp : R) (stop : L) : ArithmeticLabels atoms L → CounterInstr R (ArithmeticLabels atoms L) :=
  match atoms with
  | [] => caller
  | a :: atoms => affineCode (arithmeticCode atoms caller tmp stop) a.offset a.coefficient
      a.source a.target tmp (arithmeticEntry atoms stop)

def arithmeticResult (atoms : List (AffineAtom R)) (cs : R → Nat) : R → Nat :=
  match atoms with
  | [] => cs
  | a :: atoms => arithmeticResult atoms (a.apply cs)

def arithmeticSteps (atoms : List (AffineAtom R)) (cs : R → Nat) : Nat :=
  match atoms with
  | [] => 0
  | a :: atoms => a.steps cs + arithmeticSteps atoms (a.apply cs)

/-- A whole arithmetic prelude is a finite instruction graph with exact counts. -/
theorem arithmeticCode_run (atoms : List (AffineAtom R)) (caller : L → CounterInstr R L)
    (tmp : R) (stop : L) (ha : ∀ a ∈ atoms, a.Valid tmp) (cs : R → Nat)
    (ht : cs tmp = 0) (ys : List Bool) :
    CounterRun (arithmeticCode atoms caller tmp stop)
      ⟨some (arithmeticEntry atoms stop), cs, ys⟩ (arithmeticSteps atoms cs)
      ⟨some (arithmeticExit atoms stop), arithmeticResult atoms cs, ys⟩ := by
  induction atoms generalizing cs with
  | nil => exact CounterRun.refl _
  | cons a atoms ih =>
      let inner := arithmeticCode atoms caller tmp stop
      let prg := arithmeticCode (a :: atoms) caller tmp stop
      have h₁ := a.run inner tmp (arithmeticEntry atoms stop) (ha a (by simp)) cs ht ys
      have h₂ := ih (fun b hb => ha b (by simp [hb])) (a.apply cs)
        (by rw [AffineAtom.apply_scratch a tmp (ha a (by simp))]; exact ht)
      have h₃ := CounterRun.relabel inner prg (fun l => Sum.inr (Sum.inr l))
        (fun l => by
          change ((inner l).relabel Sum.inr).relabel Sum.inr =
            (inner l).relabel (fun l => Sum.inr (Sum.inr l))
          exact CounterInstr.relabel_comp Sum.inr Sum.inr (inner l)) h₂
      change CounterRun prg
        ⟨some (.inr (.inr (arithmeticEntry atoms stop))), a.apply cs, ys⟩
        (arithmeticSteps atoms (a.apply cs))
        ⟨some (.inr (.inr (arithmeticExit atoms stop))), arithmeticResult atoms (a.apply cs), ys⟩ at h₃
      have h := CounterRun.trans prg h₁ h₃
      convert h using 1 <;> (try simp [prg, arithmeticEntry, arithmeticExit, arithmeticSteps,
        arithmeticResult]) <;> rfl

noncomputable instance arithmeticLabelsFintype (atoms : List (AffineAtom R)) [Fintype L] :
    Fintype (ArithmeticLabels atoms L) := by
  induction atoms with
  | nil => exact inferInstanceAs (Fintype L)
  | cons a atoms ih =>
      letI := ih
      exact inferInstanceAs (Fintype (AffineLabel a.offset a.coefficient (ArithmeticLabels atoms L)))


noncomputable def AffineAtom.applyPolynomial (a : AffineAtom R) (sizes : R → Polynomial Nat) : R → Polynomial Nat :=
  Function.update sizes a.target (sizes a.target + Polynomial.C a.coefficient * sizes a.source +
    Polynomial.C a.offset)

theorem AffineAtom.applyPolynomial_eval (a : AffineAtom R) (sizes : R → Polynomial Nat) (n : Nat) :
    (fun r => (a.applyPolynomial sizes r).eval n) = a.apply (fun r => (sizes r).eval n) := by
  funext r
  by_cases h : r = a.target
  · subst r; simp [AffineAtom.applyPolynomial, AffineAtom.apply]
  · simp [AffineAtom.applyPolynomial, AffineAtom.apply, h]

/-- The clock evaluates subsequent operations at the updated register sizes. -/
noncomputable def arithmeticClock (atoms : List (AffineAtom R)) (sizes : R → Polynomial Nat) : Polynomial Nat :=
  match atoms with
  | [] => 0
  | a :: atoms => Polynomial.C a.coefficient *
      (Polynomial.C 7 * sizes a.source + Polynomial.C 2) + Polynomial.C a.offset +
      arithmeticClock atoms (a.applyPolynomial sizes)

theorem arithmeticClock_eval (atoms : List (AffineAtom R)) (sizes : R → Polynomial Nat) (n : Nat) :
    (arithmeticClock atoms sizes).eval n = arithmeticSteps atoms (fun r => (sizes r).eval n) := by
  induction atoms generalizing sizes with
  | nil => simp [arithmeticClock, arithmeticSteps]
  | cons a atoms ih =>
      simp only [arithmeticClock, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        arithmeticSteps, AffineAtom.steps, ih, AffineAtom.applyPolynomial_eval]

end ShiReversibleGenerator
