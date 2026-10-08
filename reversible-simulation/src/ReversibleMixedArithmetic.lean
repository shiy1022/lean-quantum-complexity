import ReversibleArithmeticSequence
import ReversibleProductFragment

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

structure ProductAtom (R : Type) where
  left : R
  right : R
  target : R

inductive GeneratorOperation (R : Type) where
  | affine : AffineAtom R → GeneratorOperation R
  | product : ProductAtom R → GeneratorOperation R

def GeneratorOperation.Label (op : GeneratorOperation R) (L : Type) : Type :=
  match op with
  | .affine a => AffineLabel a.offset a.coefficient L
  | .product _ => PreservedProductLabel L

def GeneratorOperation.embed (op : GeneratorOperation R) (l : L) : op.Label L :=
  match op with
  | .affine _ => .inr (.inr l)
  | .product _ => .inr (.inr l)

def GeneratorOperation.entry (op : GeneratorOperation R) (stop : L) : op.Label L :=
  match op with
  | .affine a => affineStart a.offset a.coefficient stop
  | .product _ => copyFrom 1 (.inl 0) 0

def GeneratorOperation.code (op : GeneratorOperation R) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop : L) : op.Label L → CounterInstr R (op.Label L) :=
  match op with
  | .affine a => affineCode caller a.offset a.coefficient a.source a.target tmp stop
  | .product p => preservedProductCode caller p.left p.right p.target buf tmp stop

def GeneratorOperation.apply (op : GeneratorOperation R) (cs : R → Nat) : R → Nat :=
  match op with
  | .affine a => a.apply cs
  | .product p => Function.update cs p.target (cs p.target + cs p.left * cs p.right)

def GeneratorOperation.Valid (op : GeneratorOperation R) (buf tmp : R) : Prop :=
  match op with
  | .affine a => a.Valid tmp ∧ a.target ≠ buf
  | .product p => p.left ≠ p.right ∧ p.left ≠ p.target ∧ p.left ≠ buf ∧ p.left ≠ tmp ∧
      p.right ≠ p.target ∧ p.right ≠ buf ∧ p.right ≠ tmp ∧ p.target ≠ buf ∧ p.target ≠ tmp

def GeneratorOperation.steps (op : GeneratorOperation R) (cs : R → Nat) : Nat :=
  match op with
  | .affine a => a.steps cs
  | .product p => (7 * cs p.left + 2) + (cs p.left * (7 * cs p.right + 4) + 1)

theorem GeneratorOperation.code_embed (op : GeneratorOperation R)
    (caller : L → CounterInstr R L) (buf tmp : R) (stop l : L) :
    op.code caller buf tmp stop (op.embed l) = (caller l).relabel op.embed := by
  cases op with
  | affine a =>
      change ((caller l).relabel Sum.inr).relabel Sum.inr = _
      exact CounterInstr.relabel_comp Sum.inr Sum.inr (caller l)
  | product p =>
      change ((caller l).relabel Sum.inr).relabel Sum.inr = _
      exact CounterInstr.relabel_comp Sum.inr Sum.inr (caller l)

theorem GeneratorOperation.run (op : GeneratorOperation R) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop : L) (hv : op.Valid buf tmp) (hbt : buf ≠ tmp)
    (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) :
    CounterRun (op.code caller buf tmp stop) ⟨some (op.entry stop), cs, ys⟩ (op.steps cs)
      ⟨some (op.embed stop), op.apply cs, ys⟩ := by
  cases op with
  | affine a => exact a.run caller tmp stop hv.1 cs ht ys
  | product p =>
      rcases hv with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩
      exact preservedProductCode_run_preserved caller p.left p.right p.target buf tmp stop
        h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ hbt cs hb ht ys

theorem GeneratorOperation.apply_buffer (op : GeneratorOperation R) (buf tmp : R)
    (hv : op.Valid buf tmp) (cs : R → Nat) : op.apply cs buf = cs buf := by
  cases op with
  | affine a => simp [GeneratorOperation.apply, AffineAtom.apply, Ne.symm hv.2]
  | product p => simp [GeneratorOperation.apply, Ne.symm hv.2.2.2.2.2.2.2.1]

theorem GeneratorOperation.apply_scratch (op : GeneratorOperation R) (buf tmp : R)
    (hv : op.Valid buf tmp) (cs : R → Nat) : op.apply cs tmp = cs tmp := by
  cases op with
  | affine a => exact a.apply_scratch tmp hv.1 cs
  | product p => simp [GeneratorOperation.apply, Ne.symm hv.2.2.2.2.2.2.2.2]

def GeneratorOperationLabels : List (GeneratorOperation R) → Type → Type
  | [], L => L
  | op :: ops, L => op.Label (GeneratorOperationLabels ops L)

def operationEntry (ops : List (GeneratorOperation R)) (stop : L) : GeneratorOperationLabels ops L :=
  match ops with
  | [] => stop
  | op :: ops => op.entry (operationEntry ops stop)

def operationExit (ops : List (GeneratorOperation R)) (stop : L) : GeneratorOperationLabels ops L :=
  match ops with
  | [] => stop
  | op :: ops => op.embed (operationExit ops stop)

def operationCode (ops : List (GeneratorOperation R)) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop : L) : GeneratorOperationLabels ops L → CounterInstr R (GeneratorOperationLabels ops L) :=
  match ops with
  | [] => caller
  | op :: ops => op.code (operationCode ops caller buf tmp stop) buf tmp (operationEntry ops stop)


theorem operationCode_embed (ops : List (GeneratorOperation R)) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop l : L) :
    operationCode ops caller buf tmp stop (operationExit ops l) =
      (caller l).relabel (operationExit ops) := by
  induction ops with
  | nil =>
      change caller l = (caller l).relabel (fun l => l)
      cases caller l <;> rfl
  | cons op ops ih =>
      rw [operationCode, operationExit, op.code_embed, ih]
      exact CounterInstr.relabel_comp (operationExit ops) op.embed (caller l)

def operationResult (ops : List (GeneratorOperation R)) (cs : R → Nat) : R → Nat :=
  match ops with
  | [] => cs
  | op :: ops => operationResult ops (op.apply cs)

def operationSteps (ops : List (GeneratorOperation R)) (cs : R → Nat) : Nat :=
  match ops with
  | [] => 0
  | op :: ops => op.steps cs + operationSteps ops (op.apply cs)

/-- Mixed scalar arithmetic is one fixed finite graph, not a primitive evaluator. -/
theorem operationCode_run (ops : List (GeneratorOperation R)) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop : L) (hv : ∀ op ∈ ops, op.Valid buf tmp) (hbt : buf ≠ tmp)
    (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) :
    CounterRun (operationCode ops caller buf tmp stop)
      ⟨some (operationEntry ops stop), cs, ys⟩ (operationSteps ops cs)
      ⟨some (operationExit ops stop), operationResult ops cs, ys⟩ := by
  induction ops generalizing cs with
  | nil => exact CounterRun.refl _
  | cons op ops ih =>
      let inner := operationCode ops caller buf tmp stop
      let prg := operationCode (op :: ops) caller buf tmp stop
      have h₁ := op.run inner buf tmp (operationEntry ops stop) (hv op (by simp)) hbt cs hb ht ys
      have h₂ := ih (fun x hx => hv x (by simp [hx])) (op.apply cs)
        (by rw [op.apply_buffer buf tmp (hv op (by simp))]; exact hb)
        (by rw [op.apply_scratch buf tmp (hv op (by simp))]; exact ht)
      have h₃ := CounterRun.relabel inner prg op.embed (op.code_embed inner buf tmp (operationEntry ops stop)) h₂
      change CounterRun prg ⟨some (op.embed (operationEntry ops stop)), op.apply cs, ys⟩
        (operationSteps ops (op.apply cs))
        ⟨some (op.embed (operationExit ops stop)), operationResult ops (op.apply cs), ys⟩ at h₃
      have h := CounterRun.trans prg h₁ h₃
      convert h using 1 <;> (try simp [prg, operationEntry, operationExit, operationSteps,
        operationResult]) <;> rfl

noncomputable instance operationLabelsFintype (ops : List (GeneratorOperation R)) [Fintype L] :
    Fintype (GeneratorOperationLabels ops L) := by
  induction ops with
  | nil => exact inferInstanceAs (Fintype L)
  | cons op ops ih =>
      letI := ih
      cases op with
      | affine a => exact inferInstanceAs (Fintype (AffineLabel a.offset a.coefficient (GeneratorOperationLabels ops L)))
      | product p => exact inferInstanceAs (Fintype (PreservedProductLabel (GeneratorOperationLabels ops L)))

noncomputable def GeneratorOperation.applyPolynomial (op : GeneratorOperation R)
    (sizes : R → Polynomial Nat) : R → Polynomial Nat :=
  match op with
  | .affine a => a.applyPolynomial sizes
  | .product p => Function.update sizes p.target (sizes p.target + sizes p.left * sizes p.right)

noncomputable def GeneratorOperation.clock (op : GeneratorOperation R) (sizes : R → Polynomial Nat) : Polynomial Nat :=
  match op with
  | .affine a => Polynomial.C a.coefficient * (Polynomial.C 7 * sizes a.source + Polynomial.C 2) + Polynomial.C a.offset
  | .product p => (Polynomial.C 7 * sizes p.left + Polynomial.C 2) +
      (sizes p.left * (Polynomial.C 7 * sizes p.right + Polynomial.C 4) + Polynomial.C 1)

theorem GeneratorOperation.applyPolynomial_eval (op : GeneratorOperation R) (sizes : R → Polynomial Nat) (n : Nat) :
    (fun r => (op.applyPolynomial sizes r).eval n) = op.apply (fun r => (sizes r).eval n) := by
  cases op with
  | affine a => exact a.applyPolynomial_eval sizes n
  | product p =>
      funext r
      by_cases h : r = p.target <;> simp [GeneratorOperation.applyPolynomial, GeneratorOperation.apply, h]

theorem GeneratorOperation.clock_eval (op : GeneratorOperation R) (sizes : R → Polynomial Nat) (n : Nat) :
    (op.clock sizes).eval n = op.steps (fun r => (sizes r).eval n) := by
  cases op <;> simp [GeneratorOperation.clock, GeneratorOperation.steps, AffineAtom.steps]

noncomputable def operationClock (ops : List (GeneratorOperation R)) (sizes : R → Polynomial Nat) : Polynomial Nat :=
  match ops with
  | [] => 0
  | op :: ops => op.clock sizes + operationClock ops (op.applyPolynomial sizes)

theorem operationClock_eval (ops : List (GeneratorOperation R)) (sizes : R → Polynomial Nat) (n : Nat) :
    (operationClock ops sizes).eval n = operationSteps ops (fun r => (sizes r).eval n) := by
  induction ops generalizing sizes with
  | nil => simp [operationClock, operationSteps]
  | cons op ops ih =>
      simp only [operationClock, Polynomial.eval_add, operationSteps, GeneratorOperation.clock_eval,
        ih, GeneratorOperation.applyPolynomial_eval]

end ShiReversibleGenerator
