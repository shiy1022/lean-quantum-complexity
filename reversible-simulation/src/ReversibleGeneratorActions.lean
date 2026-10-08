import ReversibleMixedArithmetic
import ReversibleEmissionSequence

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

/-- A fixed circuit-printing template can calculate addresses and then emit fields. -/
inductive GeneratorAction (R : Type) where
  | arithmetic : GeneratorOperation R → GeneratorAction R
  | emit : EmissionAtom R → GeneratorAction R

def GeneratorAction.Label (a : GeneratorAction R) (L : Type) : Type :=
  match a with
  | .arithmetic op => op.Label L
  | .emit atom => atom.Label L

def GeneratorAction.embed (a : GeneratorAction R) (l : L) : a.Label L :=
  match a with
  | .arithmetic op => op.embed l
  | .emit atom => atom.embed l

def GeneratorAction.entry (a : GeneratorAction R) (stop : L) : a.Label L :=
  match a with
  | .arithmetic op => op.entry stop
  | .emit atom => atom.entry stop

def GeneratorAction.code (a : GeneratorAction R) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop : L) : a.Label L → CounterInstr R (a.Label L) :=
  match a with
  | .arithmetic op => op.code caller buf tmp stop
  | .emit atom => atom.code caller buf tmp stop

def GeneratorAction.counters (a : GeneratorAction R) (cs : R → Nat) : R → Nat :=
  match a with
  | .arithmetic op => op.apply cs
  | .emit _ => cs

def GeneratorAction.bytes (a : GeneratorAction R) (cs : R → Nat) : List Bool :=
  match a with
  | .arithmetic _ => []
  | .emit atom => atom.bytes cs

def GeneratorAction.steps (a : GeneratorAction R) (cs : R → Nat) : Nat :=
  match a with
  | .arithmetic op => op.steps cs
  | .emit atom => atom.steps cs

def GeneratorAction.Valid (a : GeneratorAction R) (buf tmp : R) : Prop :=
  match a with
  | .arithmetic op => op.Valid buf tmp
  | .emit atom => atom.Valid buf tmp

theorem GeneratorAction.code_embed (a : GeneratorAction R) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop l : L) :
    a.code caller buf tmp stop (a.embed l) = (caller l).relabel a.embed := by
  cases a with
  | arithmetic op => exact op.code_embed caller buf tmp stop l
  | emit atom => exact atom.code_embed caller buf tmp stop l

theorem GeneratorAction.run (a : GeneratorAction R) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop : L) (hv : a.Valid buf tmp) (hbt : buf ≠ tmp)
    (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) :
    CounterRun (a.code caller buf tmp stop) ⟨some (a.entry stop), cs, ys⟩ (a.steps cs)
      ⟨some (a.embed stop), a.counters cs, a.bytes cs ++ ys⟩ := by
  cases a with
  | arithmetic op => simpa [Label, code, entry, embed, counters, bytes, steps] using op.run caller buf tmp stop hv hbt cs hb ht ys
  | emit atom => exact atom.run caller buf tmp stop hv hbt cs hb ht ys

theorem GeneratorAction.counters_buffer (a : GeneratorAction R) (buf tmp : R)
    (hv : a.Valid buf tmp) (cs : R → Nat) : a.counters cs buf = cs buf := by
  cases a with
  | arithmetic op => exact op.apply_buffer buf tmp hv cs
  | emit atom => rfl

theorem GeneratorAction.counters_scratch (a : GeneratorAction R) (buf tmp : R)
    (hv : a.Valid buf tmp) (cs : R → Nat) : a.counters cs tmp = cs tmp := by
  cases a with
  | arithmetic op => exact op.apply_scratch buf tmp hv cs
  | emit atom => rfl

def GeneratorActionLabels : List (GeneratorAction R) → Type → Type
  | [], L => L
  | a :: actions, L => a.Label (GeneratorActionLabels actions L)

def actionEntry (actions : List (GeneratorAction R)) (stop : L) : GeneratorActionLabels actions L :=
  match actions with
  | [] => stop
  | a :: actions => a.entry (actionEntry actions stop)

def actionExit (actions : List (GeneratorAction R)) (stop : L) : GeneratorActionLabels actions L :=
  match actions with
  | [] => stop
  | a :: actions => a.embed (actionExit actions stop)

def actionCode (actions : List (GeneratorAction R)) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop : L) : GeneratorActionLabels actions L → CounterInstr R (GeneratorActionLabels actions L) :=
  match actions with
  | [] => caller
  | a :: actions => a.code (actionCode actions caller buf tmp stop) buf tmp (actionEntry actions stop)

theorem actionCode_embed (actions : List (GeneratorAction R)) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop l : L) :
    actionCode actions caller buf tmp stop (actionExit actions l) =
      (caller l).relabel (actionExit actions) := by
  induction actions with
  | nil => change caller l = (caller l).relabel (fun l => l); cases caller l <;> rfl
  | cons a actions ih =>
      rw [actionCode, actionExit, a.code_embed, ih]
      exact CounterInstr.relabel_comp (actionExit actions) a.embed (caller l)

def actionCounters (actions : List (GeneratorAction R)) (cs : R → Nat) : R → Nat :=
  match actions with
  | [] => cs
  | a :: actions => actionCounters actions (a.counters cs)

def actionBytes (actions : List (GeneratorAction R)) (cs : R → Nat) : List Bool :=
  match actions with
  | [] => []
  | a :: actions => actionBytes actions (a.counters cs) ++ a.bytes cs

def actionSteps (actions : List (GeneratorAction R)) (cs : R → Nat) : Nat :=
  match actions with
  | [] => 0
  | a :: actions => a.steps cs + actionSteps actions (a.counters cs)

/-- One finite graph with exact bytes, updated register values and all instruction costs. -/
theorem actionCode_run (actions : List (GeneratorAction R)) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop : L) (hv : ∀ a ∈ actions, a.Valid buf tmp) (hbt : buf ≠ tmp)
    (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) :
    CounterRun (actionCode actions caller buf tmp stop)
      ⟨some (actionEntry actions stop), cs, ys⟩ (actionSteps actions cs)
      ⟨some (actionExit actions stop), actionCounters actions cs, actionBytes actions cs ++ ys⟩ := by
  induction actions generalizing cs ys with
  | nil => exact CounterRun.refl _
  | cons a actions ih =>
      let inner := actionCode actions caller buf tmp stop
      let prg := actionCode (a :: actions) caller buf tmp stop
      have h₁ := a.run inner buf tmp (actionEntry actions stop) (hv a (by simp)) hbt cs hb ht ys
      have h₂ := ih (fun b h => hv b (by simp [h])) (a.counters cs)
        (by rw [a.counters_buffer buf tmp (hv a (by simp))]; exact hb)
        (by rw [a.counters_scratch buf tmp (hv a (by simp))]; exact ht) (a.bytes cs ++ ys)
      have h₃ := CounterRun.relabel inner prg a.embed (a.code_embed inner buf tmp (actionEntry actions stop)) h₂
      change CounterRun prg ⟨some (a.embed (actionEntry actions stop)), a.counters cs, a.bytes cs ++ ys⟩
        (actionSteps actions (a.counters cs))
        ⟨some (a.embed (actionExit actions stop)), actionCounters actions (a.counters cs),
          actionBytes actions (a.counters cs) ++ (a.bytes cs ++ ys)⟩ at h₃
      have h := CounterRun.trans prg h₁ h₃
      convert h using 1 <;> (try simp [prg, actionEntry, actionExit, actionSteps,
        actionCounters, actionBytes, List.append_assoc]) <;> rfl

noncomputable instance actionLabelsFintype (actions : List (GeneratorAction R)) [Fintype L] :
    Fintype (GeneratorActionLabels actions L) := by
  induction actions with
  | nil => exact inferInstanceAs (Fintype L)
  | cons a actions ih =>
      letI := ih
      cases a with
      | arithmetic op => cases op with
        | affine atom => exact inferInstanceAs (Fintype (AffineLabel atom.offset atom.coefficient (GeneratorActionLabels actions L)))
        | product atom => exact inferInstanceAs (Fintype (PreservedProductLabel (GeneratorActionLabels actions L)))
      | emit atom => cases atom with
        | literal bits => exact inferInstanceAs (Fintype (LiteralLabel bits (GeneratorActionLabels actions L)))
        | natural r => exact inferInstanceAs (Fintype (NatEmissionLabel (GeneratorActionLabels actions L)))

noncomputable def GeneratorAction.countersPolynomial (a : GeneratorAction R)
    (sizes : R → Polynomial Nat) : R → Polynomial Nat :=
  match a with
  | .arithmetic op => op.applyPolynomial sizes
  | .emit _ => sizes

noncomputable def GeneratorAction.clock (a : GeneratorAction R)
    (sizes : R → Polynomial Nat) : Polynomial Nat :=
  match a with
  | .arithmetic op => op.clock sizes
  | .emit (.literal bits) => Polynomial.C bits.length
  | .emit (.natural r) => Polynomial.C 10 * sizes r + Polynomial.C 4

theorem GeneratorAction.countersPolynomial_eval (a : GeneratorAction R)
    (sizes : R → Polynomial Nat) (n : Nat) :
    (fun r => (a.countersPolynomial sizes r).eval n) = a.counters (fun r => (sizes r).eval n) := by
  cases a with
  | arithmetic op => exact op.applyPolynomial_eval sizes n
  | emit atom => rfl

theorem GeneratorAction.clock_eval (a : GeneratorAction R)
    (sizes : R → Polynomial Nat) (n : Nat) :
    (a.clock sizes).eval n = a.steps (fun r => (sizes r).eval n) := by
  cases a with
  | arithmetic op => exact op.clock_eval sizes n
  | emit atom => cases atom <;> simp [clock, steps, EmissionAtom.steps]

noncomputable def actionClock (actions : List (GeneratorAction R))
    (sizes : R → Polynomial Nat) : Polynomial Nat :=
  match actions with
  | [] => 0
  | a :: actions => a.clock sizes + actionClock actions (a.countersPolynomial sizes)

theorem actionClock_eval (actions : List (GeneratorAction R))
    (sizes : R → Polynomial Nat) (n : Nat) :
    (actionClock actions sizes).eval n = actionSteps actions (fun r => (sizes r).eval n) := by
  induction actions generalizing sizes with
  | nil => simp [actionClock, actionSteps]
  | cons a actions ih =>
      simp only [actionClock, Polynomial.eval_add, GeneratorAction.clock_eval, ih,
        GeneratorAction.countersPolynomial_eval, actionSteps]

noncomputable def actionResultPolynomial (actions : List (GeneratorAction R))
    (sizes : R → Polynomial Nat) : R → Polynomial Nat :=
  match actions with
  | [] => sizes
  | a :: actions => actionResultPolynomial actions (a.countersPolynomial sizes)

theorem actionResultPolynomial_eval (actions : List (GeneratorAction R))
    (sizes : R → Polynomial Nat) (n : Nat) :
    (fun r => (actionResultPolynomial actions sizes r).eval n) =
      actionCounters actions (fun r => (sizes r).eval n) := by
  induction actions generalizing sizes with
  | nil => rfl
  | cons a actions ih =>
      simp only [actionResultPolynomial, ih, GeneratorAction.countersPolynomial_eval, actionCounters]

end ShiReversibleGenerator
