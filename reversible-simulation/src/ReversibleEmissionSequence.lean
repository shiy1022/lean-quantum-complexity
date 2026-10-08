import ReversibleWireEmission

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

@[simp] theorem CounterCfg.relabel_some {L' : Type} (f : L → L')
    (pc : L) (cs : R → Nat) (ys : List Bool) :
    (⟨some pc, cs, ys⟩ : CounterCfg R L).relabel f = ⟨some (f pc), cs, ys⟩ := rfl

/-- A fixed printing template; only natural fields read runtime counters. -/
inductive EmissionAtom (R : Type) where
  | literal : List Bool → EmissionAtom R
  | natural : R → EmissionAtom R

def EmissionAtom.Label (a : EmissionAtom R) (L : Type) : Type :=
  match a with
  | .literal bits => LiteralLabel bits L
  | .natural _ => NatEmissionLabel L

def EmissionAtom.embed (a : EmissionAtom R) (l : L) : a.Label L :=
  match a with
  | .literal _ => .inr l
  | .natural _ => .inr (.inr l)

def EmissionAtom.entry (a : EmissionAtom R) (stop : L) : a.Label L :=
  match a with
  | .literal bits => literalPointer bits stop 0
  | .natural _ => .inl 0

def EmissionAtom.code (a : EmissionAtom R) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop : L) : a.Label L → CounterInstr R (a.Label L) :=
  match a with
  | .literal bits => literalCode bits caller stop
  | .natural r => natEmissionCode caller r buf tmp stop

def EmissionAtom.bytes (a : EmissionAtom R) (cs : R → Nat) : List Bool :=
  match a with
  | .literal bits => bits
  | .natural r => ShiBQP.encNat (cs r)

def EmissionAtom.steps (a : EmissionAtom R) (cs : R → Nat) : Nat :=
  match a with
  | .literal bits => bits.length
  | .natural r => 10 * cs r + 4

def EmissionAtom.Valid (a : EmissionAtom R) (buf tmp : R) : Prop :=
  match a with
  | .literal _ => True
  | .natural r => r ≠ buf ∧ r ≠ tmp

theorem EmissionAtom.code_embed (a : EmissionAtom R) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop l : L) :
    a.code caller buf tmp stop (a.embed l) = (caller l).relabel a.embed := by
  cases a <;> rfl

theorem EmissionAtom.run (a : EmissionAtom R) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop : L) (ha : a.Valid buf tmp) (hbt : buf ≠ tmp)
    (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) :
    CounterRun (a.code caller buf tmp stop) ⟨some (a.entry stop), cs, ys⟩ (a.steps cs)
      ⟨some (a.embed stop), cs, a.bytes cs ++ ys⟩ := by
  cases a with
  | literal bits => exact literalCode_run bits caller stop cs ys
  | natural r => exact natEmissionCode_run_preserved caller r buf tmp stop ha.1 ha.2 hbt cs hb ht ys

/-- The control type depends only on the fixed template, not on input length. -/
def EmissionLabels : List (EmissionAtom R) → Type → Type
  | [], L => L
  | a :: atoms, L => a.Label (EmissionLabels atoms L)

def emissionEntry (atoms : List (EmissionAtom R)) (stop : L) : EmissionLabels atoms L :=
  match atoms with
  | [] => stop
  | a :: atoms => a.entry (emissionEntry atoms stop)

def emissionExit (atoms : List (EmissionAtom R)) (stop : L) : EmissionLabels atoms L :=
  match atoms with
  | [] => stop
  | a :: atoms => a.embed (emissionExit atoms stop)

def emissionCode (atoms : List (EmissionAtom R)) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop : L) : EmissionLabels atoms L → CounterInstr R (EmissionLabels atoms L) :=
  match atoms with
  | [] => caller
  | a :: atoms => a.code (emissionCode atoms caller buf tmp stop) buf tmp (emissionEntry atoms stop)

def emissionBytes (atoms : List (EmissionAtom R)) (cs : R → Nat) : List Bool :=
  match atoms with
  | [] => []
  | a :: atoms => emissionBytes atoms cs ++ a.bytes cs

def emissionSteps (atoms : List (EmissionAtom R)) (cs : R → Nat) : Nat :=
  match atoms with
  | [] => 0
  | a :: atoms => a.steps cs + emissionSteps atoms cs

/-- Concatenate fixed templates without a composition axiom or an uncounted step. -/
theorem emissionCode_run (atoms : List (EmissionAtom R)) (caller : L → CounterInstr R L)
    (buf tmp : R) (stop : L) (ha : ∀ a ∈ atoms, a.Valid buf tmp) (hbt : buf ≠ tmp)
    (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) :
    CounterRun (emissionCode atoms caller buf tmp stop)
      ⟨some (emissionEntry atoms stop), cs, ys⟩ (emissionSteps atoms cs)
      ⟨some (emissionExit atoms stop), cs, emissionBytes atoms cs ++ ys⟩ := by
  induction atoms generalizing ys with
  | nil => exact CounterRun.refl _
  | cons a atoms ih =>
      let inner := emissionCode atoms caller buf tmp stop
      let prg := emissionCode (a :: atoms) caller buf tmp stop
      have h₁ := a.run inner buf tmp (emissionEntry atoms stop) (ha a (by simp)) hbt cs hb ht ys
      have h₂ := ih (fun b h => ha b (by simp [h])) (a.bytes cs ++ ys)
      have h₃ := CounterRun.relabel inner prg a.embed
        (a.code_embed inner buf tmp (emissionEntry atoms stop)) h₂
      change CounterRun prg
        ⟨some (a.embed (emissionEntry atoms stop)), cs, a.bytes cs ++ ys⟩
        (emissionSteps atoms cs)
        ⟨some (a.embed (emissionExit atoms stop)), cs, emissionBytes atoms cs ++ (a.bytes cs ++ ys)⟩ at h₃
      have h := CounterRun.trans prg h₁ h₃
      convert h using 1 <;> (try simp [prg, emissionEntry, emissionExit, emissionSteps, emissionBytes, List.append_assoc]) <;> rfl

/-- Explicit finite control exists for every fixed template and finite caller. -/
noncomputable instance emissionLabelsFintype (atoms : List (EmissionAtom R)) [Fintype L] :
    Fintype (EmissionLabels atoms L) := by
  induction atoms with
  | nil => exact inferInstanceAs (Fintype L)
  | cons a atoms ih =>
      letI := ih
      cases a with
      | literal bits => exact inferInstanceAs (Fintype (LiteralLabel bits (EmissionLabels atoms L)))
      | natural r => exact inferInstanceAs (Fintype (NatEmissionLabel (EmissionLabels atoms L)))

/-- Polynomial clock for the entire fixed template, including every literal bit. -/
noncomputable def emissionClock (atoms : List (EmissionAtom R)) (sizes : R → Polynomial Nat) :
    Polynomial Nat :=
  match atoms with
  | [] => 0
  | .literal bits :: atoms => Polynomial.C bits.length + emissionClock atoms sizes
  | .natural r :: atoms => Polynomial.C 10 * sizes r + Polynomial.C 4 + emissionClock atoms sizes

theorem emissionClock_eval (atoms : List (EmissionAtom R)) (sizes : R → Polynomial Nat) (n : Nat) :
    (emissionClock atoms sizes).eval n = emissionSteps atoms (fun r => (sizes r).eval n) := by
  induction atoms with
  | nil => simp [emissionClock, emissionSteps]
  | cons a atoms ih => cases a <;> simp [emissionClock, emissionSteps, EmissionAtom.steps, ih]

end ShiReversibleGenerator
