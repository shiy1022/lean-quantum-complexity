import ReversibleForestCircuit

set_option autoImplicit false
namespace ShiReversibleFormula
open ShiReversible

variable {n : Nat}

def forestStep (ps : List (Formula (Fin n))) (hl : ps.length = n) (x : Bits n) : Bits n :=
  fun i => (ps[i.val]'(by simpa [hl] using i.isLt)).eval x

def forestAdvance (ps : List (Formula (Fin n))) (hl : ps.length = n) : Nat → Bits n → Bits n
  | 0, x => x
  | t + 1, x => forestAdvance ps hl t (forestStep ps hl x)

/-- Successive steps share references to the previous configuration instead of substituting formulas. -/
def iterationCompile (ps : List (Formula (Fin n))) (hl : ps.length = n) :
    Nat → (Fin n → Nat) → Nat → List RawAssignment
  | 0, _, _ => []
  | t + 1, inputs, base => forestCompile inputs base ps ++
      iterationCompile ps hl t (fun i => forestResult base ps i.val) (base + forestSize ps)

def iterationRead (ps : List (Formula (Fin n))) (hl : ps.length = n) :
    Nat → (Fin n → Nat) → Nat → Fin n → Nat
  | 0, inputs, _ => inputs
  | t + 1, _, base => iterationRead ps hl t
      (fun i => forestResult base ps i.val) (base + forestSize ps)

@[simp] theorem iterationCompile_length (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (t : Nat) (inputs : Fin n → Nat) (base : Nat) :
    (iterationCompile ps hl t inputs base).length = t * forestSize ps := by
  induction t generalizing inputs base with
  | zero => simp [iterationCompile]
  | succ t ih => simp [iterationCompile, ih, Nat.succ_mul, Nat.add_comm]

theorem iterationCompile_targets (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (t : Nat) (inputs : Fin n → Nat) (base : Nat) :
    (iterationCompile ps hl t inputs base).map RawAssignment.target = List.range' base (t * forestSize ps) := by
  induction t generalizing inputs base with
  | zero => simp [iterationCompile]
  | succ t ih => simp [iterationCompile, forestCompile_targets, ih, Nat.succ_mul, Nat.add_comm]

theorem iterationCompile_topological (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (t : Nat) (inputs : Fin n → Nat) (base : Nat) (hin : ∀ i, inputs i < base) :
    ∀ a ∈ iterationCompile ps hl t inputs base, a.Topological := by
  induction t generalizing inputs base with
  | zero => simp [iterationCompile]
  | succ t ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact forestCompile_topological ps inputs base hin a ha
    · exact ih _ _ (fun i => (forestResult_bound ps base i.val (by simpa [hl] using i.isLt)).2) a ha

theorem iterationRead_bound (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (t : Nat) (inputs : Fin n → Nat) (base : Nat) (hin : ∀ i, inputs i < base) (i : Fin n) :
    iterationRead ps hl t inputs base i < base + t * forestSize ps := by
  induction t generalizing inputs base with
  | zero => simpa [iterationRead] using hin i
  | succ t ih =>
    have h := ih (fun j => forestResult base ps j.val) (base + forestSize ps)
      (fun j => (forestResult_bound ps base j.val (by simpa [hl] using j.isLt)).2)
    simpa [iterationRead, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Every time slice is compiled exactly once, and its output references feed the next slice. -/
theorem iterationCompile_correct (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (t : Nat) (inputs : Fin n → Nat) (base : Nat) (s : Nat → Bool)
    (hin : ∀ i, inputs i < base) (i : Fin n) :
    rawRun (iterationCompile ps hl t inputs base) s (iterationRead ps hl t inputs base i) =
      forestAdvance ps hl t (fun j => s (inputs j)) i := by
  induction t generalizing inputs base s with
  | zero => rfl
  | succ t ih =>
    simp only [iterationCompile, rawRun_append, iterationRead, forestAdvance]
    rw [ih _ _ _ (fun j => (forestResult_bound ps base j.val (by simpa [hl] using j.isLt)).2)]
    have he : (fun j : Fin n => rawRun (forestCompile inputs base ps) s (forestResult base ps j.val)) =
        forestStep ps hl (fun j => s (inputs j)) := by
      funext j
      exact forestCompile_correct ps inputs base s hin j.val (by simpa [hl] using j.isLt)
    rw [he]

end ShiReversibleFormula
