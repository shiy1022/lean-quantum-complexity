import ReversibleRawBridge

set_option autoImplicit false

namespace ShiReversibleFormula

variable {ι : Type}

def forestSize : List (Formula ι) → Nat
  | [] => 0
  | p :: ps => p.size + forestSize ps

def forestCompile (inputs : ι → Nat) (base : Nat) : List (Formula ι) → List RawAssignment
  | [] => []
  | p :: ps => p.rawCompile inputs base ++ forestCompile inputs (base + p.size) ps

def forestResult (base : Nat) : List (Formula ι) → Nat → Nat
  | [], _ => base
  | p :: _, 0 => p.result base
  | p :: ps, i + 1 => forestResult (base + p.size) ps i

@[simp] theorem forestCompile_length (ps : List (Formula ι)) (inputs : ι → Nat) (base : Nat) :
    (forestCompile inputs base ps).length = forestSize ps := by
  induction ps generalizing base with
  | nil => rfl
  | cons p ps ih => simp [forestCompile, forestSize, ih]

theorem forestCompile_targets (ps : List (Formula ι)) (inputs : ι → Nat) (base : Nat) :
    (forestCompile inputs base ps).map RawAssignment.target = List.range' base (forestSize ps) := by
  induction ps generalizing base with
  | nil => rfl
  | cons p ps ih =>
    simp [forestCompile, forestSize, p.rawCompile_targets, ih]

theorem forestCompile_target_interval (ps : List (Formula ι)) (inputs : ι → Nat)
    (base : Nat) (a : RawAssignment) (ha : a ∈ forestCompile inputs base ps) :
    base ≤ a.target ∧ a.target < base + forestSize ps := by
  have ht : a.target ∈ List.range' base (forestSize ps) := by
    rw [← forestCompile_targets ps inputs base]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨j, hj, he⟩ := List.mem_range'.mp ht
  simp only [Nat.one_mul] at he
  omega

theorem forestCompile_topological (ps : List (Formula ι)) (inputs : ι → Nat)
    (base : Nat) (hin : ∀ i, inputs i < base) :
    ∀ a ∈ forestCompile inputs base ps, a.Topological := by
  induction ps generalizing base with
  | nil => simp [forestCompile]
  | cons p ps ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact p.rawCompile_topological inputs base hin a ha
    · exact ih (base + p.size) (fun i => (hin i).trans_le (by omega)) a ha

theorem forestCompile_preserves (ps : List (Formula ι)) (inputs : ι → Nat)
    (base : Nat) (s : Nat → Bool) (i : Nat) (hi : i < base) :
    rawRun (forestCompile inputs base ps) s i = s i := by
  apply rawRun_preserves
  intro a ha he
  have ht := (forestCompile_target_interval ps inputs base a ha).1
  omega

theorem forestResult_bound (ps : List (Formula ι)) (base i : Nat) (hi : i < ps.length) :
    base ≤ forestResult base ps i ∧ forestResult base ps i < base + forestSize ps := by
  induction ps generalizing base i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero =>
      have hp := p.size_pos
      simp only [forestResult, Formula.result, forestSize]
      omega
    | succ i =>
      have hit : i < ps.length := by simpa using hi
      have ht := ih (base + p.size) i hit
      simp only [forestResult, forestSize]
      omega

/-- Each output gets a disjoint fresh block; no previously computed output is overwritten. -/
theorem forestCompile_correct (ps : List (Formula ι)) (inputs : ι → Nat)
    (base : Nat) (s : Nat → Bool) (hin : ∀ i, inputs i < base)
    (i : Nat) (hi : i < ps.length) :
    rawRun (forestCompile inputs base ps) s (forestResult base ps i) =
      (ps[i]).eval (fun j => s (inputs j)) := by
  induction ps generalizing base s i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero =>
      have hp := p.size_pos
      have hkeep := forestCompile_preserves ps inputs (base + p.size)
        (rawRun (p.rawCompile inputs base) s) (p.result base) (by
          simp only [Formula.result]
          omega)
      simp only [forestCompile, rawRun_append, forestResult, List.getElem_cons_zero]
      rw [hkeep, p.rawCompile_correct inputs base s hin]
    | succ i =>
      have hit : i < ps.length := by simpa using hi
      have hin' : ∀ j, inputs j < base + p.size := fun j => (hin j).trans_le (by omega)
      have hkeep : (fun j => rawRun (p.rawCompile inputs base) s (inputs j)) =
          (fun j => s (inputs j)) := by
        funext j
        exact p.rawCompile_preserves inputs base s (inputs j) (hin j)
      have hr := ih (base + p.size) (rawRun (p.rawCompile inputs base) s) hin' i hit
      rw [hkeep] at hr
      simpa only [forestCompile, rawRun_append, forestResult, List.getElem_cons_succ] using hr

theorem forestSize_bound (ps : List (Formula ι)) (bound : Nat)
    (h : ∀ p ∈ ps, p.size ≤ bound) : forestSize ps ≤ ps.length * bound := by
  induction ps with
  | nil => simp [forestSize]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht := ih (fun q hq => h q (by simp [hq]))
    simp only [forestSize, List.length_cons, Nat.succ_mul]
    omega

end ShiReversibleFormula
