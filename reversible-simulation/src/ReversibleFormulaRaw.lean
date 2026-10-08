import ReversibleBooleanFormula
import ReversibleBoolean
import Mathlib.Data.List.Range

set_option autoImplicit false

namespace ShiReversibleFormula

/-- Concrete Boolean nodes with natural-number wire addresses. -/
inductive RawAssignment where
  | constant (target : Nat) (value : Bool)
  | copy (source target : Nat)
  | neg (source target : Nat)
  | conj (left right target : Nat)

def RawAssignment.target : RawAssignment → Nat
  | .constant t _ | .copy _ t | .neg _ t | .conj _ _ t => t

def RawAssignment.value (s : Nat → Bool) : RawAssignment → Bool
  | .constant _ b => b
  | .copy r _ => s r
  | .neg r _ => !(s r)
  | .conj a b _ => s a && s b

def RawAssignment.eval (a : RawAssignment) (s : Nat → Bool) : Nat → Bool :=
  Function.update s a.target (a.value s)

def rawRun (nodes : List RawAssignment) (s : Nat → Bool) : Nat → Bool :=
  nodes.foldl (fun s a => a.eval s) s

@[simp] theorem rawRun_single_target (a : RawAssignment) (s : Nat → Bool) :
    rawRun [a] s a.target = a.value s := by
  simp [rawRun, RawAssignment.eval]

@[simp] theorem rawRun_append (p q : List RawAssignment) (s : Nat → Bool) :
    rawRun (p ++ q) s = rawRun q (rawRun p s) := by
  simp [rawRun, List.foldl_append]

/-- Every read is from an earlier wire than the fresh target. -/
def RawAssignment.Topological : RawAssignment → Prop
  | .constant _ _ => True
  | .copy r t | .neg r t => r < t
  | .conj a b t => a < t ∧ b < t

theorem Formula.size_pos {ι : Type} (p : Formula ι) : 0 < p.size := by
  cases p <;> simp [Formula.size] <;> omega

def Formula.result {ι : Type} (p : Formula ι) (base : Nat) : Nat := base + p.size - 1

/-- One fresh postorder node for every constructor; no truth-table enumeration. -/
def Formula.rawCompile {ι : Type} (inputs : ι → Nat) (base : Nat) : Formula ι → List RawAssignment
  | .constant b => [.constant base b]
  | .input i => [.copy (inputs i) base]
  | .neg p => p.rawCompile inputs base ++ [.neg (p.result base) (base + p.size)]
  | .conj p q => p.rawCompile inputs base ++ q.rawCompile inputs (base + p.size) ++
      [.conj (p.result base) (q.result (base + p.size)) (base + p.size + q.size)]

@[simp] theorem Formula.rawCompile_length {ι : Type} (p : Formula ι)
    (inputs : ι → Nat) (base : Nat) : (p.rawCompile inputs base).length = p.size := by
  induction p generalizing base with
  | constant => rfl
  | input => rfl
  | neg p ih => simp [Formula.rawCompile, Formula.size, ih]
  | conj p q ihp ihq => simp [Formula.rawCompile, Formula.size, ihp, ihq, Nat.add_assoc]

/-- The target addresses are exactly one consecutive fresh interval. -/
theorem Formula.rawCompile_targets {ι : Type} (p : Formula ι)
    (inputs : ι → Nat) (base : Nat) :
    (p.rawCompile inputs base).map RawAssignment.target = List.range' base p.size := by
  induction p generalizing base with
  | constant => simp [Formula.rawCompile, Formula.size, RawAssignment.target]
  | input => simp [Formula.rawCompile, Formula.size, RawAssignment.target]
  | neg p ih =>
    simp only [Formula.rawCompile, List.map_append, List.map_cons, List.map_nil,
      RawAssignment.target, ih, Formula.size]
    simpa using (List.range'_append_1 (s := base) (m := p.size) (n := 1))
  | conj p q ihp ihq =>
    simp only [Formula.rawCompile, List.map_append, List.map_cons, List.map_nil,
      RawAssignment.target, ihp, ihq, Formula.size]
    rw [List.range'_append_1]
    simpa [Nat.add_assoc] using
      (List.range'_append_1 (s := base) (m := p.size + q.size) (n := 1))

theorem Formula.rawCompile_target_interval {ι : Type} (p : Formula ι) (inputs : ι → Nat)
    (base : Nat) (a : RawAssignment) (ha : a ∈ p.rawCompile inputs base) :
    base ≤ a.target ∧ a.target < base + p.size := by
  have ht : a.target ∈ List.range' base p.size := by
    rw [← p.rawCompile_targets inputs base]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨j, hj, he⟩ := List.mem_range'.mp ht
  simp only [Nat.one_mul] at he
  omega

theorem rawRun_preserves (nodes : List RawAssignment) (s : Nat → Bool) (i : Nat)
    (h : ∀ a ∈ nodes, i ≠ a.target) : rawRun nodes s i = s i := by
  induction nodes generalizing s with
  | nil => rfl
  | cons a nodes ih =>
    change rawRun nodes (a.eval s) i = s i
    rw [ih _ (fun b hb => h b (by simp [hb]))]
    simp [RawAssignment.eval, Function.update_of_ne (h a (by simp))]

theorem Formula.rawCompile_preserves {ι : Type} (p : Formula ι) (inputs : ι → Nat)
    (base : Nat) (s : Nat → Bool) (i : Nat) (hi : i < base) :
    rawRun (p.rawCompile inputs base) s i = s i := by
  apply rawRun_preserves
  intro a ha he
  have ht : a.target ∈ List.range' base p.size := by
    rw [← p.rawCompile_targets inputs base]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨j, hj, he⟩ := List.mem_range'.mp ht
  simp only [Nat.one_mul] at he
  omega

theorem Formula.rawCompile_topological {ι : Type} (p : Formula ι) (inputs : ι → Nat)
    (base : Nat) (hin : ∀ i, inputs i < base) :
    ∀ a ∈ p.rawCompile inputs base, a.Topological := by
  induction p generalizing base with
  | constant b => simp [Formula.rawCompile, RawAssignment.Topological]
  | input i => simpa [Formula.rawCompile, RawAssignment.Topological] using hin i
  | neg p ih =>
    intro a ha
    simp only [Formula.rawCompile, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact ih base hin a ha
    · have hp := p.size_pos
      simp only [RawAssignment.Topological, Formula.result]
      omega
  | conj p q ihp ihq =>
    intro a ha
    simp only [Formula.rawCompile, List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact ihp base hin a ha
    · exact ihq (base + p.size) (fun i => (hin i).trans_le (by omega)) a ha
    · have hp := p.size_pos
      have hq := q.size_pos
      simp only [RawAssignment.Topological, Formula.result]
      omega

/-- Exact formula output; the state outside its fresh interval may be arbitrary. -/
theorem Formula.rawCompile_correct {ι : Type} (p : Formula ι) (inputs : ι → Nat)
    (base : Nat) (s : Nat → Bool) (hin : ∀ i, inputs i < base) :
    rawRun (p.rawCompile inputs base) s (p.result base) = p.eval (fun i => s (inputs i)) := by
  induction p generalizing base s with
  | constant b => simp [Formula.rawCompile, Formula.result, Formula.size,
      rawRun, RawAssignment.eval, RawAssignment.target, RawAssignment.value, Formula.eval]
  | input i => simp [Formula.rawCompile, Formula.result, Formula.size,
      rawRun, RawAssignment.eval, RawAssignment.target, RawAssignment.value, Formula.eval]
  | neg p ih =>
    have hp := p.size_pos
    have he : (Formula.neg p).result base = base + p.size := by
      simp only [Formula.result, Formula.size]
      omega
    rw [he]
    simp only [Formula.rawCompile, rawRun_append]
    have hstep := rawRun_single_target (RawAssignment.neg (p.result base) (base + p.size))
      (rawRun (p.rawCompile inputs base) s)
    simp only [RawAssignment.target, RawAssignment.value] at hstep
    rw [hstep]
    rw [ih base s hin]
    rfl
  | conj p q ihp ihq =>
    have hp := p.size_pos
    have hq := q.size_pos
    have he : (Formula.conj p q).result base = base + p.size + q.size := by
      simp only [Formula.result, Formula.size]
      omega
    have hin' : ∀ i, inputs i < base + p.size := fun i => (hin i).trans_le (by omega)
    have hkeep : (fun i => rawRun (p.rawCompile inputs base) s (inputs i)) =
        (fun i => s (inputs i)) := by
      funext i
      exact p.rawCompile_preserves inputs base s (inputs i) (hin i)
    have hl := q.rawCompile_preserves inputs (base + p.size)
      (rawRun (p.rawCompile inputs base) s) (p.result base) (by
        simp only [Formula.result]
        omega)
    have hr := ihq (base + p.size) (rawRun (p.rawCompile inputs base) s) hin'
    rw [hkeep] at hr
    rw [he]
    simp only [Formula.rawCompile, rawRun_append]
    have hstep := rawRun_single_target
      (RawAssignment.conj (p.result base) (q.result (base + p.size)) (base + p.size + q.size))
      (rawRun (q.rawCompile inputs (base + p.size)) (rawRun (p.rawCompile inputs base) s))
    simp only [RawAssignment.target, RawAssignment.value] at hstep
    rw [hstep]
    rw [hl, hr, ihp base s hin]
    rfl

end ShiReversibleFormula
