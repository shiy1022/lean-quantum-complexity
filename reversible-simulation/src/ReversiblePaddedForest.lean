import ReversiblePaddedFormula
import ReversibleForestCircuit

set_option autoImplicit false
namespace ShiReversibleFormula
open ShiReversible
variable {ι : Type}

/-- Each formula receives the same number of fresh nodes, including its reserved result slot. -/
def paddedForestCompile (inputs : ι → Nat) (base bound : Nat) : List (Formula ι) → List RawAssignment
  | [] => []
  | p :: ps => p.paddedCompile inputs base bound ++ paddedForestCompile inputs (base + (bound + 1)) bound ps

def paddedForestResult (base bound i : Nat) : Nat := base + i * (bound + 1) + bound

@[simp] theorem paddedForestCompile_length (ps : List (Formula ι)) (inputs : ι → Nat)
    (base bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound) :
    (paddedForestCompile inputs base bound ps).length = ps.length * (bound + 1) := by
  induction ps generalizing base with
  | nil => simp [paddedForestCompile]
  | cons p ps ih =>
    simp only [paddedForestCompile, List.length_append, p.paddedCompile_length inputs base bound
      (h p (by simp)), ih _ (fun q hq => h q (by simp [hq])), List.length_cons, Nat.succ_mul]
    omega

theorem paddedForestCompile_targets (ps : List (Formula ι)) (inputs : ι → Nat)
    (base bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound) :
    (paddedForestCompile inputs base bound ps).map RawAssignment.target =
      List.range' base (ps.length * (bound + 1)) := by
  induction ps generalizing base with
  | nil => simp [paddedForestCompile]
  | cons p ps ih =>
    simp only [paddedForestCompile, List.map_append,
      p.paddedCompile_targets inputs base bound (h p (by simp)),
      ih _ (fun q hq => h q (by simp [hq])), List.length_cons, Nat.succ_mul]
    rw [List.range'_append_1]
    congr 1
    omega

theorem paddedForestCompile_interval (ps : List (Formula ι)) (inputs : ι → Nat)
    (base bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound)
    (a : RawAssignment) (ha : a ∈ paddedForestCompile inputs base bound ps) :
    base ≤ a.target ∧ a.target < base + ps.length * (bound + 1) := by
  have ht : a.target ∈ List.range' base (ps.length * (bound + 1)) := by
    rw [← paddedForestCompile_targets ps inputs base bound h]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨j, hj, he⟩ := List.mem_range'.mp ht
  simp only [Nat.one_mul] at he
  omega

theorem paddedForestCompile_preserves (ps : List (Formula ι)) (inputs : ι → Nat)
    (base bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound) (s : Nat → Bool)
    (i : Nat) (hi : i < base) : rawRun (paddedForestCompile inputs base bound ps) s i = s i := by
  apply rawRun_preserves
  intro a ha he
  have ht := (paddedForestCompile_interval ps inputs base bound h a ha).1
  omega

theorem paddedForestCompile_topological (ps : List (Formula ι)) (inputs : ι → Nat)
    (base bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound) (hin : ∀ i, inputs i < base) :
    ∀ a ∈ paddedForestCompile inputs base bound ps, a.Topological := by
  induction ps generalizing base with
  | nil => simp [paddedForestCompile]
  | cons p ps ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact p.paddedCompile_topological inputs base bound (h p (by simp)) hin a ha
    · exact ih (base + (bound + 1)) (fun q hq => h q (by simp [hq]))
        (fun i => (hin i).trans_le (by omega)) a ha

theorem paddedForestResult_bound (base bound count i : Nat) (hi : i < count) :
    base ≤ paddedForestResult base bound i ∧
      paddedForestResult base bound i < base + count * (bound + 1) := by
  have h := Nat.mul_le_mul_right (bound + 1) (show i + 1 ≤ count by omega)
  simp only [paddedForestResult, Nat.add_mul, Nat.one_mul] at *
  omega

/-- Constant-stride forest semantics; later blocks preserve all earlier results and inputs. -/
theorem paddedForestCompile_correct (ps : List (Formula ι)) (inputs : ι → Nat)
    (base bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound) (s : Nat → Bool)
    (hin : ∀ i, inputs i < base) (i : Nat) (hi : i < ps.length) :
    rawRun (paddedForestCompile inputs base bound ps) s (paddedForestResult base bound i) =
      (ps[i]).eval (fun j => s (inputs j)) := by
  induction ps generalizing base s i with
  | nil => simp at hi
  | cons p ps ih =>
    have hp := h p (by simp)
    have hs : ∀ q ∈ ps, q.size ≤ bound := fun q hq => h q (by simp [hq])
    cases i with
    | zero =>
      have hk := paddedForestCompile_preserves ps inputs (base + (bound + 1)) bound hs
        (rawRun (p.paddedCompile inputs base bound) s) (base + bound) (by omega)
      simp only [paddedForestCompile, rawRun_append, paddedForestResult, Nat.zero_mul,
        Nat.add_zero, List.getElem_cons_zero]
      rw [hk, p.paddedCompile_correct inputs base bound hp s hin]
    | succ i =>
      have hit : i < ps.length := by simpa using hi
      have hin' : ∀ j, inputs j < base + (bound + 1) := fun j => (hin j).trans_le (by omega)
      have hk : (fun j => rawRun (p.paddedCompile inputs base bound) s (inputs j)) =
          (fun j => s (inputs j)) := by
        funext j
        apply rawRun_preserves
        intro a ha he
        have ht : base ≤ a.target := by
          have hm : a.target ∈ List.range' base (bound + 1) := by
            rw [← p.paddedCompile_targets inputs base bound hp]
            exact List.mem_map.mpr ⟨a, ha, rfl⟩
          obtain ⟨k, _, heq⟩ := List.mem_range'.mp hm
          simp only [Nat.one_mul] at heq
          omega
        have hj := hin j
        omega
      have hr := ih (base + (bound + 1)) hs (rawRun (p.paddedCompile inputs base bound) s)
        hin' i hit
      rw [hk] at hr
      simpa only [paddedForestCompile, rawRun_append, paddedForestResult, Nat.succ_mul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.getElem_cons_succ] using hr

/-- Fixed-stride forests instantiate the existing reversible compiler and global cleanup. -/
def paddedForestCircuit {n : Nat} (ps : List (Formula (Fin n))) (bound : Nat)
    (h : ∀ p ∈ ps, p.size ≤ bound) :
    SingleAssignmentCircuit n (ps.length * (bound + 1)) ps.length := by
  let raw := paddedForestCompile (fun i => i.val) n bound ps
  have ht : ∀ a ∈ raw, a.target < n + ps.length * (bound + 1) :=
    fun a ha => (paddedForestCompile_interval ps _ n bound h a ha).2
  have hp : ∀ a ∈ raw, a.Topological := paddedForestCompile_topological ps _ n bound h (fun i => i.isLt)
  let nodes := boundProgram (n + ps.length * (bound + 1)) raw ht hp
  exact {
    nodes := nodes
    targets_distinct := by
      apply List.Nodup.of_map Fin.val
      simp only [List.map_map, Function.comp_def]
      change (nodes.map (fun a => a.target.val)).Nodup
      rw [boundProgram_targets, paddedForestCompile_targets ps _ n bound h]
      exact List.nodup_range' _
    targets_auxiliary := by
      intro b hb
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
      rw [RawAssignment.toAssignment_target]
      exact (paddedForestCompile_interval ps _ n bound h a.val a.property).1
    nodes_length := by
      simpa only [nodes, raw, boundProgram_length] using paddedForestCompile_length ps _ n bound h
    read := fun i => ⟨paddedForestResult n bound i.val, (paddedForestResult_bound n bound ps.length i.val i.isLt).2⟩ }

@[simp] theorem paddedForestCircuit_eval {n : Nat} (ps : List (Formula (Fin n))) (bound : Nat)
    (h : ∀ p ∈ ps, p.size ≤ bound) (x : Bits n) (i : Fin ps.length) :
    (paddedForestCircuit ps bound h).eval x i = (ps[i.val]).eval x := by
  unfold paddedForestCircuit SingleAssignmentCircuit.eval
  rw [← initialNat_restrict x, boundProgram_correct]
  change rawRun (paddedForestCompile (fun i => i.val) n bound ps) (initialNat x)
    (paddedForestResult n bound i.val) = _
  rw [paddedForestCompile_correct ps _ n bound h _ (fun j => j.isLt) i.val i.isLt]
  congr 1
  funext j
  simp [initialNat]

theorem paddedForestCircuit_quantum_clean {n : Nat} (ps : List (Formula (Fin n))) (bound : Nat)
    (h : ∀ p ∈ ps, p.size ≤ bound) (x : Bits n) :
    quantumRun (paddedForestCircuit ps bound h).reversible
      (basis (inputMemory x, fun _ => false)) =
      basis (inputMemory x, fun i => (ps[i.val]).eval x) := by
  have he : (paddedForestCircuit ps bound h).eval x = (fun i => (ps[i.val]).eval x) :=
    funext (paddedForestCircuit_eval ps bound h x)
  simpa only [he] using (paddedForestCircuit ps bound h).quantum_clean_correct x

theorem paddedForestCircuit_size {n : Nat} (ps : List (Formula (Fin n))) (bound : Nat)
    (h : ∀ p ∈ ps, p.size ≤ bound) :
    (paddedForestCircuit ps bound h).reversible.length ≤ 4 * (ps.length * (bound + 1)) + ps.length :=
  (paddedForestCircuit ps bound h).size_bound

end ShiReversibleFormula
