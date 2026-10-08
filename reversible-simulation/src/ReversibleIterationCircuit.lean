import ReversibleForestIteration

set_option autoImplicit false
namespace ShiReversibleFormula
open ShiReversible

variable {n : Nat}

theorem iterationCompile_target_interval (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (t : Nat) (inputs : Fin n → Nat) (base : Nat) (a : RawAssignment)
    (ha : a ∈ iterationCompile ps hl t inputs base) :
    base ≤ a.target ∧ a.target < base + t * forestSize ps := by
  have ht : a.target ∈ List.range' base (t * forestSize ps) := by
    rw [← iterationCompile_targets ps hl t inputs base]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨j, hj, he⟩ := List.mem_range'.mp ht
  simp only [Nat.one_mul] at he
  omega

theorem iterationCompile_preserves (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (t : Nat) (inputs : Fin n → Nat) (base : Nat) (s : Nat → Bool) (i : Nat) (hi : i < base) :
    rawRun (iterationCompile ps hl t inputs base) s i = s i := by
  apply rawRun_preserves
  intro a ha he
  have ht := (iterationCompile_target_interval ps hl t inputs base a ha).1
  omega

/-- One single-assignment circuit for the entire iteration, sharing configuration references. -/
def iterationCircuit (ps : List (Formula (Fin n))) (hl : ps.length = n) (t : Nat) :
    SingleAssignmentCircuit n (t * forestSize ps) n := by
  let raw := iterationCompile ps hl t (fun i => i.val) n
  have ht : ∀ a ∈ raw, a.target < n + t * forestSize ps :=
    fun a ha => (iterationCompile_target_interval ps hl t _ n a ha).2
  have hp : ∀ a ∈ raw, a.Topological := iterationCompile_topological ps hl t _ n (fun i => i.isLt)
  let nodes := boundProgram (n + t * forestSize ps) raw ht hp
  exact {
    nodes := nodes
    targets_distinct := by
      apply List.Nodup.of_map Fin.val
      simp only [List.map_map, Function.comp_def]
      change (nodes.map (fun a => a.target.val)).Nodup
      rw [boundProgram_targets, iterationCompile_targets]
      exact List.nodup_range' _
    targets_auxiliary := by
      intro b hb
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
      rw [RawAssignment.toAssignment_target]
      exact (iterationCompile_target_interval ps hl t _ n a.val a.property).1
    nodes_length := by simp [nodes, raw]
    read := fun i => ⟨iterationRead ps hl t (fun j => j.val) n i,
      iterationRead_bound ps hl t _ n (fun j => j.isLt) i⟩ }

@[simp] theorem iterationCircuit_eval (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (t : Nat) (x : Bits n) : (iterationCircuit ps hl t).eval x = forestAdvance ps hl t x := by
  funext i
  unfold iterationCircuit SingleAssignmentCircuit.eval
  rw [← initialNat_restrict x, boundProgram_correct]
  change rawRun (iterationCompile ps hl t (fun j => j.val) n) (initialNat x)
      (iterationRead ps hl t (fun j => j.val) n i) = _
  rw [iterationCompile_correct ps hl t _ _ _ (fun j => j.isLt)]
  congr 2
  funext j
  simp [initialNat]

theorem iterationCircuit_quantum_clean_correct (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (t : Nat) (x : Bits n) :
    quantumRun (iterationCircuit ps hl t).reversible
      (basis (inputMemory (k := t * forestSize ps) x, fun _ => false)) =
      basis (inputMemory (k := t * forestSize ps) x, forestAdvance ps hl t x) := by
  simpa only [iterationCircuit_eval] using (iterationCircuit ps hl t).quantum_clean_correct x

theorem iterationCircuit_clean_correct (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (t : Nat) (x y : Bits n) :
    execute (iterationCircuit ps hl t).reversible (inputMemory (k := t * forestSize ps) x, y) =
      (inputMemory (k := t * forestSize ps) x, fun i => xor (y i) (forestAdvance ps hl t x i)) := by
  simpa only [iterationCircuit_eval] using (iterationCircuit ps hl t).clean_correct x y

theorem iterationCircuit_size (ps : List (Formula (Fin n))) (hl : ps.length = n) (t b : Nat)
    (h : ∀ p ∈ ps, p.size ≤ b) :
    (iterationCircuit ps hl t).reversible.length ≤ 4 * t * n * b + n := by
  have hs := forestSize_bound ps b h
  rw [hl] at hs
  have hc := (iterationCircuit ps hl t).size_bound
  have hm := Nat.mul_le_mul_left (4 * t) hs
  calc
    _ ≤ 4 * (t * forestSize ps) + n := hc
    _ ≤ 4 * t * (n * b) + n := by simpa [Nat.mul_assoc] using Nat.add_le_add_right hm n
    _ = _ := by simp [Nat.mul_assoc]

theorem forestAdvance_succ_last (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (t : Nat) (x : Bits n) :
    forestAdvance ps hl (t + 1) x = forestStep ps hl (forestAdvance ps hl t x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simpa only [forestAdvance] using ih (forestStep ps hl x)

end ShiReversibleFormula
