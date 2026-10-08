import ReversibleForestRaw
import ReversibleFormulaCircuit

set_option autoImplicit false

namespace ShiReversibleFormula

open ShiReversible

/-- A whole configuration-output forest compiles into one clean circuit with disjoint targets. -/
def forestCircuit {n : Nat} (ps : List (Formula (Fin n))) :
    SingleAssignmentCircuit n (forestSize ps) ps.length := by
  let raw := forestCompile (fun i => i.val) n ps
  have ht : ∀ a ∈ raw, a.target < n + forestSize ps :=
    fun a ha => (forestCompile_target_interval ps _ n a ha).2
  have hp : ∀ a ∈ raw, a.Topological := forestCompile_topological ps _ n (fun i => i.isLt)
  let nodes := boundProgram (n + forestSize ps) raw ht hp
  exact {
    nodes := nodes
    targets_distinct := by
      apply List.Nodup.of_map Fin.val
      simp only [List.map_map, Function.comp_def]
      change (nodes.map (fun a => a.target.val)).Nodup
      rw [boundProgram_targets, forestCompile_targets]
      exact List.nodup_range' _
    targets_auxiliary := by
      intro b hb
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
      rw [RawAssignment.toAssignment_target]
      exact (forestCompile_target_interval ps _ n a.val a.property).1
    nodes_length := by simp [nodes, raw]
    read := fun i => ⟨forestResult n ps i.val, (forestResult_bound ps n i.val i.isLt).2⟩ }

@[simp] theorem forestCircuit_eval {n : Nat} (ps : List (Formula (Fin n)))
    (x : Bits n) (i : Fin ps.length) : (forestCircuit ps).eval x i = (ps[i.val]).eval x := by
  unfold forestCircuit SingleAssignmentCircuit.eval
  rw [← initialNat_restrict x, boundProgram_correct]
  change rawRun (forestCompile (fun i => i.val) n ps) (initialNat x)
      (forestResult n ps i.val) = (ps[i.val]).eval x
  rw [forestCompile_correct ps _ _ _ (fun j => j.isLt) i.val i.isLt]
  congr 1
  funext j
  simp [initialNat]

theorem forestCircuit_quantum_clean_correct {n : Nat} (ps : List (Formula (Fin n)))
    (x : Bits n) :
    quantumRun (forestCircuit ps).reversible
      (basis (inputMemory (k := forestSize ps) x, fun _ => false)) =
      basis (inputMemory (k := forestSize ps) x, fun i => (ps[i.val]).eval x) := by
  have he : (forestCircuit ps).eval x = (fun i => (ps[i.val]).eval x) :=
    funext (forestCircuit_eval ps x)
  simpa only [he] using (forestCircuit ps).quantum_clean_correct x

/-- Exact clean XOR computation for arbitrary contents of the external output register. -/
theorem forestCircuit_clean_correct {n : Nat} (ps : List (Formula (Fin n)))
    (x : Bits n) (y : Bits ps.length) :
    execute (forestCircuit ps).reversible (inputMemory (k := forestSize ps) x, y) =
      (inputMemory (k := forestSize ps) x, fun i => xor (y i) ((ps[i.val]).eval x)) := by
  simpa only [forestCircuit_eval] using (forestCircuit ps).clean_correct x y

theorem forestCircuit_size_bound {n : Nat} (ps : List (Formula (Fin n))) (bound : Nat)
    (h : ∀ p ∈ ps, p.size ≤ bound) :
    (forestCircuit ps).reversible.length ≤ 4 * ps.length * bound + ps.length := by
  have hc := (forestCircuit ps).size_bound
  have hs := forestSize_bound ps bound h
  have hm := Nat.mul_le_mul_left 4 hs
  calc
    _ ≤ 4 * forestSize ps + ps.length := hc
    _ ≤ 4 * (ps.length * bound) + ps.length := Nat.add_le_add_right hm _
    _ = _ := by rw [Nat.mul_assoc]

end ShiReversibleFormula
