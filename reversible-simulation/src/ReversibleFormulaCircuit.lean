import ReversibleRawBridge

set_option autoImplicit false

namespace ShiReversibleFormula

open ShiReversible

/-- A formula becomes an actual circuit in the already verified clean-simulation model. -/
def Formula.circuit {n : Nat} (p : Formula (Fin n)) : SingleAssignmentCircuit n p.size 1 := by
  let raw := p.rawCompile (fun i => i.val) n
  have ht : ∀ a ∈ raw, a.target < n + p.size :=
    fun a ha => (p.rawCompile_target_interval _ n a ha).2
  have hp : ∀ a ∈ raw, a.Topological := p.rawCompile_topological _ n (fun i => i.isLt)
  let nodes := boundProgram (n + p.size) raw ht hp
  exact {
    nodes := nodes
    targets_distinct := by
      apply List.Nodup.of_map Fin.val
      simp only [List.map_map, Function.comp_def]
      change (nodes.map (fun a => a.target.val)).Nodup
      rw [boundProgram_targets, p.rawCompile_targets]
      exact List.nodup_range' _
    targets_auxiliary := by
      intro b hb
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
      rw [RawAssignment.toAssignment_target]
      exact (p.rawCompile_target_interval _ n a.val a.property).1
    nodes_length := by simp [nodes, raw]
    read := fun _ => ⟨p.result n, by
      have h := p.size_pos
      simp only [Formula.result]
      omega⟩ }

def initialNat {n : Nat} (x : Bits n) : Nat → Bool :=
  fun i => if h : i < n then x ⟨i, h⟩ else false

theorem initialNat_restrict {n k : Nat} (x : Bits n) :
    restrict (n + k) (initialNat x) = inputMemory (k := k) x := by
  rfl

@[simp] theorem Formula.circuit_eval {n : Nat} (p : Formula (Fin n)) (x : Bits n)
    (i : Fin 1) : p.circuit.eval x i = p.eval x := by
  unfold Formula.circuit SingleAssignmentCircuit.eval
  rw [← initialNat_restrict x, boundProgram_correct]
  change rawRun (p.rawCompile (fun i => i.val) n) (initialNat x) (p.result n) = p.eval x
  rw [p.rawCompile_correct _ _ _ (fun i => i.isLt)]
  congr 1
  funext j
  simp [initialNat]

/-- No construction or cleanup assumptions remain for the formula-to-quantum-circuit bridge. -/
theorem Formula.quantum_clean_correct {n : Nat} (p : Formula (Fin n)) (x : Bits n) :
    quantumRun p.circuit.reversible (basis (inputMemory (k := p.size) x, fun _ => false)) =
      basis (inputMemory (k := p.size) x, fun _ => p.eval x) := by
  have he : p.circuit.eval x = (fun _ => p.eval x) := funext (p.circuit_eval x)
  simpa only [he] using p.circuit.quantum_clean_correct x

theorem Formula.reversible_size {n : Nat} (p : Formula (Fin n)) :
    p.circuit.reversible.length ≤ 4 * p.size + 1 := p.circuit.size_bound

end ShiReversibleFormula
