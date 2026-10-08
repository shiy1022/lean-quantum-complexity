import ReversibleFormulaRaw

set_option autoImplicit false
namespace ShiReversibleFormula
variable {ι : Type}

def falsePadding (base count : Nat) : List RawAssignment :=
  (List.range' base count).map (fun t => .constant t false)

@[simp] theorem falsePadding_targets (base count : Nat) :
    (falsePadding base count).map RawAssignment.target = List.range' base count := by
  simp [falsePadding, List.map_map, Function.comp_def, RawAssignment.target]

@[simp] theorem falsePadding_length (base count : Nat) :
    (falsePadding base count).length = count := by simp [falsePadding]

theorem falsePadding_preserves (base count : Nat) (s : Nat → Bool) (i : Nat) (hi : i < base) :
    rawRun (falsePadding base count) s i = s i := by
  apply rawRun_preserves
  intro a ha he
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
  obtain ⟨j, hj, heq⟩ := List.mem_range'.mp ht
  simp only [RawAssignment.target, Nat.one_mul] at he heq
  omega

/-- Constant-stride compilation: pad to bound nodes, then put the result in the final slot. -/
def Formula.paddedCompile (p : Formula ι) (inputs : ι → Nat) (base bound : Nat) : List RawAssignment :=
  p.rawCompile inputs base ++ falsePadding (base + p.size) (bound - p.size) ++
    [.copy (p.result base) (base + bound)]

theorem Formula.paddedCompile_length (p : Formula ι) (inputs : ι → Nat) (base bound : Nat)
    (hp : p.size ≤ bound) : (p.paddedCompile inputs base bound).length = bound + 1 := by
  simp [Formula.paddedCompile]
  omega

theorem Formula.paddedCompile_targets (p : Formula ι) (inputs : ι → Nat) (base bound : Nat)
    (hp : p.size ≤ bound) :
    (p.paddedCompile inputs base bound).map RawAssignment.target = List.range' base (bound + 1) := by
  simp only [Formula.paddedCompile, List.map_append, Formula.rawCompile_targets,
    falsePadding_targets, List.map_cons, List.map_nil, RawAssignment.target]
  rw [List.range'_append_1]
  have h : p.size + (bound - p.size) = bound := by omega
  rw [h]
  simpa using (List.range'_append_1 (s := base) (m := bound) (n := 1))

theorem Formula.paddedCompile_correct (p : Formula ι) (inputs : ι → Nat) (base bound : Nat)
    (hp : p.size ≤ bound) (s : Nat → Bool) (hin : ∀ i, inputs i < base) :
    rawRun (p.paddedCompile inputs base bound) s (base + bound) =
      p.eval (fun i => s (inputs i)) := by
  have hresult : p.result base < base + p.size := by
    have h := p.size_pos
    simp only [Formula.result]
    omega
  simp only [Formula.paddedCompile, rawRun_append]
  change rawRun [.copy (p.result base) (base + bound)]
    (rawRun (falsePadding (base + p.size) (bound - p.size))
      (rawRun (p.rawCompile inputs base) s)) (RawAssignment.copy (p.result base) (base + bound)).target = _
  rw [rawRun_single_target]
  change rawRun (falsePadding (base + p.size) (bound - p.size))
    (rawRun (p.rawCompile inputs base) s) (p.result base) = _
  rw [falsePadding_preserves _ _ _ _ hresult, p.rawCompile_correct inputs base s hin]

theorem Formula.paddedCompile_topological (p : Formula ι) (inputs : ι → Nat) (base bound : Nat)
    (hp : p.size ≤ bound) (hin : ∀ i, inputs i < base) :
    ∀ a ∈ p.paddedCompile inputs base bound, a.Topological := by
  intro a ha
  simp only [Formula.paddedCompile, List.mem_append, List.mem_singleton] at ha
  rcases ha with (ha | ha) | rfl
  · exact p.rawCompile_topological inputs base hin a ha
  · obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
    trivial
  · have h := p.size_pos
    simp only [RawAssignment.Topological, Formula.result]
    omega

end ShiReversibleFormula
