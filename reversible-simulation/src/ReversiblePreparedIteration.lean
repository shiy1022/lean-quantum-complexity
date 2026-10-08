import ReversibleIterationCircuit

set_option autoImplicit false
namespace ShiReversibleFormula
open ShiReversible
variable {n m : Nat}

def forestEvaluate (ps : List (Formula (Fin n))) (hp : ps.length = m) (x : Bits n) : Bits m :=
  fun i => (ps[i.val]'(by simpa [hp] using i.isLt)).eval x

/-- Compile the preparation first, then feed its result addresses directly to the time slices. -/
def preparedCompile (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat) : List RawAssignment :=
  forestCompile (fun i => i.val) n ps ++ iterationCompile qs hq t
    (fun i => forestResult n ps i.val) (n + forestSize ps)

def preparedSize (ps : List (Formula (Fin n))) (qs : List (Formula (Fin m))) (t : Nat) : Nat :=
  forestSize ps + t * forestSize qs

theorem preparedCompile_targets (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat) :
    (preparedCompile ps hp qs hq t).map RawAssignment.target = List.range' n (preparedSize ps qs t) := by
  simp [preparedCompile, preparedSize, forestCompile_targets, iterationCompile_targets]

theorem preparedCompile_interval (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat)
    (a : RawAssignment) (ha : a ∈ preparedCompile ps hp qs hq t) :
    n ≤ a.target ∧ a.target < n + preparedSize ps qs t := by
  have ht : a.target ∈ List.range' n (preparedSize ps qs t) := by
    rw [← preparedCompile_targets ps hp qs hq t]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨j, hj, he⟩ := List.mem_range'.mp ht
  simp only [Nat.one_mul] at he
  omega

theorem preparedCompile_topological (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat) :
    ∀ a ∈ preparedCompile ps hp qs hq t, a.Topological := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact forestCompile_topological ps _ n (fun i => i.isLt) a ha
  · exact iterationCompile_topological qs hq t _ _
      (fun i => (forestResult_bound ps n i.val (by simpa [hp] using i.isLt)).2) a ha

def preparedCircuit (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat) :
    SingleAssignmentCircuit n (preparedSize ps qs t) m := by
  let raw := preparedCompile ps hp qs hq t
  have ht : ∀ a ∈ raw, a.target < n + preparedSize ps qs t :=
    fun a ha => (preparedCompile_interval ps hp qs hq t a ha).2
  have htop := preparedCompile_topological ps hp qs hq t
  let nodes := boundProgram (n + preparedSize ps qs t) raw ht htop
  exact {
    nodes := nodes
    targets_distinct := by
      apply List.Nodup.of_map Fin.val
      simp only [List.map_map, Function.comp_def]
      change (nodes.map (fun a => a.target.val)).Nodup
      rw [boundProgram_targets, preparedCompile_targets]
      exact List.nodup_range' _
    targets_auxiliary := by
      intro b hb
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
      rw [RawAssignment.toAssignment_target]
      exact (preparedCompile_interval ps hp qs hq t a.val a.property).1
    nodes_length := by simp [nodes, raw, preparedCompile, preparedSize]
    read := fun i => ⟨iterationRead qs hq t (fun j => forestResult n ps j.val) (n + forestSize ps) i, by
      have h := iterationRead_bound qs hq t _ (n + forestSize ps)
        (fun j => (forestResult_bound ps n j.val (by simpa [hp] using j.isLt)).2) i
      simpa [preparedSize, Nat.add_assoc] using h⟩ }

@[simp] theorem preparedCircuit_eval (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat) (x : Bits n) :
    (preparedCircuit ps hp qs hq t).eval x = forestAdvance qs hq t (forestEvaluate ps hp x) := by
  funext i
  unfold preparedCircuit SingleAssignmentCircuit.eval
  rw [← initialNat_restrict x, boundProgram_correct]
  change rawRun (preparedCompile ps hp qs hq t) (initialNat x)
    (iterationRead qs hq t (fun j => forestResult n ps j.val) (n + forestSize ps) i) = _
  simp only [preparedCompile, rawRun_append]
  rw [iterationCompile_correct qs hq t _ _ _
    (fun j => (forestResult_bound ps n j.val (by simpa [hp] using j.isLt)).2)]
  have he : (fun j : Fin m => rawRun (forestCompile (fun k => k.val) n ps) (initialNat x)
      (forestResult n ps j.val)) = forestEvaluate ps hp x := by
    funext j
    rw [forestCompile_correct ps _ _ _ (fun k => k.isLt) j.val (by simpa [hp] using j.isLt)]
    change (ps[j.val]).eval (fun k => initialNat x k.val) = (ps[j.val]).eval x
    congr 1
    funext k
    simp [initialNat]
  rw [he]

theorem preparedCircuit_quantum_clean_correct (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat) (x : Bits n) :
    quantumRun (preparedCircuit ps hp qs hq t).reversible
      (basis (inputMemory (k := preparedSize ps qs t) x, fun _ => false)) =
      basis (inputMemory (k := preparedSize ps qs t) x, forestAdvance qs hq t (forestEvaluate ps hp x)) := by
  simpa only [preparedCircuit_eval] using (preparedCircuit ps hp qs hq t).quantum_clean_correct x

theorem preparedSize_bound (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t a b : Nat)
    (hps : ∀ p ∈ ps, p.size ≤ a) (hqs : ∀ q ∈ qs, q.size ≤ b) :
    preparedSize ps qs t ≤ m * a + t * (m * b) := by
  have hs := forestSize_bound ps a hps
  have ht := Nat.mul_le_mul_left t (forestSize_bound qs b hqs)
  simpa [preparedSize, hp, hq] using Nat.add_le_add hs ht

end ShiReversibleFormula
