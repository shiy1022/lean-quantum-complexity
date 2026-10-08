import ReversiblePreparedIteration

set_option autoImplicit false
namespace ShiReversibleFormula
open ShiReversible
variable {n m : Nat}

def preparedRead (ps : List (Formula (Fin n))) (qs : List (Formula (Fin m)))
    (hq : qs.length = m) (t : Nat) : Fin m → Nat :=
  iterationRead qs hq t (fun j => forestResult n ps j.val) (n + forestSize ps)

theorem preparedRead_bound (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat) (i : Fin m) :
    preparedRead ps qs hq t i < n + preparedSize ps qs t := by
  have h := iterationRead_bound qs hq t _ (n + forestSize ps)
    (fun j => (forestResult_bound ps n j.val (by simpa [hp] using j.isLt)).2) i
  simpa [preparedRead, preparedSize, Nat.add_assoc] using h

theorem preparedCompile_correct (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat) (x : Bits n) :
    (fun i => rawRun (preparedCompile ps hp qs hq t) (initialNat x)
      (preparedRead ps qs hq t i)) = forestAdvance qs hq t (forestEvaluate ps hp x) := by
  have h := preparedCircuit_eval ps hp qs hq t x
  unfold preparedCircuit SingleAssignmentCircuit.eval at h
  rw [← initialNat_restrict x, boundProgram_correct] at h
  exact h

/-- Append extraction while retaining all intermediate addresses for a single global uncompute. -/
def finishedCompile (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat)
    (rs : List (Formula (Fin m))) : List RawAssignment :=
  preparedCompile ps hp qs hq t ++
    forestCompile (preparedRead ps qs hq t) (n + preparedSize ps qs t) rs

def finishedSize (ps : List (Formula (Fin n))) (qs rs : List (Formula (Fin m))) (t : Nat) : Nat :=
  preparedSize ps qs t + forestSize rs

theorem finishedCompile_targets (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat)
    (rs : List (Formula (Fin m))) :
    (finishedCompile ps hp qs hq t rs).map RawAssignment.target =
      List.range' n (finishedSize ps qs rs t) := by
  simp [finishedCompile, finishedSize, preparedCompile_targets, forestCompile_targets]

theorem finishedCompile_interval (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat)
    (rs : List (Formula (Fin m))) (a : RawAssignment) (ha : a ∈ finishedCompile ps hp qs hq t rs) :
    n ≤ a.target ∧ a.target < n + finishedSize ps qs rs t := by
  have ht : a.target ∈ List.range' n (finishedSize ps qs rs t) := by
    rw [← finishedCompile_targets ps hp qs hq t rs]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨j, hj, he⟩ := List.mem_range'.mp ht
  simp only [Nat.one_mul] at he
  omega

theorem finishedCompile_topological (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat)
    (rs : List (Formula (Fin m))) : ∀ a ∈ finishedCompile ps hp qs hq t rs, a.Topological := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact preparedCompile_topological ps hp qs hq t a ha
  · exact forestCompile_topological rs _ _ (preparedRead_bound ps hp qs hq t) a ha

def finishedCircuit (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat)
    (rs : List (Formula (Fin m))) : SingleAssignmentCircuit n (finishedSize ps qs rs t) rs.length := by
  let raw := finishedCompile ps hp qs hq t rs
  have ht : ∀ a ∈ raw, a.target < n + finishedSize ps qs rs t :=
    fun a ha => (finishedCompile_interval ps hp qs hq t rs a ha).2
  have htop := finishedCompile_topological ps hp qs hq t rs
  let nodes := boundProgram (n + finishedSize ps qs rs t) raw ht htop
  exact {
    nodes := nodes
    targets_distinct := by
      apply List.Nodup.of_map Fin.val
      simp only [List.map_map, Function.comp_def]
      change (nodes.map (fun a => a.target.val)).Nodup
      rw [boundProgram_targets, finishedCompile_targets]
      exact List.nodup_range' _
    targets_auxiliary := by
      intro b hb
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
      rw [RawAssignment.toAssignment_target]
      exact (finishedCompile_interval ps hp qs hq t rs a.val a.property).1
    nodes_length := by simp [nodes, raw, finishedCompile, preparedCompile, finishedSize, preparedSize, Nat.add_assoc]
    read := fun i => ⟨forestResult (n + preparedSize ps qs t) rs i.val, by
      have h := (forestResult_bound rs (n + preparedSize ps qs t) i.val i.isLt).2
      simpa [finishedSize, Nat.add_assoc] using h⟩ }

theorem finishedCircuit_eval (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (t : Nat)
    (rs : List (Formula (Fin m))) (x : Bits n) (i : Fin rs.length) :
    (finishedCircuit ps hp qs hq t rs).eval x i =
      (rs[i.val]).eval (forestAdvance qs hq t (forestEvaluate ps hp x)) := by
  unfold finishedCircuit SingleAssignmentCircuit.eval
  rw [← initialNat_restrict x, boundProgram_correct]
  change rawRun (finishedCompile ps hp qs hq t rs) (initialNat x)
    (forestResult (n + preparedSize ps qs t) rs i.val) = _
  simp only [finishedCompile, rawRun_append]
  rw [forestCompile_correct rs _ _ _ (preparedRead_bound ps hp qs hq t) i.val i.isLt,
    preparedCompile_correct]

end ShiReversibleFormula
