import ReversiblePaddedIteration
import ReversiblePreparedIteration

set_option autoImplicit false
namespace ShiReversibleFormula
open ShiReversible
variable {n m : Nat}

def paddedPreparedRead (ps : List (Formula (Fin n))) (qs : List (Formula (Fin m)))
    (hq : qs.length = m) (ib tb t : Nat) : Fin m → Nat :=
  paddedIterationRead qs hq tb t (fun i => paddedForestResult n ib i.val)
    (n + ps.length * (ib + 1))

def paddedFinishedSize (ps : List (Formula (Fin n))) (qs rs : List (Formula (Fin m)))
    (ib tb rb t : Nat) : Nat :=
  ps.length * (ib + 1) + t * (qs.length * (tb + 1)) + rs.length * (rb + 1)

/-- Initialization, every time slice and extraction use fixed blocks before one global cleanup. -/
def paddedFinishedCompile (ps : List (Formula (Fin n))) (qs rs : List (Formula (Fin m)))
    (hq : qs.length = m) (ib tb rb t : Nat) : List RawAssignment :=
  paddedForestCompile (fun i => i.val) n ib ps ++
  paddedIterationCompile qs hq tb t (fun i => paddedForestResult n ib i.val)
    (n + ps.length * (ib + 1)) ++
  paddedForestCompile (paddedPreparedRead ps qs hq ib tb t)
    (n + ps.length * (ib + 1) + t * (m * (tb + 1))) rb rs

theorem paddedPreparedRead_bound (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs : List (Formula (Fin m))) (hq : qs.length = m) (ib tb t : Nat) (i : Fin m) :
    paddedPreparedRead ps qs hq ib tb t i <
      n + ps.length * (ib + 1) + t * (m * (tb + 1)) :=
  paddedIterationRead_bound qs hq tb t _ _
    (fun j => (paddedForestResult_bound n ib ps.length j.val (by simpa [hp] using j.isLt)).2) i

theorem paddedFinishedCompile_targets (ps : List (Formula (Fin n))) (qs rs : List (Formula (Fin m)))
    (hq : qs.length = m) (ib tb rb t : Nat)
    (hi : ∀ p ∈ ps, p.size ≤ ib) (ht : ∀ p ∈ qs, p.size ≤ tb) (hr : ∀ p ∈ rs, p.size ≤ rb) :
    (paddedFinishedCompile ps qs rs hq ib tb rb t).map RawAssignment.target =
      List.range' n (paddedFinishedSize ps qs rs ib tb rb t) := by
  simp only [paddedFinishedCompile, List.map_append,
    paddedForestCompile_targets ps _ n ib hi, paddedIterationCompile_targets qs hq tb ht,
    paddedForestCompile_targets rs _ _ rb hr, paddedFinishedSize, hq]
  rw [List.range'_append_1]
  simpa [Nat.add_assoc] using (List.range'_append_1 (s := n)
    (m := ps.length * (ib + 1) + t * (m * (tb + 1))) (n := rs.length * (rb + 1)))

theorem paddedFinishedCompile_length (ps : List (Formula (Fin n))) (qs rs : List (Formula (Fin m)))
    (hq : qs.length = m) (ib tb rb t : Nat)
    (hi : ∀ p ∈ ps, p.size ≤ ib) (ht : ∀ p ∈ qs, p.size ≤ tb) (hr : ∀ p ∈ rs, p.size ≤ rb) :
    (paddedFinishedCompile ps qs rs hq ib tb rb t).length = paddedFinishedSize ps qs rs ib tb rb t := by
  simp only [paddedFinishedCompile, List.length_append,
    paddedForestCompile_length ps _ n ib hi, paddedIterationCompile_length qs hq tb ht,
    paddedForestCompile_length rs _ _ rb hr, paddedFinishedSize, hq]

theorem paddedFinishedCompile_interval (ps : List (Formula (Fin n))) (qs rs : List (Formula (Fin m)))
    (hq : qs.length = m) (ib tb rb t : Nat)
    (hi : ∀ p ∈ ps, p.size ≤ ib) (ht : ∀ p ∈ qs, p.size ≤ tb) (hr : ∀ p ∈ rs, p.size ≤ rb)
    (a : RawAssignment) (ha : a ∈ paddedFinishedCompile ps qs rs hq ib tb rb t) :
    n ≤ a.target ∧ a.target < n + paddedFinishedSize ps qs rs ib tb rb t := by
  have hm : a.target ∈ List.range' n (paddedFinishedSize ps qs rs ib tb rb t) := by
    rw [← paddedFinishedCompile_targets ps qs rs hq ib tb rb t hi ht hr]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨j, hj, he⟩ := List.mem_range'.mp hm
  simp only [Nat.one_mul] at he
  omega

theorem paddedFinishedCompile_topological (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs rs : List (Formula (Fin m))) (hq : qs.length = m) (ib tb rb t : Nat)
    (hi : ∀ p ∈ ps, p.size ≤ ib) (ht : ∀ p ∈ qs, p.size ≤ tb) (hr : ∀ p ∈ rs, p.size ≤ rb) :
    ∀ a ∈ paddedFinishedCompile ps qs rs hq ib tb rb t, a.Topological := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · exact paddedForestCompile_topological ps _ n ib hi (fun i => i.isLt) a ha
    · exact paddedIterationCompile_topological qs hq tb ht t _ _
        (fun j => (paddedForestResult_bound n ib ps.length j.val (by simpa [hp] using j.isLt)).2) a ha
  · exact paddedForestCompile_topological rs _ _ rb hr
      (paddedPreparedRead_bound ps hp qs hq ib tb t) a ha

def paddedFinishedCircuit (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs rs : List (Formula (Fin m))) (hq : qs.length = m) (ib tb rb t : Nat)
    (hi : ∀ p ∈ ps, p.size ≤ ib) (ht : ∀ p ∈ qs, p.size ≤ tb) (hr : ∀ p ∈ rs, p.size ≤ rb) :
    SingleAssignmentCircuit n (paddedFinishedSize ps qs rs ib tb rb t) rs.length := by
  let raw := paddedFinishedCompile ps qs rs hq ib tb rb t
  have hb : ∀ a ∈ raw, a.target < n + paddedFinishedSize ps qs rs ib tb rb t :=
    fun a ha => (paddedFinishedCompile_interval ps qs rs hq ib tb rb t hi ht hr a ha).2
  have htop := paddedFinishedCompile_topological ps hp qs rs hq ib tb rb t hi ht hr
  let nodes := boundProgram (n + paddedFinishedSize ps qs rs ib tb rb t) raw hb htop
  exact {
    nodes := nodes
    targets_distinct := by
      apply List.Nodup.of_map Fin.val
      simp only [List.map_map, Function.comp_def]
      change (nodes.map (fun a => a.target.val)).Nodup
      rw [boundProgram_targets, paddedFinishedCompile_targets ps qs rs hq ib tb rb t hi ht hr]
      exact List.nodup_range' _
    targets_auxiliary := by
      intro b hb
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
      rw [RawAssignment.toAssignment_target]
      exact (paddedFinishedCompile_interval ps qs rs hq ib tb rb t hi ht hr a.val a.property).1
    nodes_length := by
      simpa only [nodes, raw, boundProgram_length] using
        paddedFinishedCompile_length ps qs rs hq ib tb rb t hi ht hr
    read := fun i => ⟨paddedForestResult
      (n + ps.length * (ib + 1) + t * (m * (tb + 1))) rb i.val, by
        have hb := (paddedForestResult_bound
          (n + ps.length * (ib + 1) + t * (m * (tb + 1))) rb rs.length i.val i.isLt).2
        simpa [paddedFinishedSize, hq, Nat.add_assoc] using hb⟩ }

theorem paddedFinishedCircuit_eval (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs rs : List (Formula (Fin m))) (hq : qs.length = m) (ib tb rb t : Nat)
    (hi : ∀ p ∈ ps, p.size ≤ ib) (ht : ∀ p ∈ qs, p.size ≤ tb) (hr : ∀ p ∈ rs, p.size ≤ rb)
    (x : Bits n) (i : Fin rs.length) :
    (paddedFinishedCircuit ps hp qs rs hq ib tb rb t hi ht hr).eval x i =
      (rs[i.val]).eval (forestAdvance qs hq t (forestEvaluate ps hp x)) := by
  unfold paddedFinishedCircuit SingleAssignmentCircuit.eval
  rw [← initialNat_restrict x, boundProgram_correct]
  change rawRun (paddedFinishedCompile ps qs rs hq ib tb rb t) (initialNat x)
    (paddedForestResult (n + ps.length * (ib + 1) + t * (m * (tb + 1))) rb i.val) = _
  simp only [paddedFinishedCompile, rawRun_append]
  rw [paddedForestCompile_correct rs _ _ rb hr _ (paddedPreparedRead_bound ps hp qs hq ib tb t) i.val i.isLt]
  have he : (fun j => rawRun
      (paddedIterationCompile qs hq tb t (fun k => paddedForestResult n ib k.val)
        (n + ps.length * (ib + 1)))
      (rawRun (paddedForestCompile (fun k => k.val) n ib ps) (initialNat x))
      (paddedPreparedRead ps qs hq ib tb t j)) =
      forestAdvance qs hq t (forestEvaluate ps hp x) := by
    funext j
    rw [paddedPreparedRead, paddedIterationCompile_correct qs hq tb ht]
    · have hs : (fun k : Fin m => rawRun (paddedForestCompile (fun a => a.val) n ib ps)
          (initialNat x) (paddedForestResult n ib k.val)) = forestEvaluate ps hp x := by
        funext k
        rw [paddedForestCompile_correct ps _ n ib hi _ (fun a => a.isLt) k.val (by simpa [hp] using k.isLt)]
        change (ps[k.val]).eval (fun a => initialNat x a.val) = (ps[k.val]).eval x
        congr 1
        funext a
        simp [initialNat]
      rw [hs]
    · intro k
      exact (paddedForestResult_bound n ib ps.length k.val (by simpa [hp] using k.isLt)).2
  rw [he]

theorem paddedFinishedCircuit_quantum_clean (ps : List (Formula (Fin n))) (hp : ps.length = m)
    (qs rs : List (Formula (Fin m))) (hq : qs.length = m) (ib tb rb t : Nat)
    (hi : ∀ p ∈ ps, p.size ≤ ib) (ht : ∀ p ∈ qs, p.size ≤ tb) (hr : ∀ p ∈ rs, p.size ≤ rb) (x : Bits n) :
    quantumRun (paddedFinishedCircuit ps hp qs rs hq ib tb rb t hi ht hr).reversible
      (basis (inputMemory x, fun _ => false)) =
      basis (inputMemory x, fun i => (rs[i.val]).eval (forestAdvance qs hq t (forestEvaluate ps hp x))) := by
  have he : (paddedFinishedCircuit ps hp qs rs hq ib tb rb t hi ht hr).eval x =
      (fun i => (rs[i.val]).eval (forestAdvance qs hq t (forestEvaluate ps hp x))) :=
    funext (paddedFinishedCircuit_eval ps hp qs rs hq ib tb rb t hi ht hr x)
  simpa only [he] using (paddedFinishedCircuit ps hp qs rs hq ib tb rb t hi ht hr).quantum_clean_correct x

end ShiReversibleFormula
