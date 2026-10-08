import ReversiblePaddedForest
import ReversibleForestIteration

set_option autoImplicit false
namespace ShiReversibleFormula
open ShiReversible
variable {n : Nat}

def paddedIterationCompile (ps : List (Formula (Fin n))) (hl : ps.length = n) (bound : Nat) :
    Nat → (Fin n → Nat) → Nat → List RawAssignment
  | 0, _, _ => []
  | t + 1, inputs, base => paddedForestCompile inputs base bound ps ++
      paddedIterationCompile ps hl bound t (fun i => paddedForestResult base bound i.val)
        (base + n * (bound + 1))

def paddedIterationRead (ps : List (Formula (Fin n))) (hl : ps.length = n) (bound : Nat) :
    Nat → (Fin n → Nat) → Nat → Fin n → Nat
  | 0, inputs, _ => inputs
  | t + 1, _, base => paddedIterationRead ps hl bound t
      (fun i => paddedForestResult base bound i.val) (base + n * (bound + 1))

/-- Every nonempty time slice has a directly calculated output address. -/
theorem paddedIterationRead_succ (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (bound t : Nat) (inputs : Fin n → Nat) (base : Nat) (i : Fin n) :
    paddedIterationRead ps hl bound (t + 1) inputs base i =
      base + t * (n * (bound + 1)) + i.val * (bound + 1) + bound := by
  induction t generalizing inputs base with
  | zero => simp [paddedIterationRead, paddedForestResult]
  | succ t ih =>
      change paddedIterationRead ps hl bound (t + 1)
        (fun j => paddedForestResult base bound j.val) (base + n * (bound + 1)) i = _
      rw [ih]
      ring

@[simp] theorem paddedIterationCompile_length (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound) (t : Nat) (inputs : Fin n → Nat) (base : Nat) :
    (paddedIterationCompile ps hl bound t inputs base).length = t * (n * (bound + 1)) := by
  induction t generalizing inputs base with
  | zero => simp [paddedIterationCompile]
  | succ t ih =>
      simp [paddedIterationCompile, paddedForestCompile_length ps inputs base bound h, hl,
        ih, Nat.succ_mul, Nat.add_comm]

theorem paddedIterationCompile_targets (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound) (t : Nat) (inputs : Fin n → Nat) (base : Nat) :
    (paddedIterationCompile ps hl bound t inputs base).map RawAssignment.target =
      List.range' base (t * (n * (bound + 1))) := by
  induction t generalizing inputs base with
  | zero => simp [paddedIterationCompile]
  | succ t ih =>
      simp [paddedIterationCompile, paddedForestCompile_targets ps inputs base bound h, hl,
        ih, Nat.succ_mul, Nat.add_comm]

theorem paddedIterationCompile_topological (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound) (t : Nat) (inputs : Fin n → Nat)
    (base : Nat) (hin : ∀ i, inputs i < base) :
    ∀ a ∈ paddedIterationCompile ps hl bound t inputs base, a.Topological := by
  induction t generalizing inputs base with
  | zero => simp [paddedIterationCompile]
  | succ t ih =>
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact paddedForestCompile_topological ps inputs base bound h hin a ha
      · exact ih _ _ (fun i => by
          simpa only [hl] using (paddedForestResult_bound base bound ps.length i.val
            (by simpa [hl] using i.isLt)).2) a ha

theorem paddedIterationRead_bound (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (bound t : Nat) (inputs : Fin n → Nat) (base : Nat) (hin : ∀ i, inputs i < base) (i : Fin n) :
    paddedIterationRead ps hl bound t inputs base i < base + t * (n * (bound + 1)) := by
  induction t generalizing inputs base with
  | zero => simpa [paddedIterationRead] using hin i
  | succ t ih =>
      have he := ih (fun j => paddedForestResult base bound j.val) (base + n * (bound + 1))
        (fun j => by simpa only [hl] using
          (paddedForestResult_bound base bound ps.length j.val (by simpa [hl] using j.isLt)).2)
      simpa [paddedIterationRead, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

theorem paddedIterationCompile_correct (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound) (t : Nat) (inputs : Fin n → Nat)
    (base : Nat) (s : Nat → Bool) (hin : ∀ i, inputs i < base) (i : Fin n) :
    rawRun (paddedIterationCompile ps hl bound t inputs base) s
      (paddedIterationRead ps hl bound t inputs base i) =
      forestAdvance ps hl t (fun j => s (inputs j)) i := by
  induction t generalizing inputs base s with
  | zero => rfl
  | succ t ih =>
      simp only [paddedIterationCompile, rawRun_append, paddedIterationRead, forestAdvance]
      rw [ih _ _ _ (fun j => by simpa only [hl] using
        (paddedForestResult_bound base bound ps.length j.val (by simpa [hl] using j.isLt)).2)]
      have he : (fun j : Fin n => rawRun (paddedForestCompile inputs base bound ps) s
          (paddedForestResult base bound j.val)) = forestStep ps hl (fun j => s (inputs j)) := by
        funext j
        exact paddedForestCompile_correct ps inputs base bound h s hin j.val (by simpa [hl] using j.isLt)
      rw [he]

theorem paddedIterationCompile_interval (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound) (t : Nat) (inputs : Fin n → Nat) (base : Nat)
    (a : RawAssignment) (ha : a ∈ paddedIterationCompile ps hl bound t inputs base) :
    base ≤ a.target ∧ a.target < base + t * (n * (bound + 1)) := by
  have ht : a.target ∈ List.range' base (t * (n * (bound + 1))) := by
    rw [← paddedIterationCompile_targets ps hl bound h t inputs base]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨j, hj, he⟩ := List.mem_range'.mp ht
  simp only [Nat.one_mul] at he
  omega

def paddedIterationCircuit (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound) (t : Nat) :
    SingleAssignmentCircuit n (t * (n * (bound + 1))) n := by
  let raw := paddedIterationCompile ps hl bound t (fun i => i.val) n
  have ht : ∀ a ∈ raw, a.target < n + t * (n * (bound + 1)) :=
    fun a ha => (paddedIterationCompile_interval ps hl bound h t _ n a ha).2
  have hp : ∀ a ∈ raw, a.Topological :=
    paddedIterationCompile_topological ps hl bound h t _ n (fun i => i.isLt)
  let nodes := boundProgram (n + t * (n * (bound + 1))) raw ht hp
  exact {
    nodes := nodes
    targets_distinct := by
      apply List.Nodup.of_map Fin.val
      simp only [List.map_map, Function.comp_def]
      change (nodes.map (fun a => a.target.val)).Nodup
      rw [boundProgram_targets, paddedIterationCompile_targets ps hl bound h t _ n]
      exact List.nodup_range' _
    targets_auxiliary := by
      intro b hb
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
      rw [RawAssignment.toAssignment_target]
      exact (paddedIterationCompile_interval ps hl bound h t _ n a.val a.property).1
    nodes_length := by
      simpa only [nodes, raw, boundProgram_length] using paddedIterationCompile_length ps hl bound h t _ n
    read := fun i => ⟨paddedIterationRead ps hl bound t (fun j => j.val) n i,
      paddedIterationRead_bound ps hl bound t _ n (fun j => j.isLt) i⟩ }

@[simp] theorem paddedIterationCircuit_eval (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound) (t : Nat) (x : Bits n) :
    (paddedIterationCircuit ps hl bound h t).eval x = forestAdvance ps hl t x := by
  funext i
  unfold paddedIterationCircuit SingleAssignmentCircuit.eval
  rw [← initialNat_restrict x, boundProgram_correct]
  change rawRun (paddedIterationCompile ps hl bound t (fun j => j.val) n) (initialNat x)
    (paddedIterationRead ps hl bound t (fun j => j.val) n i) = _
  rw [paddedIterationCompile_correct ps hl bound h t _ _ _ (fun j => j.isLt)]
  congr 2
  funext j
  simp [initialNat]

theorem paddedIterationCircuit_quantum_clean (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound) (t : Nat) (x : Bits n) :
    quantumRun (paddedIterationCircuit ps hl bound h t).reversible
      (basis (inputMemory x, fun _ => false)) =
      basis (inputMemory x, forestAdvance ps hl t x) := by
  simpa only [paddedIterationCircuit_eval] using (paddedIterationCircuit ps hl bound h t).quantum_clean_correct x

theorem paddedIterationCircuit_size (ps : List (Formula (Fin n))) (hl : ps.length = n)
    (bound : Nat) (h : ∀ p ∈ ps, p.size ≤ bound) (t : Nat) :
    (paddedIterationCircuit ps hl bound h t).reversible.length ≤ 4 * (t * (n * (bound + 1))) + n :=
  (paddedIterationCircuit ps hl bound h t).size_bound

end ShiReversibleFormula
