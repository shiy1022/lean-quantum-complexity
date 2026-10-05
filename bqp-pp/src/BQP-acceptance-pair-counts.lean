import «BQP-forward-amplitude»

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace BQPPaths
open ShiShallow BQPGates

def phaseDifference (a b : ℕ) : ℕ := (a + 8 - b % 8) % 8

def fiberCount {ι Ω : Type} [Fintype ι] [DecidableEq Ω]
    (Y : ι → Ω) (k : ι → ℕ) (y : Ω) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun q : ι × ι =>
    Y q.1 = y ∧ Y q.2 = y ∧ phaseDifference (k q.1) (k q.2) = d)).card

def endpointCount {ι Ω : Type} [Fintype ι] [DecidableEq Ω]
    (Y : ι → Ω) (k : ι → ℕ) (acc : Ω → Bool) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun q : ι × ι => acc (Y q.1) = true ∧ Y q.1 = Y q.2 ∧
    phaseDifference (k q.1) (k q.2) = d)).card

/-- There are at most `4^h` ordered pairs of `h`-bit witnesses. -/
theorem endpointCount_le {Ω : Type} [DecidableEq Ω] (h : ℕ)
    (Y : (Fin h → Bool) → Ω) (k : (Fin h → Bool) → ℕ) (acc : Ω → Bool) (d : ℕ) :
    endpointCount Y k acc d ≤ 4 ^ h := by
  unfold endpointCount
  calc
    _ ≤ (Finset.univ : Finset ((Fin h → Bool) × (Fin h → Bool))).card :=
      Finset.card_filter_le _ _
    _ = 2 ^ h * 2 ^ h := by simp [Fintype.card_fun]
    _ = 4 ^ h := by rw [← mul_pow]; norm_num

/-- The irrational coefficient bound follows from counts, with no assumed bound. -/
theorem endpoint_coefficient_bound {Ω : Type} [DecidableEq Ω] (h : ℕ)
    (Y : (Fin h → Bool) → Ω) (k : (Fin h → Bool) → ℕ) (acc : Ω → Bool) :
    ((endpointCount Y k acc 1 : ℤ) - endpointCount Y k acc 3).natAbs ≤ 4 ^ h := by
  have h₁ := endpointCount_le h Y k acc 1
  have h₃ := endpointCount_le h Y k acc 3
  omega

private theorem fiber_subtype_count {ι Ω : Type} [Fintype ι] [DecidableEq ι] [DecidableEq Ω]
    (Y : ι → Ω) (k : ι → ℕ) (y : Ω) (d : ℕ) :
    (Finset.univ.filter (fun q : {i // Y i = y} × {i // Y i = y} =>
      phaseDifference (k q.1.val) (k q.2.val) = d)).card = fiberCount Y k y d := by
  classical
  unfold fiberCount
  apply Finset.card_bij (fun q _ => (q.1.val, q.2.val))
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact ⟨q.1.property, q.2.property, hq⟩
  · intro q hq r hr he
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst he)
    · exact Subtype.ext (congrArg Prod.snd he)
  · intro q hq
    rcases (Finset.mem_filter.mp hq).2 with ⟨h₁, h₂, hd⟩
    refine ⟨(⟨q.1, h₁⟩, ⟨q.2, h₂⟩), ?_, rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hd

/-- The squared norm on each output fiber is expressed by its actual pair counts. -/
theorem fiber_norm {ι Ω : Type} [Fintype ι] [DecidableEq ι] [DecidableEq Ω]
    (Y : ι → Ω) (k : ι → ℕ) (y : Ω) :
    ‖∑ i ∈ Finset.univ.filter (fun i => Y i = y), omega ^ k i‖ ^ 2 =
      ((fiberCount Y k y 0 : ℝ) - (fiberCount Y k y 4 : ℝ)) +
        Real.sqrt 2 * ((fiberCount Y k y 1 : ℝ) - (fiberCount Y k y 3 : ℝ)) := by
  classical
  have hs := Finset.sum_subtype (F := inferInstance) (p := fun i : ι => Y i = y) (Finset.univ.filter (fun i : ι => Y i = y))
    (fun i => by simp) (fun i => omega ^ k i)
  have hr := (BQPChecked.reference12.2.1 {i : ι // Y i = y}
    (fun i => k i.val) omega rfl).2.2.2
  have hc := fun d => fiber_subtype_count Y k y d
  dsimp only [phaseDifference] at hc
  rw [hs]
  rw [← hc 0, ← hc 4, ← hc 1, ← hc 3]
  exact hr

/-- Sum the output fibers. Equal endpoints are essential; independent accepting
endpoints would count interference terms that are absent from quantum acceptance. -/
theorem amplitude_pair_count {ι Ω : Type} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω] (h : ℕ) (Y : ι → Ω) (k : ι → ℕ)
    (acc : Ω → Bool) (amp : Ω → ℂ)
    (hamp : ∀ y, amp y = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ h *
      ∑ i ∈ Finset.univ.filter (fun i => Y i = y), omega ^ k i) :
    (∑ y : Ω, if acc y = true then ‖amp y‖ ^ 2 else 0) =
      (1 / 2 : ℝ) ^ h *
        (((endpointCount Y k acc 0 : ℝ) - (endpointCount Y k acc 4 : ℝ)) +
          Real.sqrt 2 * ((endpointCount Y k acc 1 : ℝ) - (endpointCount Y k acc 3 : ℝ))) := by
  exact (BQPChecked.reference7 Ω ι acc h k Y amp omega (fiberCount Y k)
    (endpointCount Y k acc) (fun _ _ => rfl) (fun _ => rfl)
    BQPChecked.reference5.1 hamp (fiber_norm Y k)).2

/-- Integer pair-count representation of actual circuit acceptance, with no
assumed path decomposition, phase formula, or gate semantics. -/
theorem circuit_acceptance_pair_counts :
    ∃ (N : ∀ n : ℕ, List (Instr n) → ℕ)
      (Fwd : ∀ n : ℕ, List (Instr n) → Bits n → List Bool → Bits n)
      (Pf : ∀ n : ℕ, List (Instr n) → Bits n → List Bool → ZMod 8),
      (∀ (n : ℕ) (gs : List (Instr n)), N n gs =
        gs.countP (fun g => match g with | .h _ => true | _ => false)) ∧
      ∀ (n m : ℕ) (c : Layered (n + m)) (x : Bits n) (out : Fin (n + m)),
        let z := Fin.append x (fun _ : Fin m => false)
        let Y := fun w : Fin (N (n + m) c.flatten) → Bool => Fwd (n + m) c.flatten z (List.ofFn w)
        let k := fun w : Fin (N (n + m) c.flatten) → Bool => (Pf (n + m) c.flatten z (List.ofFn w)).val
        let C := endpointCount Y k (fun y => y out)
        acceptProb c x out = (1 / 2 : ℝ) ^ N (n + m) c.flatten *
          (((C 0 : ℝ) - (C 4 : ℝ)) + Real.sqrt 2 * ((C 1 : ℝ) - (C 3 : ℝ))) := by
  classical
  obtain ⟨N, Fwd, Pf, hcount, h⟩ := padded_input_amplitude
  refine ⟨N, Fwd, Pf, hcount, ?_⟩
  intro n m c x out
  dsimp only
  exact amplitude_pair_count (N (n + m) c.flatten)
    (fun w => Fwd (n + m) c.flatten (Fin.append x (fun _ : Fin m => false)) (List.ofFn w))
    (fun w => (Pf (n + m) c.flatten (Fin.append x (fun _ : Fin m => false)) (List.ofFn w)).val)
    (fun y => y out) (runLayered c (inputState x)) (h n m c x)

end BQPPaths
