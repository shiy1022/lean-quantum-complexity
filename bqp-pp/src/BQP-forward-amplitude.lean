import «BQP-path-correspondence»
import «BQP-path-fiber-sum»

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace BQPPaths
open ShiShallow BQPGates

/-- Interpret a witness list as a fixed-length bit vector. -/
def witnessFn (h : ℕ) (w : List Bool) : Fin h → Bool := fun i => w.getD i.val false

theorem witnessFn_ofFn {h : ℕ} (b : Fin h → Bool) : witnessFn h (List.ofFn b) = b := by
  funext i
  have hi : (i : ℕ) < (List.ofFn b).length := by simp
  have he : (List.ofFn b).getD (i : ℕ) false = (List.ofFn b)[(i : ℕ)]'hi :=
    (List.getElem_eq_getD false).symm
  rw [witnessFn, he]
  simp

theorem ofFn_witnessFn {h : ℕ} (w : List Bool) (hw : w.length = h) :
    List.ofFn (witnessFn h w) = w := by
  subst h
  have he : witnessFn w.length w = fun i : Fin w.length => w[(i : ℕ)] := by
    funext i
    exact (List.getElem_eq_getD false).symm
  rw [he]
  exact List.ofFn_getElem

/-- Transfer a backward amplitude sum through a length-preserving path bijection.
The scalar and phase are derived separately from the real circuit semantics. -/
theorem reindex_amplitude {Ω : Type} [DecidableEq Ω]
    (h : ℕ) (A : Ω → List Bool → ℂ) (P : Ω → List Bool → Ω)
    (Fwd : List Bool → Ω) (Bk : List Bool → List Bool) (Pf : List Bool → ZMod 8)
    (y z : Ω) (q ω : ℂ)
    (hlen : ∀ w, (Bk w).length = h)
    (hback : ∀ w, P (Fwd w) (Bk w) = z)
    (hinj : ∀ u v : List Bool, u.length = h → v.length = h →
      Fwd u = Fwd v → Bk u = Bk v → u = v)
    (hsurj : ∀ b : List Bool, b.length = h → P y b = z →
      ∃ w : List Bool, w.length = h ∧ Fwd w = y ∧ Bk w = b)
    (hphase : ∀ w, A (Fwd w) (Bk w) = q * ω ^ (Pf w).val) :
    (∑ b : Fin h → Bool, A y (List.ofFn b) *
      (if P y (List.ofFn b) = z then 1 else 0)) =
    q * ∑ w ∈ Finset.univ.filter (fun w : Fin h → Bool => Fwd (List.ofFn w) = y),
      ω ^ (Pf (List.ofFn w)).val := by
  classical
  have hf := fiber_sum (fun w : Fin h → Bool => Fwd (List.ofFn w))
    (fun w => witnessFn h (Bk (List.ofFn w))) (fun b => P y (List.ofFn b)) y z
    (by
      intro w hw
      rw [ofFn_witnessFn _ (hlen _), ← hw]
      exact hback _)
    (by
      intro u v hu hv huv
      apply List.ofFn_injective
      apply hinj _ _ (by simp) (by simp) (hu.trans hv.symm)
      have he := congrArg List.ofFn huv
      have hu' := ofFn_witnessFn (Bk (List.ofFn u)) (hlen _)
      have hv' := ofFn_witnessFn (Bk (List.ofFn v)) (hlen _)
      simpa only [hu', hv'] using he)
    (by
      intro b hb
      obtain ⟨w, hw, hwy, hwb⟩ := hsurj (List.ofFn b) (by simp) hb
      refine ⟨witnessFn h w, ?_, ?_⟩
      · simpa only [ofFn_witnessFn w hw] using hwy
      · rw [ofFn_witnessFn w hw, hwb, witnessFn_ofFn])
    (fun b => A y (List.ofFn b))
  calc
    _ = ∑ b ∈ Finset.univ.filter (fun b : Fin h → Bool => P y (List.ofFn b) = z),
        A y (List.ofFn b) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp
    _ = _ := hf
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      have hy := (Finset.mem_filter.mp hw).2
      rw [ofFn_witnessFn _ (hlen _), ← hy, hphase]

/-- For actual layered circuits, forward witnesses enumerate the amplitude at
each output, with the same phase attached to a witness at every occurrence. -/
theorem forward_amplitude :
    ∃ (N : ∀ n : ℕ, List (Instr n) → ℕ)
      (Fwd : ∀ n : ℕ, List (Instr n) → Bits n → List Bool → Bits n)
      (Pf : ∀ n : ℕ, List (Instr n) → Bits n → List Bool → ZMod 8),
      (∀ (n : ℕ) (gs : List (Instr n)), N n gs =
        gs.countP (fun g => match g with | .h _ => true | _ => false)) ∧
      ∀ (n : ℕ) (c : Layered n) (z y : Bits n),
        runLayered c (fun t => if t = z then 1 else 0) y =
          ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ N n c.flatten *
            ∑ w ∈ Finset.univ.filter
              (fun w : Fin (N n c.flatten) → Bool => Fwd n c.flatten z (List.ofFn w) = y),
              omega ^ (Pf n c.flatten z (List.ofFn w)).val := by
  classical
  obtain ⟨N, A, P, Fwd, Bk, Wit, Pf, hcount, hsum, hlen, hback, hrec, hbij, hphase⟩ :=
    forward_backward_correspondence
  refine ⟨N, Fwd, Pf, hcount, ?_⟩
  intro n c z y
  rw [hsum]
  apply reindex_amplitude (N n c.flatten) (A n c.flatten) (P n c.flatten)
    (Fwd n c.flatten z) (Bk n c.flatten z) (Pf n c.flatten z) y z
    (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ N n c.flatten) omega
    (hlen n c.flatten z) (hback n c.flatten z)
  · intro u v hu hv huv hB
    calc
      u = Wit n c.flatten (Fwd n c.flatten z u) (Bk n c.flatten z u) :=
        (hrec n c.flatten z u hu).symm
      _ = Wit n c.flatten (Fwd n c.flatten z v) (Bk n c.flatten z v) := by rw [huv, hB]
      _ = v := hrec n c.flatten z v hv
  · intro b hb hP
    exact ((hbij n c.flatten y z b hb).mp hP).exists
  · exact hphase n c.flatten z

/-- Specialization to the exact padded input state in the BQP definition. -/
theorem padded_input_amplitude :
    ∃ (N : ∀ n : ℕ, List (Instr n) → ℕ)
      (Fwd : ∀ n : ℕ, List (Instr n) → Bits n → List Bool → Bits n)
      (Pf : ∀ n : ℕ, List (Instr n) → Bits n → List Bool → ZMod 8),
      (∀ (n : ℕ) (gs : List (Instr n)), N n gs =
        gs.countP (fun g => match g with | .h _ => true | _ => false)) ∧
      ∀ (n m : ℕ) (c : Layered (n + m)) (x : Bits n) (y : Bits (n + m)),
        runLayered c (inputState x) y =
          ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ N (n + m) c.flatten *
            ∑ w ∈ Finset.univ.filter
              (fun w : Fin (N (n + m) c.flatten) → Bool =>
                Fwd (n + m) c.flatten (Fin.append x (fun _ : Fin m => false)) (List.ofFn w) = y),
              omega ^ (Pf (n + m) c.flatten (Fin.append x (fun _ : Fin m => false)) (List.ofFn w)).val := by
  classical
  obtain ⟨N, Fwd, Pf, hcount, h⟩ := forward_amplitude
  refine ⟨N, Fwd, Pf, hcount, ?_⟩
  intro n m c x y
  have hi : inputState (m := m) x =
      fun t => if t = Fin.append x (fun _ : Fin m => false) then (1 : ℂ) else 0 := by
    funext t
    exact inputState_delta x t
  rw [hi]
  exact h (n + m) c (Fin.append x (fun _ : Fin m => false)) y

end BQPPaths
