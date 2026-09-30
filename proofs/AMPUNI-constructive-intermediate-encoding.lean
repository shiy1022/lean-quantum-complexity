import «AMPUNI-encoding-size»
import «AMPUNI-intermediate-bounds»
import «AMPUNI-constructive-family»

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiQMAConstructiveSchedule
open ShiShallow ShiClassQMA ShiClassQMAU ShiQMAErrorIteration
  ShiQMAVariableRounds Polynomial

/-- The final constructive verifier bounds every earlier round by monotonicity. -/
theorem constructive_intermediate_resources_polyBounded (F : QMAFamily)
    (p : Polynomial ℕ) (hF : ShiBQP.PolyBounded F.toFamily) :
    ∃ B : Polynomial ℕ,
      ∀ (n r : Nat), r ≤ rounds p n →
        depth ((iter F r).circ n) ≤ B.eval n ∧
        (iter F r).wit n + (iter F r).anc n ≤ B.eval n := by
  obtain ⟨B, hdepth, hwires⟩ := constructiveFamily_polyBounded F p hF
  refine ⟨B, ?_⟩
  intro n r hr
  have hdfinal : depth ((iter F (rounds p n)).circ n) ≤ B.eval n := hdepth n
  have hwfinal : (iter F (rounds p n)).wit n +
      (iter F (rounds p n)).anc n ≤ B.eval n := hwires n
  constructor
  · exact (iter_depth_mono F n r _ hr).trans hdfinal
  · have hwm := iter_wit_mono F n r _ hr
    have ham := iter_anc_mono F n r _ hr
    omega

/-- Every intermediate encoding has one shared polynomial length bound. -/
theorem constructive_intermediate_encoded_length_polyBounded (F : QMAFamily)
    (p : Polynomial ℕ)
    (hwell : ShiBQP.WellFormed F.toFamily)
    (hpoly : ShiBQP.PolyBounded F.toFamily) :
    ∃ Q : Polynomial ℕ,
      ∀ (n r : Nat), r ≤ rounds p n →
        (encQMAFamilyAt (iter F r) n).length ≤ Q.eval n := by
  obtain ⟨B, hB⟩ := constructive_intermediate_resources_polyBounded F p hpoly
  let W : Polynomial ℕ := X + B + 1
  let Q : Polynomial ℕ :=
    C 4 + C 2 * W + C 2 * B + B * W * (C 2 * W + C 6)
  have hW (n : Nat) : W.eval n = n + B.eval n + 1 := by
    simp [W, eval_add, eval_X, eval_C]
  have hQ (n : Nat) :
      Q.eval n = 4 + 2 * W.eval n + 2 * B.eval n +
        B.eval n * W.eval n * (2 * W.eval n + 6) := by
    simp [Q, eval_add, eval_mul, eval_C]
  refine ⟨Q, ?_⟩
  intro n r hr
  obtain ⟨hdepth, htotal⟩ := hB n r hr
  have hwidth :
      n + (iter F r).wit n + (iter F r).anc n + 1 ≤ W.eval n := by
    rw [hW]
    omega
  have htwo :
      2 * (n + (iter F r).wit n + (iter F r).anc n + 1) + 6 ≤
        2 * W.eval n + 6 := by omega
  have hmul :
      depth ((iter F r).circ n) *
          (n + (iter F r).wit n + (iter F r).anc n + 1) *
          (2 * (n + (iter F r).wit n + (iter F r).anc n + 1) + 6) ≤
        B.eval n * W.eval n * (2 * W.eval n + 6) :=
    Nat.mul_le_mul (Nat.mul_le_mul hdepth hwidth) htwo
  calc
    (encQMAFamilyAt (iter F r) n).length ≤
        4 + 2 * (n + (iter F r).wit n + (iter F r).anc n + 1) +
          2 * depth ((iter F r).circ n) +
          depth ((iter F r).circ n) *
            (n + (iter F r).wit n + (iter F r).anc n + 1) *
            (2 * (n + (iter F r).wit n + (iter F r).anc n + 1) + 6) :=
      encoded_length_le_width_depth (iter F r) (iter_wellFormed F r hwell) n
    _ ≤ Q.eval n := by
      rw [hQ]
      omega

/-- Every call to the one-round transformer receives a polynomial-size input. -/
theorem constructive_intermediate_transform_inputs_polyBounded (F : QMAFamily)
    (p : Polynomial ℕ)
    (hwell : ShiBQP.WellFormed F.toFamily)
    (hpoly : ShiBQP.PolyBounded F.toFamily) :
    ∃ Q : Polynomial ℕ,
      ∀ (n r : Nat), r ≤ rounds p n →
        (ShiBQP.encNat n ++ encQMAFamilyAt (iter F r) n).length ≤ Q.eval n := by
  obtain ⟨B, hB⟩ := constructive_intermediate_encoded_length_polyBounded F p hwell hpoly
  refine ⟨X + 1 + B, ?_⟩
  intro n r hr
  have h := hB n r hr
  simp only [List.length_append]
  have hnat : (ShiBQP.encNat n).length = n + 1 := by
    simp [ShiBQP.encNat]
  rw [hnat]
  simpa [eval_add, eval_X, eval_C] using Nat.add_le_add_left h (n + 1)

end ShiQMAConstructiveSchedule


