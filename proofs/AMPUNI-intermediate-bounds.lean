import «AMPUNI-variable-resources»

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiQMAVariableRounds
open ShiShallow ShiClassQMA ShiQMAErrorIteration

/-- Later rounds have no smaller witness register. -/
theorem iter_wit_mono (F : QMAFamily) (n r s : Nat) (hrs : r ≤ s) :
    (iter F r).wit n ≤ (iter F s).wit n := by
  rw [iter_wit, iter_wit]
  exact Nat.mul_le_mul_right _ (pow_le_pow_right₀ (by decide : (1 : Nat) ≤ 3) hrs)

/-- Later rounds have no fewer ancillas. -/
theorem iter_anc_mono (F : QMAFamily) (n r s : Nat) (hrs : r ≤ s) :
    (iter F r).anc n ≤ (iter F s).anc n := by
  have hr := iter_anc_identity F r n
  have hs := iter_anc_identity F s n
  have hp := pow_le_pow_right₀ (by decide : (1 : Nat) ≤ 3) hrs
  have hm := Nat.mul_le_mul_right (2 * F.anc n + 2 * n + 3) hp
  omega

/-- Later rounds have no smaller circuit depth. -/
theorem iter_depth_mono (F : QMAFamily) (n r s : Nat) (hrs : r ≤ s) :
    depth ((iter F r).circ n) ≤ depth ((iter F s).circ n) := by
  have hr := iter_depth_identity F r n
  have hs := iter_depth_identity F s n
  have hp := pow_le_pow_right₀ (by decide : (1 : Nat) ≤ 3) hrs
  have hm := Nat.mul_le_mul_right (2 * depth (F.circ n) + 113) hp
  omega

/-- A single polynomial bounds resources of every intermediate verifier. -/
theorem all_intermediate_resources_polyBounded (F : QMAFamily)
    (p : Polynomial ℕ) (hF : ShiBQP.PolyBounded F.toFamily) :
    ∃ B : Polynomial ℕ,
      ∀ (n r : Nat), r ≤ roundsFor (p.eval n) →
        depth ((iter F r).circ n) ≤ B.eval n ∧
        (iter F r).wit n + (iter F r).anc n ≤ B.eval n := by
  obtain ⟨B, hdepth, hwires⟩ := polynomialFamily_polyBounded F p hF
  refine ⟨B, ?_⟩
  intro n r hr
  have hdfinal : depth ((iter F (roundsFor (p.eval n))).circ n) ≤ B.eval n :=
    hdepth n
  have hwfinal : (iter F (roundsFor (p.eval n))).wit n +
      (iter F (roundsFor (p.eval n))).anc n ≤ B.eval n :=
    hwires n
  constructor
  · exact (iter_depth_mono F n r _ hr).trans hdfinal
  · have hwm := iter_wit_mono F n r _ hr
    have ham := iter_anc_mono F n r _ hr
    omega

end ShiQMAVariableRounds

#print axioms ShiQMAVariableRounds.all_intermediate_resources_polyBounded
