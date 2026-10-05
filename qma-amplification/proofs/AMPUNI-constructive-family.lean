import «AMPUNI-variable-resources»
import «AMPUNI-constructive-schedule»

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiQMAConstructiveSchedule
open ShiShallow ShiClassQMA ShiQMAVariableRounds Polynomial

/-- The verifier family using a round count computable from the input
length's binary logarithm and fixed constants belonging to `p`. -/
noncomputable def constructiveFamily (F : QMAFamily)
    (p : Polynomial ℕ) : QMAFamily :=
  varying F (rounds p)

theorem constructiveFamily_wellFormed (F : QMAFamily)
    (p : Polynomial ℕ) (hF : ShiBQP.WellFormed F.toFamily) :
    ShiBQP.WellFormed (constructiveFamily F p).toFamily :=
  variable_wellFormed F _ hF

/-- For fixed `p`, all wire counts and circuit depths remain bounded by a
natural-coefficient polynomial in the input length. -/
theorem constructiveFamily_polyBounded (F : QMAFamily)
    (p : Polynomial ℕ) (hF : ShiBQP.PolyBounded F.toFamily) :
    ShiBQP.PolyBounded (constructiveFamily F p).toFamily := by
  obtain ⟨q, hdepth, hwires⟩ := hF
  let Cc : ℕ :=
    3 ^ (Nat.log 2 (p.eval 1 + 1) + p.natDegree + 4)
  let B : Polynomial ℕ :=
    C Cc * (X + 1) ^ (2 * p.natDegree) *
      (q + 2 * X + C 116)
  have hB (n : ℕ) :
      B.eval n =
        Cc * (n + 1) ^ (2 * p.natDegree) *
          (q.eval n + 2 * n + 116) := by
    simp [B, eval_mul, eval_pow, eval_add, eval_C, eval_X,
      mul_add, add_assoc]
  refine ⟨B, ?_, ?_⟩
  · intro n
    change depth ((iter F (rounds p n)).circ n) ≤ B.eval n
    have hq : depth (F.circ n) ≤ q.eval n := hdepth n
    have hc := copies_rounds_le p n
    calc
      depth ((iter F (rounds p n)).circ n)
          ≤ 3 ^ rounds p n * (depth (F.circ n) + 113) :=
            iter_depth_le F _ n
      _ ≤ 3 ^ rounds p n * (q.eval n + 113) :=
            Nat.mul_le_mul_left _ (Nat.add_le_add_right hq _)
      _ ≤ Cc * (n + 1) ^ (2 * p.natDegree) *
            (q.eval n + 113) :=
            Nat.mul_le_mul_right _ hc
      _ ≤ B.eval n := by
        rw [hB]
        exact Nat.mul_le_mul_left _ (by omega)
  · intro n
    change (iter F (rounds p n)).wit n +
      (iter F (rounds p n)).anc n ≤ B.eval n
    have hq : F.wit n + F.anc n ≤ q.eval n := hwires n
    have hc := copies_rounds_le p n
    calc
      (iter F (rounds p n)).wit n +
          (iter F (rounds p n)).anc n
          ≤ 3 ^ rounds p n *
            (F.wit n + F.anc n + 2 * n + 3) :=
            iter_wit_add_anc_le F _ n
      _ ≤ 3 ^ rounds p n * (q.eval n + 2 * n + 3) :=
            Nat.mul_le_mul_left _ (by omega)
      _ ≤ Cc * (n + 1) ^ (2 * p.natDegree) *
            (q.eval n + 2 * n + 3) :=
            Nat.mul_le_mul_right _ hc
      _ ≤ B.eval n := by
        rw [hB]
        exact Nat.mul_le_mul_left _ (by omega)

end ShiQMAConstructiveSchedule
