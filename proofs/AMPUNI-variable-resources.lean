import «AMPUNI-variable-family»

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiQMAVariableRounds
open ShiShallow ShiClassQMA ShiQMAErrorIteration Polynomial

/-- The copy count is quadratically bounded even at target exponent zero. -/
theorem copies_roundsFor_le_all (m : Nat) :
    3 ^ roundsFor m ≤ 81 * (m + 1) ^ 2 := by
  by_cases hm : m = 0
  · subst m
    norm_num [roundsFor]
  · have hp : 0 < m := Nat.pos_of_ne_zero hm
    calc
      3 ^ roundsFor m ≤ 81 * m ^ 2 := copies_roundsFor_le m hp
      _ ≤ 81 * (m + 1) ^ 2 := by nlinarith

/-- At length `n`, the target exponent is `p.eval n`. -/
noncomputable def polynomialFamily (F : QMAFamily) (p : Polynomial ℕ) : QMAFamily :=
  varying F (fun n => roundsFor (p.eval n))

/-- The length-dependent family remains polynomially bounded. -/
theorem polynomialFamily_polyBounded (F : QMAFamily) (p : Polynomial ℕ)
    (hF : ShiBQP.PolyBounded F.toFamily) :
    ShiBQP.PolyBounded (polynomialFamily F p).toFamily := by
  obtain ⟨q, hdepth, hwires⟩ := hF
  let B : Polynomial ℕ := C 81 * (p + 1) ^ 2 * (q + 2 * X + C 116)
  have hB (n : Nat) :
      B.eval n = 81 * (p.eval n + 1) ^ 2 * (q.eval n + 2 * n + 116) := by
    simp [B, eval_mul, eval_pow, eval_add, eval_C, eval_X, mul_add, add_assoc]
  refine ⟨B, ?_, ?_⟩
  · intro n
    change depth ((iter F (roundsFor (p.eval n))).circ n) ≤ B.eval n
    have hq : depth (F.circ n) ≤ q.eval n := hdepth n
    have hc := copies_roundsFor_le_all (p.eval n)
    calc
      depth ((iter F (roundsFor (p.eval n))).circ n)
          ≤ 3 ^ roundsFor (p.eval n) * (depth (F.circ n) + 113) :=
            iter_depth_le F _ n
      _ ≤ 3 ^ roundsFor (p.eval n) * (q.eval n + 113) :=
            Nat.mul_le_mul_left _ (Nat.add_le_add_right hq _)
      _ ≤ 81 * (p.eval n + 1) ^ 2 * (q.eval n + 113) :=
            Nat.mul_le_mul_right _ hc
      _ ≤ B.eval n := by
        rw [hB]
        exact Nat.mul_le_mul_left _ (by omega)
  · intro n
    change (iter F (roundsFor (p.eval n))).wit n +
      (iter F (roundsFor (p.eval n))).anc n ≤ B.eval n
    have hq : F.wit n + F.anc n ≤ q.eval n := hwires n
    have hc := copies_roundsFor_le_all (p.eval n)
    calc
      (iter F (roundsFor (p.eval n))).wit n +
          (iter F (roundsFor (p.eval n))).anc n
          ≤ 3 ^ roundsFor (p.eval n) *
            (F.wit n + F.anc n + 2 * n + 3) :=
            iter_wit_add_anc_le F _ n
      _ ≤ 3 ^ roundsFor (p.eval n) * (q.eval n + 2 * n + 3) :=
            Nat.mul_le_mul_left _ (by omega)
      _ ≤ 81 * (p.eval n + 1) ^ 2 * (q.eval n + 2 * n + 3) :=
            Nat.mul_le_mul_right _ hc
      _ ≤ B.eval n := by
        rw [hB]
        exact Nat.mul_le_mul_left _ (by omega)

theorem polynomialFamily_wellFormed (F : QMAFamily) (p : Polynomial ℕ)
    (hF : ShiBQP.WellFormed F.toFamily) :
    ShiBQP.WellFormed (polynomialFamily F p).toFamily :=
  variable_wellFormed F _ hF

end ShiQMAVariableRounds

#print axioms ShiQMAVariableRounds.polynomialFamily_polyBounded
