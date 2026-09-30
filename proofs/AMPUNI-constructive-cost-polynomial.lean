import «AMPUNI-constructive-intermediate-encoding»
import «AMPUNI-constructive-round-bound»
import «AMPUNI-repeat-loop-cost-bound»

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiQMAConstructiveSchedule
open ShiClassQMA ShiClassQMAU ShiClassQMAAmpX ShiQMAVariableRounds Polynomial

/-- A single polynomial bounds the recursive controller cost for every
sequence of source runs satisfying the established quadratic call bound. -/
theorem constructive_preloadedCost_polyBounded (F : QMAFamily)
    (p : Polynomial ℕ) (C : Nat)
    (hwell : ShiBQP.WellFormed F.toFamily)
    (hpoly : ShiBQP.PolyBounded F.toFamily) :
    ∃ T : Polynomial ℕ, ∀ (n : Nat) (times : Nat → Nat),
      (∀ r, times r ≤ C *
        ((ShiBQP.encNat n ++ encQMAFamilyAt (iter F r) n).length + 1) ^ 2) →
      ShiTMRepeatController.preloadedCost n
        (fun r => (encQMAFamilyAt (ampFamilyX (iter F r)) n).length)
        times 0 (rounds p n - 1) ≤ T.eval n := by
  obtain ⟨Q, hQ⟩ :=
    constructive_intermediate_transform_inputs_polyBounded F p hwell hpoly
  obtain ⟨Rpoly, hR⟩ := rounds_polyBounded p
  let B : Polynomial ℕ :=
    Polynomial.C C * (Q + 1) ^ 2 + Polynomial.C 2 * (Q + 1) + X + 3
  let T : Polynomial ℕ := Rpoly * B + X + 2
  have hB (n : Nat) : B.eval n =
      C * (Q.eval n + 1) ^ 2 + 2 * (Q.eval n + 1) + n + 3 := by
    simp [B, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  have hT (n : Nat) : T.eval n =
      Rpoly.eval n * B.eval n + n + 2 := by
    simp [T, eval_add, eval_mul, eval_C, eval_X]
  refine ⟨T, ?_⟩
  intro n times htimes
  let R := rounds p n
  let q := R - 1
  have hpos : 0 < R := by
    simp [R, rounds, exponentBudget]
  have hq : q + 1 = R := by
    dsimp [q]
    omega
  have htb (i : Nat) (hi : i ≤ q) :
      times i ≤ C * (Q.eval n + 1) ^ 2 := by
    have hiR : i ≤ rounds p n := by
      dsimp [q, R] at hi
      omega
    have hlen := hQ n i hiR
    have hp :
        ((ShiBQP.encNat n ++ encQMAFamilyAt (iter F i) n).length + 1) ^ 2
          ≤ (Q.eval n + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    exact (htimes i).trans (Nat.mul_le_mul_left C hp)
  have hlb (i : Nat) (hi : i ≤ q) :
      (encQMAFamilyAt (ampFamilyX (iter F i)) n).length ≤ Q.eval n := by
    have hiR : i + 1 ≤ rounds p n := by
      dsimp [q, R] at hi
      omega
    have hlen := hQ n (i + 1) hiR
    simp only [List.length_append] at hlen
    simpa [iter] using (show
      (encQMAFamilyAt (iter F (i + 1)) n).length ≤ Q.eval n by omega)
  have hlin := ShiTMRepeatController.preloadedCost_le_linear
    n q (C * (Q.eval n + 1) ^ 2) (Q.eval n)
    (fun i => (encQMAFamilyAt (ampFamilyX (iter F i)) n).length)
    times htb hlb 0 q (by omega)
  have hround := hR n
  rw [hT, hB]
  have hmult : R *
      (C * (Q.eval n + 1) ^ 2 + 2 * (Q.eval n + 1) + n + 3) ≤
      Rpoly.eval n *
        (C * (Q.eval n + 1) ^ 2 + 2 * (Q.eval n + 1) + n + 3) :=
    Nat.mul_le_mul_right _ hround
  rw [show R = q + 1 from hq.symm] at hmult
  exact hlin.trans (Nat.add_le_add_right (Nat.add_le_add_right hmult n) 2)

end ShiQMAConstructiveSchedule
