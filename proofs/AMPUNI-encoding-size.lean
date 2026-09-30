import «AMPUNI-variable-resources»
import Theorems.Thm_ShiTM_encoding_length_formulas_and_size_bound

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiQMAVariableRounds
open ShiShallow ShiClassQMA ShiClassQMAU Polynomial

/-- Encoding length in terms of circuit width and depth. -/
theorem encoded_length_le_width_depth (F : QMAFamily)
    (hF : ShiBQP.WellFormed F.toFamily) (n : Nat) :
    (encQMAFamilyAt F n).length ≤
      4 + 2 * (n + F.wit n + F.anc n + 1) +
        2 * depth (F.circ n) +
        depth (F.circ n) * (n + F.wit n + F.anc n + 1) *
          (2 * (n + F.wit n + F.anc n + 1) + 6) := by
  obtain ⟨hnat, _, _, _, _, _, _, _, _, _, _, _, hcirc⟩ :=
    ShiTM.encoding_length_formulas_and_size_bound
  have hwidth :
      n + F.wit n + F.anc n + 1 =
        n + (F.wit n + (F.anc n + 1)) := by omega
  have hcode := hcirc _ (F.circ n) (hF n)
  have hheaders :
      (encQMAFamilyAt F n).length =
        F.wit n + F.anc n + (F.out n : Nat) + 3 +
          (ShiBQP.encCirc (F.circ n)).length := by
    simp [encQMAFamilyAt, hnat]
    omega
  rw [hheaders]
  have hcode' :
      (ShiBQP.encCirc (F.circ n)).length ≤
        2 * depth (F.circ n) + 1 +
          depth (F.circ n) * (n + F.wit n + F.anc n + 1) *
            (2 * (n + F.wit n + F.anc n + 1) + 6) := by
    simpa only [hwidth] using hcode
  have hout : (F.out n : Nat) < n + F.wit n + F.anc n + 1 := by
    simpa only [hwidth] using (F.out n).isLt
  omega

/-- Any well-formed, polynomially bounded verifier has polynomial-size full encodings. -/
theorem encoded_length_polyBounded (F : QMAFamily)
    (hwell : ShiBQP.WellFormed F.toFamily)
    (hpoly : ShiBQP.PolyBounded F.toFamily) :
    ∃ Q : Polynomial ℕ,
      ∀ n : Nat, (encQMAFamilyAt F n).length ≤ Q.eval n := by
  obtain ⟨q, hd, hw⟩ := hpoly
  let W : Polynomial ℕ := X + q + 1
  let Q : Polynomial ℕ :=
    C 4 + C 2 * W + C 2 * q + q * W * (C 2 * W + C 6)
  have hW (n : Nat) : W.eval n = n + q.eval n + 1 := by
    simp [W, eval_add, eval_X, eval_C]
  have hQ (n : Nat) :
      Q.eval n = 4 + 2 * W.eval n + 2 * q.eval n +
        q.eval n * W.eval n * (2 * W.eval n + 6) := by
    simp [Q, eval_add, eval_mul, eval_C]
  refine ⟨Q, ?_⟩
  intro n
  have htotal : F.wit n + F.anc n ≤ q.eval n := hw n
  have hdepth : depth (F.circ n) ≤ q.eval n := hd n
  have hwidth : n + F.wit n + F.anc n + 1 ≤ W.eval n := by
    rw [hW]
    omega
  have htwo :
      2 * (n + F.wit n + F.anc n + 1) + 6 ≤
        2 * W.eval n + 6 := by omega
  have hmul :
      depth (F.circ n) * (n + F.wit n + F.anc n + 1) *
          (2 * (n + F.wit n + F.anc n + 1) + 6) ≤
        q.eval n * W.eval n * (2 * W.eval n + 6) :=
    Nat.mul_le_mul
      (Nat.mul_le_mul hdepth hwidth) htwo
  calc
    (encQMAFamilyAt F n).length ≤
        4 + 2 * (n + F.wit n + F.anc n + 1) +
          2 * depth (F.circ n) +
          depth (F.circ n) * (n + F.wit n + F.anc n + 1) *
            (2 * (n + F.wit n + F.anc n + 1) + 6) :=
      encoded_length_le_width_depth F hwell n
    _ ≤ Q.eval n := by
      rw [hQ]
      omega

theorem polynomialFamily_encoded_length_polyBounded (F : QMAFamily)
    (p : Polynomial ℕ)
    (hwell : ShiBQP.WellFormed F.toFamily)
    (hpoly : ShiBQP.PolyBounded F.toFamily) :
    ∃ Q : Polynomial ℕ,
      ∀ n : Nat, (encQMAFamilyAt (polynomialFamily F p) n).length ≤ Q.eval n :=
  encoded_length_polyBounded _ (polynomialFamily_wellFormed F p hwell)
    (polynomialFamily_polyBounded F p hpoly)

end ShiQMAVariableRounds

#print axioms ShiQMAVariableRounds.polynomialFamily_encoded_length_polyBounded
