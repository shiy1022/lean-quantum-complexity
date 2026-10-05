import «AMPUNI-constructive-valid-polynomial»
import «AMPUNI-total-polynomial-clocked-bounds»
import «AMPUNI-total-polynomial-function»
import «AMPUNI-polynomial-eval-upper»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option synthInstance.maxSize 100000
noncomputable section
namespace ShiTMConstructiveConcrete
open ShiClassQMA ShiClassQMAU ShiQMAConstructiveSchedule

private theorem eval_le_monomial_of_le (P : Polynomial ℕ) (n m : Nat) (h : n ≤ m) :
    P.eval n ≤ P.eval 1 * (m + 1) ^ (P.natDegree + 1) := by
  have hp : (n + 1) ^ P.natDegree ≤ (m + 1) ^ (P.natDegree + 1) :=
    (Nat.pow_le_pow_left (by omega) P.natDegree).trans
      (Nat.pow_le_pow_right (by omega) (Nat.le_succ P.natDegree))
  exact (ShiQMAPolynomialBound.eval_le_coeffSum_mul P n).trans
    (Nat.mul_le_mul_left _ hp)

/-- A total polynomial-time string transformer computes every verifier in
the constructive amplification schedule. Its fixed clock may depend on
the original family's resource bound and on the target polynomial. -/
theorem constructive_encoding_transducer (F : QMAFamily) (p : Polynomial ℕ)
    (hwell : ShiBQP.WellFormed F.toFamily)
    (hpoly : ShiBQP.PolyBounded F.toFamily) :
    ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
      ∀ n : Nat,
        g (ShiBQP.encNat n ++ encQMAFamilyAt F n) =
          encQMAFamilyAt (constructiveFamily F p) n := by
  obtain ⟨k, T, hT⟩ := constructive_valid_polyBounded F p hwell hpoly
  let tm := finiteMachine k p
  let ein : Bool ≃ tm.Γ tm.k₀ := Equiv.refl Bool
  let full := ShiTMTotalPolynomialClocked.finiteMachine tm ein T.natDegree (T.eval 1)
  obtain ⟨P, hP⟩ := ShiTMTotalPolynomialClocked.total_polynomial
    tm ein T.natDegree (T.eval 1)
  have hall : ∀ xs : List Bool, ∃ ys : List Bool,
      Nonempty (Turing.TM2OutputsInTime full (xs.map (Equiv.refl Bool).symm)
        (some (ys.map (Equiv.refl Bool).symm)) (P.eval xs.length)) := by
    intro xs
    obtain ⟨ys, hy⟩ := hP xs
    have hin : xs.map (Equiv.refl Bool).symm = xs := List.map_id xs
    have hout : ys.map (Equiv.refl Bool).symm = ys := List.map_id ys
    have heq := congrArg₂ (fun (a b : List Bool) =>
      Nonempty (Turing.TM2OutputsInTime full a (some b) (P.eval xs.length))) hin hout
    exact ⟨ys, heq.mpr hy⟩
  obtain ⟨g, hg, hunique⟩ := ShiTMTotalFunction.function_of_total_polynomial full
    (Equiv.refl Bool) (Equiv.refl Bool) P hall
  obtain ⟨Q, hQ⟩ := ShiTMTotalPolynomialClocked.valid_run_polynomial
    tm ein T.natDegree (T.eval 1)
  refine ⟨g, hg, ?_⟩
  intro n
  let xs := ShiBQP.encNat n ++ encQMAFamilyAt F n
  let ys := encQMAFamilyAt (constructiveFamily F p) n
  obtain ⟨steps, v, S, hr, hout, hsteps⟩ := hT n
  have hn : n ≤ xs.length := by
    simp only [xs, List.length_append]
    have hlen : (ShiBQP.encNat n).length = n + 1 := by simp [ShiBQP.encNat]
    rw [hlen]
    omega
  have hb := hsteps.trans (eval_le_monomial_of_le T n xs.length hn)
  have hin : xs.map ein = xs := List.map_id xs
  have hr' : (ShiTMSubroutine.run tm.m)^[steps]
      (some (Turing.initList tm (xs.map ein))) = some ⟨none, v, S⟩ := by
    exact (congrArg
      (fun input : List (tm.Γ tm.k₀) =>
        (ShiTMSubroutine.run tm.m)^[steps] (some (Turing.initList tm input))) hin).trans hr
  have hf := hQ xs steps v S hr' hb
  have hf' : Nonempty (Turing.TM2OutputsInTime full xs (some ys) (Q.eval xs.length)) := by
    have hout' : S tm.k₁ = ys := hout
    exact (congrArg (fun output : List Bool =>
      Nonempty (Turing.TM2OutputsInTime full xs (some output) (Q.eval xs.length))) hout').mp hf
  apply hunique xs ys (Q.eval xs.length)
  have hin' : xs.map (Equiv.refl Bool).symm = xs := List.map_id xs
  have hout' : ys.map (Equiv.refl Bool).symm = ys := List.map_id ys
  have heq := congrArg₂ (fun (a b : List Bool) =>
    Nonempty (Turing.TM2OutputsInTime full a (some b) (Q.eval xs.length))) hin' hout'
  exact heq.mpr hf'

end ShiTMConstructiveConcrete
