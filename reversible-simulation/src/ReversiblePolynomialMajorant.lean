import ReversibleMachineExecution
import ReversibleShiftedPower

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- A shifted power dominates every natural-coefficient clock, even at input zero. -/
theorem polynomial_shifted_power_bound (p : Polynomial Nat) (n : Nat) :
    p.eval n ≤ (n + (p.eval 1 + 1)) ^ (p.natDegree + 1) := by
  classical
  let b := n + (p.eval 1 + 1)
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hn : n ≤ b := by dsimp [b]; omega
  have hsum : p.eval n ≤ p.eval 1 * b ^ p.natDegree := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    have he : p.eval 1 = ∑ i ∈ p.support, p.coeff i := by
      simp [Polynomial.eval_eq_sum, Polynomial.sum_def]
    rw [he, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left hn i).trans
      (Nat.pow_le_pow_right hb (Polynomial.le_natDegree_of_mem_supp i hi))
  have hc : p.eval 1 ≤ b := by dsimp [b]; omega
  calc
    p.eval n ≤ p.eval 1 * b ^ p.natDegree := hsum
    _ ≤ b * b ^ p.natDegree := Nat.mul_le_mul_right _ hc
    _ = b ^ (p.natDegree + 1) := by rw [pow_succ]; ac_rfl

/-- Enlarging a proved clock preserves the same actual machine and output certificate. -/
noncomputable def enlargePolyClock {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f)
    (p : Polynomial Nat) (hp : ∀ n, M.time.eval n ≤ p.eval n) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f where
  tm := M.tm
  inputAlphabet := M.inputAlphabet
  outputAlphabet := M.outputAlphabet
  time := p
  outputsFun xs := {
    steps := (M.outputsFun xs).steps
    evals_in_steps := (M.outputsFun xs).evals_in_steps
    steps_le_m := (M.outputsFun xs).steps_le_m.trans (hp xs.length) }

/-- Every original computation has the same machine certified at a shifted-power budget. -/
theorem shifted_power_clock {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) :
    ∃ N : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f,
      N.tm = M.tm ∧ N.time = (Polynomial.X + Polynomial.C (M.time.eval 1 + 1)) ^ (M.time.natDegree + 1) := by
  let p := (Polynomial.X + Polynomial.C (M.time.eval 1 + 1)) ^ (M.time.natDegree + 1)
  have hp : ∀ n, M.time.eval n ≤ p.eval n := by
    intro n
    simpa [p] using polynomial_shifted_power_bound M.time n
  exact ⟨enlargePolyClock M p hp, rfl, rfl⟩

/-- The same original computation admits a clock with an actual polynomial-time unary printer. -/
theorem shifted_power_clock_printable {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) :
    ∃ N : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f,
      N.tm = M.tm ∧ Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
        (id : List Bool → List Bool) (fun xs => List.replicate (N.time.eval xs.length) true)) := by
  obtain ⟨N, hm, ht⟩ := shifted_power_clock M
  refine ⟨N, hm, ?_⟩
  rw [ht]
  simpa only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] using
    shiftedUnaryPower_polytime (M.time.eval 1 + 1) (M.time.natDegree + 1)

end ShiReversibleGenerator
