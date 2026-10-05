import «BQP-counting-core»

set_option autoImplicit false
namespace BQPCounting
open ShiClassPP

/-- Split exact-length witnesses into the two possible first bits. -/
theorem count_prefix (R : List Bool × List Bool → Bool) (x : List Bool) (m : ℕ) :
    countAccept R x (m + 1) =
      countAccept (fun p => R (p.1, false :: p.2)) x m +
      countAccept (fun p => R (p.1, true :: p.2)) x m := by
  have hg := gap_first_bit R (fun p => R (p.1, false :: p.2))
    (fun p => R (p.1, true :: p.2)) x m (by
      intro b
      rw [List.ofFn_succ]
      cases b 0 <;> rfl)
  have hp : (2 : ℤ) ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
  simp only [gap, hp] at hg
  change 2 * (countAccept R x (m + 1) : ℤ) - (2 ^ m + 2 ^ m) =
    (2 * (countAccept (fun p => R (p.1, false :: p.2)) x m : ℤ) - 2 ^ m) +
    (2 * (countAccept (fun p => R (p.1, true :: p.2)) x m : ℤ) - 2 ^ m) at hg
  have he : (countAccept R x (m + 1) : ℤ) =
      (countAccept (fun p => R (p.1, false :: p.2)) x m : ℤ) +
      (countAccept (fun p => R (p.1, true :: p.2)) x m : ℤ) := by
    linarith only [hg]
  exact_mod_cast he

/-- Add two witness bits, accepting exactly when they agree. -/
def pairedPrefix (R : List Bool × List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  match p.2 with
  | a :: b :: w => (a == b) && R (p.1, w)
  | _ => false

theorem count_pairedPrefix (R : List Bool × List Bool → Bool) (x : List Bool) (m : ℕ) :
    countAccept (pairedPrefix R) x (m + 2) = 2 * countAccept R x m := by
  rw [count_prefix _ _ (m + 1), count_prefix _ _ m, count_prefix _ _ m]
  simp [pairedPrefix, countAccept, two_mul]

theorem count_pairedPrefix_double (R : List Bool × List Bool → Bool)
    (x : List Bool) (h : ℕ) :
    countAccept (pairedPrefix R) x (2 * (h + 1)) = 2 * countAccept R x (2 * h) := by
  rw [show 2 * (h + 1) = 2 * h + 2 by omega]
  exact count_pairedPrefix R x (2 * h)

/-- The padding doubles all residue counts while increasing the normalization
exponent by one, so the represented acceptance probability is unchanged. -/
theorem pairedPrefix_representation (R : ℕ → List Bool × List Bool → Bool)
    (x : List Bool) (h : ℕ) :
    (1 / 2 : ℝ) ^ (h + 1) *
      (((countAccept (pairedPrefix (R 0)) x (2 * (h + 1)) : ℝ) -
          (countAccept (pairedPrefix (R 4)) x (2 * (h + 1)) : ℝ)) +
        Real.sqrt 2 * ((countAccept (pairedPrefix (R 1)) x (2 * (h + 1)) : ℝ) -
          (countAccept (pairedPrefix (R 3)) x (2 * (h + 1)) : ℝ))) =
    (1 / 2 : ℝ) ^ h *
      (((countAccept (R 0) x (2 * h) : ℝ) - (countAccept (R 4) x (2 * h) : ℝ)) +
        Real.sqrt 2 * ((countAccept (R 1) x (2 * h) : ℝ) - (countAccept (R 3) x (2 * h) : ℝ))) := by
  simp only [count_pairedPrefix_double, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  ring

end BQPCounting
