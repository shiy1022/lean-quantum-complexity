import ReversibleEstablishedQuantumCore

set_option autoImplicit false
namespace ShiShallow



theorem apply1_tMat_eq_phase {n : ℕ} (i : Fin n) (ψ : ShiShallow.QState n) :
    ShiShallow.apply1 ShiShallow.tMat i ψ =
      fun x => (if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) * ψ x := by
  funext x
  unfold ShiShallow.apply1
  rw [Fintype.sum_bool]
  cases hx : x i with
  | false =>
      have hu : Function.update x i false = x := by
        rw [← hx]; exact Function.update_eq_self i x
      rw [hu]
      simp [ShiShallow.tMat, Matrix.of_apply]
  | true =>
      have hu : Function.update x i true = x := by
        rw [← hx]; exact Function.update_eq_self i x
      rw [hu]
      simp [ShiShallow.tMat, Matrix.of_apply]



open ShiShallow

private lemma shiCnj_update_involution {n : ℕ} (x : Bits n) (i j : Fin n) (hij : i ≠ j) :
    Function.update (Function.update x j (xor (x j) (x i))) j
      (xor ((Function.update x j (xor (x j) (x i))) j)
           ((Function.update x j (xor (x j) (x i))) i)) = x := by
  funext k
  by_cases hk : k = j
  · subst hk
    rw [Function.update_self, Function.update_self, Function.update_of_ne hij]
    cases x k <;> cases x i <;> decide
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]

theorem cnot_conj_phase_map {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : QState n)
    (F : QState n → QState n) (a : Bits n → ℂ)
    (hF : ∀ (φ : QState n) (y : Bits n), F φ y = a y * φ y) :
    cnotState i j hij (F (cnotState i j hij ψ))
      = fun x => a (Function.update x j (xor (x j) (x i))) * ψ x := by
  funext x
  show F (cnotState i j hij ψ) (Function.update x j (xor (x j) (x i)))
      = a (Function.update x j (xor (x j) (x i))) * ψ x
  rw [hF]
  congr 1
  show ψ (Function.update (Function.update x j (xor (x j) (x i))) j
        (xor ((Function.update x j (xor (x j) (x i))) j)
             ((Function.update x j (xor (x j) (x i))) i))) = ψ x
  rw [shiCnj_update_involution x i j hij]



open ShiShallow

theorem phase_composition {n : ℕ} (f g : QState n → QState n) (a b : Bits n → ℂ)
    (hf : ∀ (φ : QState n) (x : Bits n), f φ x = a x * φ x)
    (hg : ∀ (φ : QState n) (x : Bits n), g φ x = b x * φ x)
    (ψ : QState n) :
    ∀ x : Bits n, g (f ψ) x = (b x * a x) * ψ x := by
  intro x
  rw [hg (f ψ) x, hf ψ x]
  ring



private lemma shiCCZ_omega_pow_four :
    Complex.exp (Complex.I * Real.pi / 4) ^ 4 = -1 := by
  have h1 : Complex.exp (Complex.I * Real.pi / 4) ^ 4
      = Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4)
        * (Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4)) := by
    ring
  rw [h1, ← Complex.exp_add, ← Complex.exp_add,
      (show Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4
          + (Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4)
        = Real.pi * Complex.I by ring)]
  exact Complex.exp_pi_mul_I

private lemma shiCCZ_omega_pow_eight :
    Complex.exp (Complex.I * Real.pi / 4) ^ 8 = 1 := by
  have h : Complex.exp (Complex.I * Real.pi / 4) ^ 8
      = (Complex.exp (Complex.I * Real.pi / 4) ^ 4) ^ 2 := by ring
  rw [h, shiCCZ_omega_pow_four]
  norm_num

private lemma shiCCZ_omega_pow_sixteen :
    Complex.exp (Complex.I * Real.pi / 4) ^ 16 = 1 := by
  have h : Complex.exp (Complex.I * Real.pi / 4) ^ 16
      = (Complex.exp (Complex.I * Real.pi / 4) ^ 8) ^ 2 := by ring
  rw [h, shiCCZ_omega_pow_eight]
  norm_num

theorem ccz_phase_exponent_eq (a b c : Bool) :
    Complex.exp (Complex.I * Real.pi / 4) ^
        ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)
          + 7 * (if xor a b then 1 else 0) + 7 * (if xor b c then 1 else 0)
          + 7 * (if xor a c then 1 else 0) + (if xor a (xor b c) then 1 else 0))
      = if (a && b && c) then (-1 : ℂ) else 1 := by
  cases a <;> cases b <;> cases c <;>
    first
      | exact shiCCZ_omega_pow_four
      | exact shiCCZ_omega_pow_sixteen
      | exact pow_zero _

theorem inv_sqrt_two_mul_self : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [one_div]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, hr]
  push_cast
  ring


end ShiShallow
