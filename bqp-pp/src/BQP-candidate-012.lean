import Definitions.Def_ShiShallow_Core
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiBQP_modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two

namespace BQPReferenceValidation.Source12

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! RING-1.  Let `ω = Complex.exp (Complex.I * π / 4)`, a primitive eighth root of unity, and let
`S = ∑ i, ω ^ (k i)` be a path sum of eighth roots of unity indexed by a finite type.

The chosen "phase-difference" statistic is

  `C d = #{ p : ι × ι | (k p.1 + 8 - k p.2 % 8) % 8 = d }`

over ALL ordered pairs (`Finset.univ : Finset (ι × ι)`, which is `univ ×ˢ univ`).  Since
`k p.2 % 8 ≤ 7 < k p.1 + 8` the truncated subtraction never truncates, so this is honestly
"the number of ordered branch pairs whose phase difference is `d` mod 8".

The headline is the last conjunct of the general block: `‖S‖²` is REAL and equals

  `C 0 - C 4 + √2 * (C 1 - C 3)`,

an element of `ℤ + √2·ℤ = ℤ[√2]`, NOT of `ℤ`; the `√2` part does not cancel, as the first
witness (`C 1 = 1`, `C 3 = 0`, `‖S‖² = 2 + √2`) shows unconditionally. -/

private lemma norm_sq_mul_conj (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]

private lemma omega_form (ω : ℂ) (hω : ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4)) :
    ω = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I) := by
  have h : Complex.I * (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hω, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring

private lemma s2_sq : (((Real.sqrt 2 / 2 : ℝ) : ℂ)) ^ 2 = 1 / 2 := by
  have h : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [← Complex.ofReal_pow, h]
  norm_num

private lemma omega_pows (ω : ℂ) (hω : ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4)) :
    ω = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I) ∧
      ω ^ 2 = Complex.I ∧
      ω ^ 3 = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (-1 + Complex.I) ∧
      ω ^ 4 = -1 ∧
      ω ^ 5 = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (-1 - Complex.I) ∧
      ω ^ 6 = -Complex.I ∧
      ω ^ 7 = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - Complex.I) ∧
      ω ^ 8 = 1 := by
  have hf : ω = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I) := omega_form ω hω
  have ht : (((Real.sqrt 2 / 2 : ℝ) : ℂ)) ^ 2 = 1 / 2 := s2_sq
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hw2 : ω ^ 2 = Complex.I := by
    rw [hf]
    linear_combination (2 * Complex.I) * ht + (((Real.sqrt 2 / 2 : ℝ) : ℂ)) ^ 2 * hI
  have hw4 : ω ^ 4 = -1 := by
    have e : ω ^ 4 = (ω ^ 2) ^ 2 := by ring
    rw [e, hw2, hI]
  have hw3 : ω ^ 3 = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (-1 + Complex.I) := by
    have e : ω ^ 3 = ω ^ 2 * ω := by ring
    rw [e, hw2, hf]
    linear_combination (((Real.sqrt 2 / 2 : ℝ) : ℂ)) * hI
  have hw5 : ω ^ 5 = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (-1 - Complex.I) := by
    have e : ω ^ 5 = ω ^ 4 * ω := by ring
    rw [e, hw4, hf]
    ring
  have hw6 : ω ^ 6 = -Complex.I := by
    have e : ω ^ 6 = ω ^ 4 * ω ^ 2 := by ring
    rw [e, hw4, hw2]
    ring
  have hw7 : ω ^ 7 = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - Complex.I) := by
    have e : ω ^ 7 = ω ^ 4 * (ω ^ 2 * ω) := by ring
    rw [e, hw4, hw2, hf]
    linear_combination (-(((Real.sqrt 2 / 2 : ℝ) : ℂ))) * hI
  have hw8 : ω ^ 8 = 1 := by
    have e : ω ^ 8 = ω ^ 4 * ω ^ 4 := by ring
    rw [e, hw4]
    ring
  exact ⟨hf, hw2, hw3, hw4, hw5, hw6, hw7, hw8⟩

private lemma conj_omega (ω : ℂ) (hω : ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4)) :
    (starRingEnd ℂ) ω = ω ^ 7 := by
  obtain ⟨hf, -, -, -, -, -, hw7, -⟩ := omega_pows ω hω
  rw [hw7, hf]
  simp only [map_mul, map_add, map_one, Complex.conj_I, Complex.conj_ofReal]
  ring

private lemma omega_add_pow7 (ω : ℂ) (hω : ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4)) :
    ω + ω ^ 7 = ((Real.sqrt 2 : ℝ) : ℂ) := by
  obtain ⟨hf, -, -, -, -, -, hw7, -⟩ := omega_pows ω hω
  rw [hw7, hf]
  push_cast
  ring

private lemma omega_norm (ω : ℂ) (hω : ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4)) :
    ‖ω‖ = 1 := by
  obtain ⟨-, -, -, -, -, -, -, hw8⟩ := omega_pows ω hω
  have hconj := conj_omega ω hω
  have hc : ((‖ω‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [norm_sq_mul_conj, hconj]
    push_cast
    linear_combination hw8
  have hr : ‖ω‖ ^ 2 = 1 := Complex.ofReal_inj.mp hc
  have h0 : (‖ω‖ - 1) * (‖ω‖ + 1) = 0 := by linear_combination hr
  rcases mul_eq_zero.mp h0 with h | h
  · linarith
  · linarith [norm_nonneg ω]

private lemma pow_mod8 (z : ℂ) (h : z ^ 8 = 1) (a : ℕ) : z ^ a = z ^ (a % 8) := by
  conv_lhs => rw [← Nat.div_add_mod a 8]
  rw [pow_add, pow_mul, h, one_pow, one_mul]

private lemma diff_mod (a b : ℕ) : (a + 7 * b) % 8 = (a + 8 - b % 8) % 8 := by
  have hb : b % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have e1 : (a + 7 * b) % 8 = (a + 7 * (b % 8)) % 8 :=
    (Nat.ModEq.add_left a (Nat.ModEq.mul_left 7 (Nat.mod_modEq b 8))).symm
  have h8 : a + 7 * (b % 8) + 8 = (a + 8 - b % 8) + 8 * (b % 8) := by omega
  have e2 : (a + 7 * (b % 8)) % 8 = (a + 8 - b % 8) % 8 := by
    rw [← Nat.add_mod_right (a + 7 * (b % 8)) 8, h8, Nat.add_mul_mod_self_left]
  exact e1.trans e2

private lemma swap_key' (u v : ℕ) (hu : u < 8) (hv : v < 8) (h : (u + 8 - v) % 8 ≠ 0) :
    (v + 8 - u) % 8 = 8 - (u + 8 - v) % 8 := by
  interval_cases u <;> interval_cases v <;> omega

private lemma swap_key (a b : ℕ) (h : (a + 8 - b % 8) % 8 ≠ 0) :
    (b + 8 - a % 8) % 8 = 8 - (a + 8 - b % 8) % 8 := by
  have ha : a % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hb : b % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have e1 : (a + 8 - b % 8) % 8 = (a % 8 + 8 - b % 8) % 8 := by
    have hsplit : a + 8 - b % 8 = (a % 8 + 8 - b % 8) + 8 * (a / 8) := by
      have hd := Nat.div_add_mod a 8
      omega
    rw [hsplit, Nat.add_mul_mod_self_left]
  have e2 : (b + 8 - a % 8) % 8 = (b % 8 + 8 - a % 8) % 8 := by
    have hsplit : b + 8 - a % 8 = (b % 8 + 8 - a % 8) + 8 * (b / 8) := by
      have hd := Nat.div_add_mod b 8
      omega
    rw [hsplit, Nat.add_mul_mod_self_left]
  rw [e1] at h ⊢
  rw [e2]
  exact swap_key' (a % 8) (b % 8) ha hb h

private lemma collect {α : Type} [Fintype α] [DecidableEq α] (z : ℂ) (f : α → ℕ)
    (hf : ∀ a, f a < 8) :
    ∑ a, z ^ (f a)
      = ∑ d ∈ Finset.range 8,
          (((Finset.univ.filter (fun a => f a = d)).card : ℕ) : ℂ) * z ^ d := by
  refine (Finset.sum_fiberwise_of_maps_to
    (fun a (_ : a ∈ (Finset.univ : Finset α)) => Finset.mem_range.mpr (hf a))
    (fun a => z ^ (f a))).symm.trans ?_
  refine Finset.sum_congr rfl ?_
  intro d _
  have hcong : ∀ a ∈ Finset.univ.filter (fun a => f a = d), z ^ (f a) = z ^ d := by
    intro a ha
    rw [(Finset.mem_filter.mp ha).2]
  rw [Finset.sum_congr rfl hcong, Finset.sum_const, nsmul_eq_mul]

private def Cnt {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = d)).card

private lemma residue_sum {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ) (ω : ℂ)
    (hω : ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4)) :
    ∑ i, ω ^ k i
      = ∑ j ∈ Finset.range 8,
          (((Finset.univ.filter (fun i => k i % 8 = j)).card : ℕ) : ℂ) * ω ^ j := by
  obtain ⟨-, -, -, -, -, -, -, hw8⟩ := omega_pows ω hω
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset ι)) => pow_mod8 ω hw8 (k i))]
  exact collect ω (fun i => k i % 8) (fun i => Nat.mod_lt _ (by norm_num))

private lemma pair_sum {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ) (ω : ℂ)
    (hω : ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4)) :
    ((‖∑ i, ω ^ k i‖ ^ 2 : ℝ) : ℂ)
      = ∑ d ∈ Finset.range 8, ((Cnt k d : ℕ) : ℂ) * ω ^ d := by
  obtain ⟨-, -, -, -, -, -, -, hw8⟩ := omega_pows ω hω
  have hconj := conj_omega ω hω
  have hcs : (starRingEnd ℂ) (∑ i, ω ^ k i) = ∑ i, ω ^ (7 * k i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_pow, hconj, ← pow_mul]
  have hleft : ((∑ i, ω ^ k i) * ∑ j, ω ^ (7 * k j))
      = ∑ i : ι, ∑ j : ι, ω ^ ((k i + 8 - k j % 8) % 8) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [← pow_add, pow_mod8 ω hw8 (k i + 7 * k j), diff_mod (k i) (k j)]
  have hdouble : (∑ p : ι × ι, ω ^ ((k p.1 + 8 - k p.2 % 8) % 8))
      = ∑ i : ι, ∑ j : ι, ω ^ ((k i + 8 - k j % 8) % 8) := Fintype.sum_prod_type _
  have hcol := collect ω (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8)
    (fun p => Nat.mod_lt _ (by norm_num))
  rw [norm_sq_mul_conj, hcs, hleft, ← hdouble]
  exact hcol

private lemma card_symm {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ) (d e : ℕ)
    (hd : d ≠ 0) (hd8 : d < 8) (he : e = 8 - d) : Cnt k e = Cnt k d := by
  subst he
  show (Finset.univ.filter
      (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = 8 - d)).card
    = (Finset.univ.filter
      (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = d)).card
  rw [Finset.card_filter, Finset.card_filter]
  refine Fintype.sum_bijective Prod.swap Prod.swap_bijective _ _ ?_
  intro p
  show (if (k p.1 + 8 - k p.2 % 8) % 8 = 8 - d then 1 else 0)
      = (if (k p.2 + 8 - k p.1 % 8) % 8 = d then 1 else 0)
  by_cases hc : (k p.1 + 8 - k p.2 % 8) % 8 = 8 - d
  · have hne : (k p.1 + 8 - k p.2 % 8) % 8 ≠ 0 := by omega
    have hsw := swap_key (k p.1) (k p.2) hne
    rw [if_pos hc, if_pos (by omega : (k p.2 + 8 - k p.1 % 8) % 8 = d)]
  · have hne2 : ¬ ((k p.2 + 8 - k p.1 % 8) % 8 = d) := by
      intro hx
      have hne : (k p.2 + 8 - k p.1 % 8) % 8 ≠ 0 := by omega
      have hsw := swap_key (k p.2) (k p.1) hne
      exact hc (by omega)
    rw [if_neg hc, if_neg hne2]

private lemma real_form {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ) (ω : ℂ)
    (hω : ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4)) :
    ‖∑ i, ω ^ k i‖ ^ 2
      = (Cnt k 0 : ℝ) - (Cnt k 4 : ℝ)
        + Real.sqrt 2 * ((Cnt k 1 : ℝ) - (Cnt k 3 : ℝ)) := by
  obtain ⟨hf, hw2, hw3, hw4, hw5, hw6, hw7, -⟩ := omega_pows ω hω
  have hp := pair_sum k ω hω
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hp
  have h5 : Cnt k 5 = Cnt k 3 := card_symm k 3 5 (by norm_num) (by norm_num) (by norm_num)
  have h6 : Cnt k 6 = Cnt k 2 := card_symm k 2 6 (by norm_num) (by norm_num) (by norm_num)
  have h7 : Cnt k 7 = Cnt k 1 := card_symm k 1 7 (by norm_num) (by norm_num) (by norm_num)
  have hgoal : ((‖∑ i, ω ^ k i‖ ^ 2 : ℝ) : ℂ)
      = (((Cnt k 0 : ℝ) - (Cnt k 4 : ℝ)
          + Real.sqrt 2 * ((Cnt k 1 : ℝ) - (Cnt k 3 : ℝ)) : ℝ) : ℂ) := by
    rw [hp, h5, h6, h7, pow_zero, pow_one, hw2, hw3, hw4, hw5, hw6, hw7, hf]
    push_cast
    ring
  exact Complex.ofReal_inj.mp hgoal

private lemma witA (ω : ℂ) (hω : ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4)) :
    ‖∑ i : Fin 2, ω ^ (i : ℕ)‖ ^ 2 = 2 + Real.sqrt 2 := by
  obtain ⟨-, -, -, -, -, -, -, hw8⟩ := omega_pows ω hω
  have hconj := conj_omega ω hω
  have hsum := omega_add_pow7 ω hω
  have hs : (∑ i : Fin 2, ω ^ (i : ℕ)) = 1 + ω := by
    rw [Fin.sum_univ_two]
    norm_num
  have hc : ((‖(1 : ℂ) + ω‖ ^ 2 : ℝ) : ℂ) = ((2 + Real.sqrt 2 : ℝ) : ℂ) := by
    rw [norm_sq_mul_conj, map_add, map_one, hconj]
    push_cast
    linear_combination hsum + hw8
  rw [hs]
  exact Complex.ofReal_inj.mp hc

private lemma witB (ω : ℂ) (hω : ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4)) :
    (∑ i : Fin 2, ω ^ (4 * (i : ℕ))) = 0 ∧ ‖∑ i : Fin 2, ω ^ (4 * (i : ℕ))‖ ^ 2 = 0 := by
  obtain ⟨-, -, -, hw4, -, -, -, -⟩ := omega_pows ω hω
  have hs : (∑ i : Fin 2, ω ^ (4 * (i : ℕ))) = 0 := by
    rw [Fin.sum_univ_two]
    have e0 : 4 * ((0 : Fin 2) : ℕ) = 0 := by norm_num
    have e1 : 4 * ((1 : Fin 2) : ℕ) = 4 := by norm_num
    rw [e0, e1, pow_zero, hw4]
    ring
  refine ⟨hs, ?_⟩
  rw [hs, norm_zero]
  norm_num

private lemma witC (ω : ℂ) (hω : ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4)) :
    ‖∑ _i : Fin 3, ω ^ 3‖ ^ 2 = 9 := by
  have hn := omega_norm ω hω
  have hs : (∑ _i : Fin 3, ω ^ 3) = 3 * ω ^ 3 := by
    rw [Fin.sum_univ_three]
    ring
  rw [hs, norm_mul, norm_pow, hn, Complex.norm_ofNat]
  norm_num

theorem _root_.BQPReferenceValidation.candidate12 :
    (∀ ω : ℂ, ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4) →
        ω ^ 8 = 1 ∧ ω ^ 4 = -1 ∧ ‖ω‖ = 1 ∧ ω ^ 2 = Complex.I ∧
          ω + ω ^ 7 = ((Real.sqrt 2 : ℝ) : ℂ) ∧
          2 * Real.cos (Real.pi / 4) = Real.sqrt 2) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (k : ι → ℕ) (ω : ℂ),
        ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4) →
        (∑ i, ω ^ k i
            = ∑ j ∈ Finset.range 8,
                (((Finset.univ.filter (fun i => k i % 8 = j)).card : ℕ) : ℂ) * ω ^ j) ∧
        (((‖∑ i, ω ^ k i‖ ^ 2 : ℝ) : ℂ)
            = ∑ d ∈ Finset.range 8,
                (((Finset.univ.filter
                    (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = d)).card : ℕ) : ℂ)
                  * ω ^ d) ∧
        (∀ d : ℕ, d ≠ 0 → d < 8 →
            (Finset.univ.filter
                (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = 8 - d)).card
              = (Finset.univ.filter
                (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = d)).card) ∧
        ‖∑ i, ω ^ k i‖ ^ 2
            = (((Finset.univ.filter
                  (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = 0)).card : ℕ) : ℝ)
              - (((Finset.univ.filter
                  (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = 4)).card : ℕ) : ℝ)
              + Real.sqrt 2
                * ((((Finset.univ.filter
                      (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = 1)).card : ℕ) : ℝ)
                  - (((Finset.univ.filter
                      (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = 3)).card : ℕ) : ℝ))) ∧
    (∀ ω : ℂ, ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4) →
        ((Finset.univ.filter
              (fun p : Fin 2 × Fin 2 => ((p.1 : ℕ) + 8 - (p.2 : ℕ) % 8) % 8 = 1)).card = 1 ∧
            (Finset.univ.filter
              (fun p : Fin 2 × Fin 2 => ((p.1 : ℕ) + 8 - (p.2 : ℕ) % 8) % 8 = 3)).card = 0 ∧
            (Finset.univ.filter
              (fun p : Fin 2 × Fin 2 => ((p.1 : ℕ) + 8 - (p.2 : ℕ) % 8) % 8 = 0)).card = 2 ∧
            (Finset.univ.filter
              (fun p : Fin 2 × Fin 2 => ((p.1 : ℕ) + 8 - (p.2 : ℕ) % 8) % 8 = 4)).card = 0 ∧
            ‖∑ i : Fin 2, ω ^ (i : ℕ)‖ ^ 2 = 2 + Real.sqrt 2 ∧
            (2 : ℝ) + Real.sqrt 2 ≠ 2) ∧
        ((∑ i : Fin 2, ω ^ (4 * (i : ℕ))) = 0 ∧
            ‖∑ i : Fin 2, ω ^ (4 * (i : ℕ))‖ ^ 2 = 0 ∧
            (Finset.univ.filter
              (fun p : Fin 2 × Fin 2 =>
                (4 * (p.1 : ℕ) + 8 - 4 * (p.2 : ℕ) % 8) % 8 = 0)).card = 2 ∧
            (Finset.univ.filter
              (fun p : Fin 2 × Fin 2 =>
                (4 * (p.1 : ℕ) + 8 - 4 * (p.2 : ℕ) % 8) % 8 = 4)).card = 2 ∧
            (Finset.univ.filter
              (fun p : Fin 2 × Fin 2 =>
                (4 * (p.1 : ℕ) + 8 - 4 * (p.2 : ℕ) % 8) % 8 = 1)).card = 0 ∧
            (Finset.univ.filter
              (fun p : Fin 2 × Fin 2 =>
                (4 * (p.1 : ℕ) + 8 - 4 * (p.2 : ℕ) % 8) % 8 = 3)).card = 0) ∧
        (‖∑ _i : Fin 3, ω ^ 3‖ ^ 2 = 9 ∧
            (Finset.univ.filter
              (fun _p : Fin 3 × Fin 3 => (3 + 8 - 3 % 8) % 8 = 0)).card = 9)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω hω
    obtain ⟨-, hw2, -, hw4, -, -, -, hw8⟩ := omega_pows ω hω
    refine ⟨hw8, hw4, omega_norm ω hω, hw2, omega_add_pow7 ω hω, ?_⟩
    rw [Real.cos_pi_div_four]
    ring
  · intro ι _ _ k ω hω
    refine ⟨residue_sum k ω hω, pair_sum k ω hω, ?_, real_form k ω hω⟩
    intro d hd hd8
    exact card_symm k d (8 - d) hd hd8 rfl
  · intro ω hω
    refine ⟨⟨by decide, by decide, by decide, by decide, witA ω hω, ?_⟩, ?_, witC ω hω, by decide⟩
    · have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      intro hx
      linarith
    · obtain ⟨hb1, hb2⟩ := witB ω hω
      exact ⟨hb1, hb2, by decide, by decide, by decide, by decide⟩

end BQPReferenceValidation.Source12

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate12
    let target ← getConstInfo ``ShiBQP.modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate12
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two; axioms {axioms}"
