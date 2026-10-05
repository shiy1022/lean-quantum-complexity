import Definitions.Def_ShiBQP_Core
import Definitions.Def_ShiClassPP
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiBQP_acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion

namespace BQPReferenceValidation.Source5

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! COUNT-1: acceptance probability as a signed integer count.

Downstream of PATH-1 (an amplitude is `((√2 : ℝ) : ℂ)⁻¹ ^ h` times a sum of eighth roots of
unity) and of RING-1 (the squared norm of such a sum lies in `ℤ + √2 ℤ`).  Taking those two
shapes as hypotheses, acceptance is `(1/2)^h * (A + B √2)` with `A B : ℤ` the sums, over the
accepting output strings, of the per-string integer parts.

The crux is the threshold comparison.  With `D := 2*A - 2^h : ℤ` the condition `1/2 < accept`
is `0 < D + 2 B √2`, which mentions an irrational.  It is reduced here to a purely integer,
decidable criterion by splitting on the signs of `D` and `B` and comparing `D^2` with `8 B^2`.
The `√2` term genuinely survives: witnesses are supplied where it flips the verdict in each
direction. -/


private lemma s2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private lemma s2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

private lemma s2_gt_one : (1 : ℝ) < Real.sqrt 2 := by
  nlinarith [s2_sq, s2_pos]

/-- Normalisation bridge: the path-sum prefactor contributes exactly `(1/2)^h`. -/
private lemma norm_sq_prefactor (h : ℕ) (z : ℂ) :
    ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ h * z‖ ^ 2 = (1 / 2 : ℝ) ^ h * ‖z‖ ^ 2 := by
  have hs : ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ h‖ = (Real.sqrt 2)⁻¹ ^ h := by
    rw [norm_pow, norm_inv, Complex.norm_of_nonneg (Real.sqrt_nonneg 2)]
  have h2 : ((Real.sqrt 2)⁻¹) ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, s2_sq]; norm_num
  rw [norm_mul, mul_pow, hs, ← pow_mul, mul_comm h 2, pow_mul, h2]

private lemma sq_scaled (B : ℤ) :
    (2 * (B : ℝ) * Real.sqrt 2) ^ 2 = 8 * (B : ℝ) ^ 2 := by
  have h : (2 * (B : ℝ) * Real.sqrt 2) ^ 2 = 4 * (B : ℝ) ^ 2 * (Real.sqrt 2 ^ 2) := by ring
  rw [h, s2_sq]; ring

/-- Mixed case `D < 0 < B`: the comparison is decided by `D^2` against `8 B^2`. -/
private lemma mixed_neg_pos {D B : ℤ} (hD : D < 0) (hB : 0 < B) :
    ((0 : ℝ) < (D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2 ↔ D ^ 2 < 8 * B ^ 2) := by
  have hsp := s2_pos
  have hDr : (D : ℝ) < 0 := by exact_mod_cast hD
  have hBr : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hpos : (0 : ℝ) < 2 * (B : ℝ) * Real.sqrt 2 :=
    mul_pos (by linarith) hsp
  constructor
  · intro hlt
    have h1 : (0 : ℝ) < 2 * (B : ℝ) * Real.sqrt 2 - (D : ℝ) := by linarith
    have hexp : ((D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2)
        * (2 * (B : ℝ) * Real.sqrt 2 - (D : ℝ))
        = 8 * (B : ℝ) ^ 2 - (D : ℝ) ^ 2 := by
      have hr : ((D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2)
          * (2 * (B : ℝ) * Real.sqrt 2 - (D : ℝ))
          = (2 * (B : ℝ) * Real.sqrt 2) ^ 2 - (D : ℝ) ^ 2 := by ring
      rw [hr, sq_scaled B]
    have hprod := mul_pos hlt h1
    rw [hexp] at hprod
    have h3 : (D : ℝ) ^ 2 < 8 * (B : ℝ) ^ 2 := by linarith
    exact_mod_cast h3
  · intro h
    have h3 : (D : ℝ) ^ 2 < 8 * (B : ℝ) ^ 2 := by exact_mod_cast h
    by_contra hc
    push_neg at hc
    have hle : 2 * (B : ℝ) * Real.sqrt 2 ≤ -(D : ℝ) := by linarith
    have hsq := mul_self_le_mul_self (le_of_lt hpos) hle
    nlinarith [hsq, sq_scaled B]

/-- Mixed case `B < 0 < D`: the comparison is decided by `8 B^2` against `D^2`. -/
private lemma mixed_pos_neg {D B : ℤ} (hD : 0 < D) (hB : B < 0) :
    ((0 : ℝ) < (D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2 ↔ 8 * B ^ 2 < D ^ 2) := by
  have hsp := s2_pos
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hBr : (B : ℝ) < 0 := by exact_mod_cast hB
  have hneg : 2 * (B : ℝ) * Real.sqrt 2 < 0 := by
    have : (0 : ℝ) < 2 * (-(B : ℝ)) * Real.sqrt 2 := mul_pos (by linarith) hsp
    linarith
  constructor
  · intro hlt
    have h1 : (0 : ℝ) < (D : ℝ) - 2 * (B : ℝ) * Real.sqrt 2 := by linarith
    have hexp : ((D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2)
        * ((D : ℝ) - 2 * (B : ℝ) * Real.sqrt 2)
        = (D : ℝ) ^ 2 - 8 * (B : ℝ) ^ 2 := by
      have hr : ((D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2)
          * ((D : ℝ) - 2 * (B : ℝ) * Real.sqrt 2)
          = (D : ℝ) ^ 2 - (2 * (B : ℝ) * Real.sqrt 2) ^ 2 := by ring
      rw [hr, sq_scaled B]
    have hprod := mul_pos hlt h1
    rw [hexp] at hprod
    have h3 : 8 * (B : ℝ) ^ 2 < (D : ℝ) ^ 2 := by linarith
    exact_mod_cast h3
  · intro h
    have h3 : 8 * (B : ℝ) ^ 2 < (D : ℝ) ^ 2 := by exact_mod_cast h
    by_contra hc
    push_neg at hc
    have hle : (D : ℝ) ≤ -(2 * (B : ℝ) * Real.sqrt 2) := by linarith
    have hsq := mul_self_le_mul_self (le_of_lt hDr) hle
    nlinarith [hsq, sq_scaled B]

/-- **The integer criterion.**  `0 < D + 2 B √2` over the reals is equivalent to an explicit
decidable statement about the integers `D` and `B` alone. -/
private lemma crit_iff (D B : ℤ) :
    ((0 : ℝ) < (D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2 ↔
      ((0 < D ∧ 0 ≤ B) ∨ (0 ≤ D ∧ 0 < B) ∨ (D < 0 ∧ 0 < B ∧ D ^ 2 < 8 * B ^ 2) ∨
        (0 < D ∧ B < 0 ∧ 8 * B ^ 2 < D ^ 2))) := by
  have hsp := s2_pos
  have hz : ((0 : ℤ) : ℝ) = (0 : ℝ) := by norm_num
  rcases lt_trichotomy B 0 with hB | hB | hB
  · have hBr : (B : ℝ) < 0 := by exact_mod_cast hB
    have hneg : 2 * (B : ℝ) * Real.sqrt 2 < 0 := by
      have : (0 : ℝ) < 2 * (-(B : ℝ)) * Real.sqrt 2 := mul_pos (by linarith) hsp
      linarith
    rcases lt_trichotomy D 0 with hD | hD | hD
    · have hDr : (D : ℝ) < 0 := by exact_mod_cast hD
      constructor
      · intro hlt; exfalso; linarith
      · intro hr
        exfalso
        rcases hr with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2, -⟩ | ⟨h1, -, -⟩ <;> omega
    · subst hD
      rw [hz]
      constructor
      · intro hlt; exfalso; linarith
      · intro hr
        exfalso
        rcases hr with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2, -⟩ | ⟨h1, -, -⟩ <;> omega
    · rw [mixed_pos_neg hD hB]
      constructor
      · intro hlt; exact Or.inr (Or.inr (Or.inr ⟨hD, hB, hlt⟩))
      · intro hr
        rcases hr with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2, -⟩ | ⟨-, -, h3⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exact h3
  · subst hB
    rw [hz]
    constructor
    · intro hlt
      have hDr : (0 : ℝ) < (D : ℝ) := by linarith
      have hD' : 0 < D := by exact_mod_cast hDr
      exact Or.inl ⟨hD', le_refl 0⟩
    · intro hr
      have hD : 0 < D := by
        rcases hr with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2, -⟩ | ⟨h1, -, -⟩ <;> omega
      have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
      linarith
  · have hBr : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
    have hpos : (0 : ℝ) < 2 * (B : ℝ) * Real.sqrt 2 := mul_pos (by linarith) hsp
    rcases lt_trichotomy D 0 with hD | hD | hD
    · rw [mixed_neg_pos hD hB]
      constructor
      · intro hlt; exact Or.inr (Or.inr (Or.inl ⟨hD, hB, hlt⟩))
      · intro hr
        rcases hr with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨h1, h2, -⟩
        · exfalso; omega
        · exfalso; omega
        · exact h3
        · exfalso; omega
    · subst hD
      rw [hz]
      constructor
      · intro _; exact Or.inr (Or.inl ⟨le_refl 0, hB⟩)
      · intro _; linarith
    · have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
      constructor
      · intro _; exact Or.inl ⟨hD, le_of_lt hB⟩
      · intro _; linarith

/-- The `1/2` threshold on `(1/2)^h (A + B √2)`, cleared to the integer shift
`D = 2 A - 2 ^ h`. -/
private lemma half_lt_iff (h : ℕ) (A B : ℤ) (p : ℝ)
    (hp : p = (1 / 2 : ℝ) ^ h * ((A : ℝ) + (B : ℝ) * Real.sqrt 2)) :
    ((1 : ℝ) / 2 < p ↔ (0 : ℝ) < ((2 * A - 2 ^ h : ℤ) : ℝ) + 2 * (B : ℝ) * Real.sqrt 2) := by
  have ht : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  have hpow : (1 / 2 : ℝ) ^ h = 1 / (2 : ℝ) ^ h := by rw [div_pow, one_pow]
  have hcast : ((2 * A - 2 ^ h : ℤ) : ℝ) = 2 * (A : ℝ) - (2 : ℝ) ^ h := by push_cast; ring
  rw [hp, hpow, hcast, div_mul_eq_mul_div, one_mul, lt_div_iff₀ ht]
  constructor <;> intro hx <;> linarith


theorem _root_.BQPReferenceValidation.candidate5 :
    -- (0) the path-sum prefactor contributes exactly `(1/2)^h` to each squared amplitude
    (∀ (h : ℕ) (z : ℂ),
        ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ h * z‖ ^ 2 = (1 / 2 : ℝ) ^ h * ‖z‖ ^ 2) ∧
    -- (1) acceptance is `(1/2)^h * (A + B √2)`, `A`, `B` sums of the per-output integers
    (∀ (F : ShiClass.Family) (n : ℕ) (x : ShiShallow.Bits n) (h : ℕ)
        (Z : ShiShallow.Bits (n + (F.anc n + 1)) → ℂ)
        (a b : ShiShallow.Bits (n + (F.anc n + 1)) → ℤ),
        (∀ y, ShiShallow.runLayered (F.circ n) (ShiShallow.inputState (m := F.anc n + 1) x) y
            = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ h * Z y) →
        (∀ y, ‖Z y‖ ^ 2 = ((a y : ℤ) : ℝ) + ((b y : ℤ) : ℝ) * Real.sqrt 2) →
        F.accept n x = (1 / 2 : ℝ) ^ h *
          (((∑ y ∈ Finset.univ.filter (fun y => y (F.out n) = true), a y : ℤ) : ℝ)
            + ((∑ y ∈ Finset.univ.filter (fun y => y (F.out n) = true), b y : ℤ) : ℝ)
              * Real.sqrt 2)) ∧
    -- (2) the crux: the irrational comparison reduced to integer arithmetic
    (∀ D B : ℤ,
        ((0 : ℝ) < (D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2 ↔
          ((0 < D ∧ 0 ≤ B) ∨ (0 ≤ D ∧ 0 < B) ∨ (D < 0 ∧ 0 < B ∧ D ^ 2 < 8 * B ^ 2) ∨
            (0 < D ∧ B < 0 ∧ 8 * B ^ 2 < D ^ 2)))) ∧
    (∀ Crit : ℤ → ℤ → Prop,
      (∀ D B : ℤ, (Crit D B ↔
          ((0 < D ∧ 0 ≤ B) ∨ (0 ≤ D ∧ 0 < B) ∨ (D < 0 ∧ 0 < B ∧ D ^ 2 < 8 * B ^ 2) ∨
            (0 < D ∧ B < 0 ∧ 8 * B ^ 2 < D ^ 2)))) →
      -- (2a) the criterion is exactly the `1/2` threshold on the acceptance probability
      ((∀ (h : ℕ) (A B : ℤ) (p : ℝ),
          p = (1 / 2 : ℝ) ^ h * ((A : ℝ) + (B : ℝ) * Real.sqrt 2) →
          ((1 : ℝ) / 2 < p ↔ Crit (2 * A - 2 ^ h) B)) ∧
      -- (2b) it is decidable: a Boolean function on the integers computes it
        (∃ f : ℤ → ℤ → Bool, ∀ D B : ℤ, (Crit D B ↔ f D B = true)) ∧
      -- (2c) with no `√2` part it is exactly the sign test behind `gap`
        (∀ D : ℤ, (Crit D 0 ↔ 0 < D)) ∧
      -- (3) robustness: the BQP gap keeps the comparison away from the boundary
        (∀ (h : ℕ) (A B : ℤ) (p : ℝ),
          p = (1 / 2 : ℝ) ^ h * ((A : ℝ) + (B : ℝ) * Real.sqrt 2) →
          (((2 : ℝ) / 3 ≤ p → Crit (2 * A - 2 ^ h) B) ∧
            (p ≤ (1 : ℝ) / 3 → ¬ Crit (2 * A - 2 ^ h) B))) ∧
      -- (4) the `2 * count - 2 ^ m` shape of `gap`, ready for `mem_ppof_iff_gap_pos`
        (∀ (R : PvsNP.Str × PvsNP.Str → Bool) (x : PvsNP.Str) (m : ℕ),
          (0 < ShiClassPP.gap R x m ↔ 2 ^ m < 2 * ShiClassPP.countAccept R x m)) ∧
      -- (NV1) `√2` flips a NEGATIVE integer verdict to positive: `h = 1`, `A = 1`, `B = 1`
        (¬ ((1 : ℝ) / 2 < (1 / 2 : ℝ) ^ (1 : ℕ) * (((1 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * Real.sqrt 2))
          ∧ (1 : ℝ) / 2 < (1 / 2 : ℝ) ^ (1 : ℕ) * (((1 : ℤ) : ℝ) + ((1 : ℤ) : ℝ) * Real.sqrt 2)
          ∧ Crit (2 * 1 - 2 ^ (1 : ℕ)) 1) ∧
      -- (NV2) `√2` flips a POSITIVE integer verdict to negative: `h = 1`, `A = 2`, `B = -1`
        ((1 : ℝ) / 2 < (1 / 2 : ℝ) ^ (1 : ℕ) * (((2 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * Real.sqrt 2)
          ∧ ¬ ((1 : ℝ) / 2 <
                (1 / 2 : ℝ) ^ (1 : ℕ) * (((2 : ℤ) : ℝ) + ((-1 : ℤ) : ℝ) * Real.sqrt 2))
          ∧ ¬ Crit (2 * 2 - 2 ^ (1 : ℕ)) (-1)) ∧
      -- (NV3) sanity, no `√2` part: `h = 1`, `A = 2`, `B = 0`
        ((1 : ℝ) / 2 < (1 / 2 : ℝ) ^ (1 : ℕ) * (((2 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * Real.sqrt 2)
          ∧ Crit (2 * 2 - 2 ^ (1 : ℕ)) 0))) := by
  have hsp := s2_pos
  have hone := s2_gt_one
  refine ⟨norm_sq_prefactor, ?_, crit_iff, ?_⟩
  · -- (1) acceptance as a signed integer count
    intro F n x h Z a b hamp hring
    have key : ∀ y : ShiShallow.Bits (n + (F.anc n + 1)),
        ‖ShiShallow.runLayered (F.circ n)
            (ShiShallow.inputState (m := F.anc n + 1) x) y‖ ^ 2
          = (1 / 2 : ℝ) ^ h * (((a y : ℤ) : ℝ) + ((b y : ℤ) : ℝ) * Real.sqrt 2) := by
      intro y
      rw [hamp y, norm_sq_prefactor, hring y]
    have hsplit :
        (∑ y : ShiShallow.Bits (n + (F.anc n + 1)), if y (F.out n) = true then
            ‖ShiShallow.runLayered (F.circ n)
              (ShiShallow.inputState (m := F.anc n + 1) x) y‖ ^ 2 else 0)
          = ∑ y ∈ Finset.univ.filter (fun y : ShiShallow.Bits (n + (F.anc n + 1)) =>
              y (F.out n) = true),
              ‖ShiShallow.runLayered (F.circ n)
                (ShiShallow.inputState (m := F.anc n + 1) x) y‖ ^ 2 :=
      (Finset.sum_filter _ _).symm
    have hterm :
        (∑ y ∈ Finset.univ.filter (fun y : ShiShallow.Bits (n + (F.anc n + 1)) =>
            y (F.out n) = true),
            ‖ShiShallow.runLayered (F.circ n)
              (ShiShallow.inputState (m := F.anc n + 1) x) y‖ ^ 2)
          = ∑ y ∈ Finset.univ.filter (fun y : ShiShallow.Bits (n + (F.anc n + 1)) =>
              y (F.out n) = true),
              (1 / 2 : ℝ) ^ h * (((a y : ℤ) : ℝ) + ((b y : ℤ) : ℝ) * Real.sqrt 2) :=
      Finset.sum_congr rfl (fun y _ => key y)
    have hA : ((∑ y ∈ Finset.univ.filter (fun y : ShiShallow.Bits (n + (F.anc n + 1)) =>
          y (F.out n) = true), a y : ℤ) : ℝ)
        = ∑ y ∈ Finset.univ.filter (fun y : ShiShallow.Bits (n + (F.anc n + 1)) =>
            y (F.out n) = true), ((a y : ℤ) : ℝ) := by
      push_cast; ring
    have hB : ((∑ y ∈ Finset.univ.filter (fun y : ShiShallow.Bits (n + (F.anc n + 1)) =>
          y (F.out n) = true), b y : ℤ) : ℝ)
        = ∑ y ∈ Finset.univ.filter (fun y : ShiShallow.Bits (n + (F.anc n + 1)) =>
            y (F.out n) = true), ((b y : ℤ) : ℝ) := by
      push_cast; ring
    simp only [ShiClass.Family.accept, ShiShallow.acceptProb]
    rw [hsplit, hterm, hA, hB, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
  · -- the criterion package
    intro Crit hCrit
    have hC : ∀ D B : ℤ, (Crit D B ↔ (0 : ℝ) < (D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2) := by
      intro D B
      rw [hCrit D B, crit_iff D B]
    have hthr : ∀ (h : ℕ) (A B : ℤ) (p : ℝ),
        p = (1 / 2 : ℝ) ^ h * ((A : ℝ) + (B : ℝ) * Real.sqrt 2) →
        ((1 : ℝ) / 2 < p ↔ Crit (2 * A - 2 ^ h) B) := by
      intro h A B p hp
      rw [hC (2 * A - 2 ^ h) B]
      exact half_lt_iff h A B p hp
    refine ⟨hthr, ⟨fun D B => decide ((0 < D ∧ 0 ≤ B) ∨ (0 ≤ D ∧ 0 < B) ∨
        (D < 0 ∧ 0 < B ∧ D ^ 2 < 8 * B ^ 2) ∨ (0 < D ∧ B < 0 ∧ 8 * B ^ 2 < D ^ 2)), ?_⟩,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro D B
      rw [hCrit D B, decide_eq_true_iff]
    · -- (2c) the `B = 0` reduction
      intro D
      rw [hCrit D 0]
      constructor
      · intro hr
        rcases hr with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2, -⟩ | ⟨h1, -, -⟩ <;> omega
      · intro hD
        exact Or.inl ⟨hD, le_refl 0⟩
    · -- (3) robustness from the BQP gap
      intro h A B p hp
      constructor
      · intro hge
        refine (hthr h A B p hp).mp ?_
        linarith
      · intro hle hcrit
        have hgt := (hthr h A B p hp).mpr hcrit
        linarith
    · -- (4) the `gap` shape
      intro R x m
      simp only [ShiClassPP.gap]
      constructor
      · intro hgt
        have h1 : ((2 ^ m : ℕ) : ℤ) < ((2 * ShiClassPP.countAccept R x m : ℕ) : ℤ) := by
          push_cast
          linarith
        exact_mod_cast h1
      · intro hgt
        have h1 : ((2 ^ m : ℕ) : ℤ) < ((2 * ShiClassPP.countAccept R x m : ℕ) : ℤ) := by
          exact_mod_cast hgt
        push_cast at h1
        linarith
    · -- (NV1) the `√2` term turns a false integer verdict true
      refine ⟨?_, ?_, ?_⟩
      · norm_num
      · push_cast
        nlinarith [hsp]
      · rw [hC]
        push_cast
        nlinarith [hsp]
    · -- (NV2) the `√2` term turns a true integer verdict false
      refine ⟨?_, ?_, ?_⟩
      · norm_num
      · push_cast
        intro hx
        linarith
      · rw [hC]
        push_cast
        intro hx
        linarith
    · -- (NV3) `B = 0` sanity check
      refine ⟨?_, ?_⟩
      · norm_num
      · rw [hC]
        push_cast
        norm_num

end BQPReferenceValidation.Source5

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate5
    let target ← getConstInfo ``ShiBQP.acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate5
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion; axioms {axioms}"
