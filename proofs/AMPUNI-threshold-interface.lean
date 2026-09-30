import «AMPUNI-centered-uniform-closed»
import «AMPUNI-computable-centering»

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiQMAGeneralGap
open ShiShallow ShiClassQMA ShiClassQMAU ShiQMACenteredGap ShiQMAConstructiveSchedule

/-- The parameterized QMA interface, retaining separately generated witness sizes. -/
def QMAWith (c s : Nat → ℝ) : Set (Language Bool) :=
  {L | ∃ F : QMAFamily, UniformQMA F ∧ ShiBQP.WellFormed F.toFamily ∧
    ShiBQP.PolyBounded F.toFamily ∧ VerifiesWith F L c s}

theorem QMAWith_const (c s : ℝ) :
    QMAWith (fun _ => c) (fun _ => s) = QMAU c s := rfl

/-- Unary length and precision, with an explicit separator. The output contains
binary fractional bits, so requesting precision k requires only k output bits. -/
def thresholdInput (n k : Nat) : PvsNP.Str := ShiBQP.encNat n ++ ShiBQP.unary k

/-- Efficient real thresholds are represented by polynomial-time dyadic
approximators. This is a premise about the original thresholds, not an
assumed amplifier or centering-circuit transducer. -/
structure ThresholdApproximation (a : Nat → ℝ) where
  approximate : PvsNP.Str → PvsNP.Str
  polynomialTime : PvsNP.PolyTimeComputable approximate
  length_eq : ∀ n k, (approximate (thresholdInput n k)).length = k
  error_le : ∀ n k, |dyadicValue (approximate (thresholdInput n k)) - a n| ≤
    1 / (2 : ℝ) ^ k

/-- Concrete integer coin numerator obtained from the two approximation algorithms.
Its correctness is proved below; a polynomial-time machine for this composition
is still a separate obligation. -/
def thresholdCoinNumerator {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) : Nat :=
  let k := rounds q n
  centeringNumerator k
    (binaryNumerator (A.approximate (thresholdInput n k)))
    (binaryNumerator (B.approximate (thresholdInput n k)))

theorem thresholdCoinNumerator_spec {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) (hab : b n ≤ a n)
    (hgap : (1 : ℝ) ≤ (↑(q.eval n) : ℝ) * (a n - b n)) :
    thresholdCoinNumerator A B q n ≤ 2 ^ (rounds q n + 1) ∧
    |(thresholdCoinNumerator A B q n : ℝ) / (2 : ℝ) ^ (rounds q n + 1) -
      centeringCoin (a n) (b n)| ≤ (a n - b n) / 4 := by
  let k := rounds q n
  let as := A.approximate (thresholdInput n k)
  let bs := B.approximate (thresholdInput n k)
  have hal : as.length = k := A.length_eq n k
  have hbl : bs.length = k := B.length_eq n k
  have herr := centering_from_bits as bs (hal.trans hbl.symm)
    (by simpa only [hal] using A.error_le n k)
    (by simpa only [hal] using B.error_le n k)
  rw [hal] at herr
  refine ⟨centeringNumerator_le _ _ _, herr.trans ?_⟩
  have hnat : 4 * q.eval n ≤ 2 ^ k := by
    have h := eval_le_pow_budget q n
    dsimp [k, rounds]
    rw [pow_add]
    norm_num
    omega
  have hreal : 4 * (↑(q.eval n) : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hnat
  have hpos : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) _
  apply (div_le_iff₀ hpos).mpr
  have hm := mul_nonneg (sub_nonneg.mpr hreal) (sub_nonneg.mpr hab)
  nlinarith

/-- A positive gap and nonnegative soundness exclude the constant-one coin.
Thus the fractional circuit handles every threshold coin used here. -/
theorem thresholdCoinNumerator_lt {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) (hb : 0 ≤ b n) (hab : b n ≤ a n)
    (hgap : (1 : ℝ) ≤ (↑(q.eval n) : ℝ) * (a n - b n)) :
    thresholdCoinNumerator A B q n < 2 ^ (rounds q n + 1) := by
  have hpos : 0 < a n - b n := by
    by_contra hn
    have hnonpos : a n - b n ≤ 0 := le_of_not_gt hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (q.eval n) :
      (0 : ℝ) ≤ ↑(q.eval n)) hnonpos
    linarith
  have he := (abs_le.mp (thresholdCoinNumerator_spec A B q n hab hgap).2).2
  have hr : (thresholdCoinNumerator A B q n : ℝ) /
      (2 : ℝ) ^ (rounds q n + 1) < 1 := by
    dsimp [centeringCoin] at he
    linarith
  have hd : (0 : ℝ) < 2 ^ (rounds q n + 1) := pow_pos (by norm_num) _
  have ht := (div_lt_one hd).mp hr
  exact_mod_cast ht

/-- Executable fractional bits fed directly to the centering circuit. -/
def thresholdCoinBits {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) : List Bool :=
  fractionBits (rounds q n + 1) (thresholdCoinNumerator A B q n)

theorem thresholdCoinBits_length {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) :
    (thresholdCoinBits A B q n).length = rounds q n + 1 :=
  fractionBits_length _ _

theorem thresholdCoinBits_spec {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) (hb : 0 ≤ b n) (hab : b n ≤ a n)
    (hgap : (1 : ℝ) ≤ (↑(q.eval n) : ℝ) * (a n - b n)) :
    |dyadicValue (thresholdCoinBits A B q n) - centeringCoin (a n) (b n)| ≤
      (a n - b n) / 4 := by
  have hj := thresholdCoinNumerator_lt A B q n hb hab hgap
  simpa only [thresholdCoinBits, dyadicValue, fractionBits_length,
    fractionBits_numerator _ _ hj] using
    (thresholdCoinNumerator_spec A B q n hab hgap).2

/-- The precision uses the existing affine-logarithmic counter, and even a
unary encoding of the resulting numerator has polynomial length. -/
theorem thresholdCoinNumerator_size {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) :
    thresholdCoinNumerator A B q n ≤
      2 * (3 ^ (Nat.log 2 (q.eval 1 + 1) + q.natDegree + 4) *
        (n + 1) ^ (2 * q.natDegree)) := by
  have hnum : thresholdCoinNumerator A B q n ≤ 2 ^ (rounds q n + 1) :=
    centeringNumerator_le _ _ _
  have hp : 2 ^ rounds q n ≤ 3 ^ rounds q n := Nat.pow_le_pow_left (by decide) _
  have hb := copies_rounds_le q n
  rw [pow_succ] at hnum
  nlinarith

/-- The checked centered-gap result expressed directly as a class inclusion. -/
theorem QMAWith_centered_amplification (d : Nat → ℝ) (q p : Polynomial ℕ)
    (hd₀ : ∀ n, 0 ≤ d n) (hd₁ : ∀ n, d n ≤ 1 / 2)
    (hgap : ∀ n, (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d n) :
    QMAWith (fun n => 1 / 2 + d n) (fun n => 1 / 2 - d n) ⊆
      QMAWith (fun n => 1 - ((1 : ℝ) / 2) ^ (p.eval n))
        (fun n => ((1 : ℝ) / 2) ^ (p.eval n)) := by
  intro L hL
  obtain ⟨F, hu, hw, hp, hv⟩ := hL
  exact centered_gap_amplification_closed F L hu hw hp d q p hd₀ hd₁ hgap hv

/-- The target exponent may be any polynomially bounded natural-valued
function. The generator only needs a dominating polynomial, so it need not
compute that function exactly. -/
theorem QMAWith_centered_bounded_target (d : Nat → ℝ) (q p : Polynomial ℕ)
    (r : Nat → Nat) (hr : ∀ n, r n ≤ p.eval n)
    (hd₀ : ∀ n, 0 ≤ d n) (hd₁ : ∀ n, d n ≤ 1 / 2)
    (hgap : ∀ n, (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d n) :
    QMAWith (fun n => 1 / 2 + d n) (fun n => 1 / 2 - d n) ⊆
      QMAWith (fun n => 1 - ((1 : ℝ) / 2) ^ (r n))
        (fun n => ((1 : ℝ) / 2) ^ (r n)) := by
  intro L hL
  obtain ⟨G, hu, hw, hp, hv⟩ := QMAWith_centered_amplification d q p hd₀ hd₁ hgap hL
  refine ⟨G, hu, hw, hp, ?_⟩
  intro w
  have he : ((1 : ℝ) / 2) ^ (p.eval w.length) ≤ ((1 : ℝ) / 2) ^ (r w.length) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (hr w.length)
  exact verifiesAt_mono (hv w) (by linarith only [he]) he

end ShiQMAGeneralGap



-- The interface proofs add no assumed transducer or nonstandard axiom.
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``ShiQMAGeneralGap.QMAWith_const,
    ``ShiQMAGeneralGap.thresholdCoinNumerator_spec,
    ``ShiQMAGeneralGap.thresholdCoinNumerator_size,
    ``ShiQMAGeneralGap.thresholdCoinNumerator_lt,
    ``ShiQMAGeneralGap.thresholdCoinBits_length,
    ``ShiQMAGeneralGap.thresholdCoinBits_spec,
    ``ShiQMAGeneralGap.QMAWith_centered_amplification,
    ``ShiQMAGeneralGap.QMAWith_centered_bounded_target]
  for name in names do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected interface axiom {ax} in {name}"
    logInfo m!"THRESHOLD_INTERFACE_CHECKED {name}; axioms {axioms}"
