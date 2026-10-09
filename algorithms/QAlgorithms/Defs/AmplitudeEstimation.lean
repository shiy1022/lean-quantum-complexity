import QAlgorithms.Defs.Measurement

/-!
# Phase precision on the circle, iterative phase estimation, amplitude estimation,
search with an unknown number of marked items (shared definition layer)

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), Chapters 3–4. Phases are measured in full turns (`φ ∈ [0, 1)` stands for
`e^{2πiφ}`), the QFT is the frozen `qftQubits` (sign `+`, normalization `1/√2^m`, Def. 3.1), and
the first qubit is the most significant bit.
-/

namespace QAlgorithms

open scoped ENNReal

/-- Nannicini p.62 (Thm. 3.9), p.64 and p.66 (§3.3): the distance on the circle `ℝ/ℤ` of two
phases measured in full turns, `|(x − y) − round(x − y)|`. For `x, y ∈ [0, 1)` this is the
source's `min{|x − y|, 1 − |x − y|}`. The distance of angles `a, b` modulo `2π` is
`2π · circDist (a / 2π) (b / 2π)`. -/
noncomputable def circDist (x y : ℝ) : ℝ :=
  |(x - y) - (round (x - y) : ℝ)|

/-- Nannicini p.66, §3.3.2 (initialization step of iterative phase estimation): the integer
`k ∈ {0, …, 7}` obtained by rounding the estimate `ω_h` (in full turns) to the closest multiple of
`1/8`, modulo `1`, written as `8 · (ω_h rounded)`. Ties round up (Mathlib's `round`). Its 3-bit
binary expansion (most significant first) is `p_h p_{h+1} p_{h+2}`. -/
noncomputable def ipeInitIndex (h : ℕ) (ω : ℕ → ℝ) : ℕ :=
  Int.toNat (round (8 * ω h) % 8)

/-- Nannicini p.66, §3.3.2: the pair of digits `(p_{h−d}, p_{h−d+1})` after `d` steps of iterative
phase estimation, for `d ≤ h − 1`. Step `d = 0` is the initialization (`p_h, p_{h+1}` from
`ipeInitIndex`). The iteration step for `j = h − d − 1` sets `p_j := 0` if
`|0.0 p_{j+1} p_{j+2} − ω_j| < 1/4` (distance on the circle) and `p_j := 1` otherwise (the source's
second test `|0.1 p_{j+1} p_{j+2} − ω_j| < 1/4` is taken as the else branch). -/
noncomputable def ipeLowPair (h : ℕ) (ω : ℕ → ℝ) : ℕ → Bool × Bool
  | 0 => ((ipeInitIndex h ω).testBit 2, (ipeInitIndex h ω).testBit 1)
  | d + 1 =>
      let a := (ipeLowPair h ω d).1
      let b := (ipeLowPair h ω d).2
      (if circDist ((if a then 1 else 0) * 4⁻¹ + (if b then 1 else 0) * 8⁻¹) (ω (h - d - 1)) < 4⁻¹
        then false else true, a)

/-- Nannicini p.66, §3.3.2: the digits `p_1, …, p_{h+2}` (`true` = digit 1) computed by iterative
phase estimation from the angle estimates `ω_j` of `2^{j−1} φ` in full turns (`ω_h` is used by the
initialization, `ω_j` for `j = h − 1, …, 1` by the iteration step). `p_h p_{h+1} p_{h+2}` is the
binary expansion of `ipeInitIndex h ω`; `p_j` for `1 ≤ j < h` comes from `ipeLowPair`. Indices
outside `1, …, h + 2` return `false`. Meaningful for `h ≥ 1` (statements assume it). -/
noncomputable def ipeDigits (h : ℕ) (ω : ℕ → ℝ) : ℕ → Bool := fun j =>
  if j = h + 2 then (ipeInitIndex h ω).testBit 0
  else if j = h + 1 then (ipeInitIndex h ω).testBit 1
  else if 1 ≤ j ∧ j ≤ h then (ipeLowPair h ω (h - j)).1
  else false

/-- Nannicini p.66, §3.3.2: the binary fraction `0.p_j p_{j+1} … p_last =
Σ_{i=j}^{last} p_i 2^{−(i−j+1)}` (used with `last = h + 2`). -/
noncomputable def binFracFrom (p : ℕ → Bool) (j last : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc j last, (if p i then 1 else 0) * ((2 : ℝ) ^ (i - j + 1))⁻¹

/-- Nannicini p.78, Thm. 4.6: the good component `|ψ_G⟩ = (1/√p) Σ_{j∈M} α_j |j⟩` of
`α = S|0⟩`, with `p = Σ_{j∈M} |α_j|²`. Junk value `0` when `p = 0`; Thm. 4.6's setting has
`0 < p < 1`, a hypothesis of the statement. -/
noncomputable def ampGoodState {ι : Type*} [Fintype ι] [DecidableEq ι] (α : EuclideanSpace ℂ ι)
    (M : Finset ι) : EuclideanSpace ℂ ι :=
  ((Real.sqrt (probEvent α fun j => j ∈ M))⁻¹ : ℂ) •
    WithLp.toLp 2 fun j => if j ∈ M then α j else 0

/-- Nannicini p.78, Thm. 4.6: the bad component `|ψ_B⟩ = (1/√(1 − p)) Σ_{j∉M} α_j |j⟩` of
`α = S|0⟩`, `p` as in `ampGoodState`. Junk value `0` when `p = 1`. -/
noncomputable def ampBadState {ι : Type*} [Fintype ι] [DecidableEq ι] (α : EuclideanSpace ℂ ι)
    (M : Finset ι) : EuclideanSpace ℂ ι :=
  ((Real.sqrt (1 - probEvent α fun j => j ∈ M))⁻¹ : ℂ) •
    WithLp.toLp 2 fun j => if j ∈ M then 0 else α j

/-- Nannicini pp.86–87, §4.3.3 and Fig. 4.9: the state before measurement of the amplitude
estimation circuit with `m` qubits of precision: `|0⟩_m|0⟩_n`, then `S` on the second register,
then phase estimation (frozen `phaseEstimationState`) of the Grover operator
`G = S F S† R` with `F = 2|0⟩⟨0| − I` (frozen `ampAmpIterate S R 0`). The controlled powers
`G^{2^{m−k}}` are controlled by qubit `k` (first qubit most significant), as in Fig. 4.9. -/
noncomputable def aeState {n : ℕ} (m : ℕ) (S R : Matrix (Qubits n) (Qubits n) ℂ) :
    EuclideanSpace ℂ (Qubits m × Qubits n) :=
  phaseEstimationState m (ampAmpIterate S R 0) (act S (zeroKet n))

/-- Nannicini p.86, §4.3.3 (last step of amplitude estimation): the angle returned from the
measured `m`-bit string `b`: with `0.b = bitsToNat b / 2^m`, it is `π(1 − 0.b)` if the first bit
`b_1` is `1` (i.e. `2^{m−1} ≤ bitsToNat b`) and `π · 0.b` otherwise. The amplitude estimate is
`sin²` of it. At `m = 0` it is `0`. -/
noncomputable def aeAngle {m : ℕ} (b : Qubits m) : ℝ :=
  if 1 ≤ m ∧ 2 ^ (m - 1) ≤ bitsToNat b then
    Real.pi * (1 - (bitsToNat b : ℝ) * ((2 : ℝ) ^ m)⁻¹)
  else Real.pi * ((bitsToNat b : ℝ) * ((2 : ℝ) ^ m)⁻¹)

/-- Nannicini p.92, Eq. (4.11) and the proof of Lem. 4.28: the first-register state
`|ϑ_+⟩ = Q_m† (2^{−m/2} Σ_k e^{2iθk} |k⟩)` produced by the amplitude estimation circuit on the
eigenstate with eigenvalue `e^{2iθ}`; `|ϑ_−⟩` is `aeVartheta m (−θ)`. -/
noncomputable def aeVartheta (m : ℕ) (θ : ℝ) : EuclideanSpace ℂ (Qubits m) :=
  act (star (qftQubits m)) (WithLp.toLp 2 fun k =>
    Complex.exp (2 * Complex.I * (θ : ℂ) * (bitsToNat k : ℂ)) * ((Real.sqrt ((2 : ℝ) ^ m))⁻¹ : ℂ))

/-- Nannicini p.94, Alg. 1, lines 13–18 (the enumeration fallback): the strings of `{0,1}^n` are
tested in increasing `bitsToNat` order, one application of `U_f` each, starting from cost `c`.
If a marked string exists, the first one `j` is returned at cost `c + bitsToNat j + 1`; otherwise
"no solution" (`none`) at cost `c + 2^n`. A point mass on `(output, cost)`. -/
noncomputable def searchAlg1Enum {n : ℕ} (f : Qubits n → Bool) (c : ℕ)
    (oc : Option (Qubits n) × ℕ) : ℝ≥0∞ :=
  open Classical in
  if ∃ j, f j = true then
    (if ∃ j, f j = true ∧ (∀ j', f j' = true → bitsToNat j ≤ bitsToNat j') ∧
        oc = (some j, c + bitsToNat j + 1) then 1 else 0)
  else (if oc = (none, c + 2 ^ n) then 1 else 0)

/-- Nannicini p.94, Alg. 1, lines 3–12: the weight of ending with `oc = (output, cost)` when the
remaining rounds use the precisions listed in `rounds`, starting from cost `c`. In a round with
precision `m`, the string `j` is read on the second register of the amplitude estimation circuit
(`aeState m H^{⊗n} R`, `R|j⟩ = (−1)^{f(j)}|j⟩` the frozen `phaseOracle f`) with its marginal
probability (Postulate 3); the round costs `(2^m − 1) + 1` applications of `U_f` (the `2^m − 1`
Grover iterates of phase estimation, one `U_f` each, plus the evaluation of `f(j)`); the run
stops with output `j` if `f(j) = 1`, else goes on. After the last round, `searchAlg1Enum`. -/
noncomputable def searchAlg1Rounds {n : ℕ} (f : Qubits n → Bool) :
    List ℕ → ℕ → Option (Qubits n) × ℕ → ℝ≥0∞
  | [], c, oc => searchAlg1Enum f c oc
  | m :: rest, c, oc =>
      ∑ j : Qubits n,
        ENNReal.ofReal (∑ b : Qubits m, prob (aeState m (hadamardN n) (phaseOracle f)) (b, j)) *
          (if f j = true then (if oc = (some j, c + ((2 ^ m - 1) + 1)) then 1 else 0)
          else searchAlg1Rounds f rest (c + ((2 ^ m - 1) + 1)) oc)

/-- Nannicini p.94, Alg. 1: the probability that the quantum search algorithm without knowledge of
the number of marked items ends with output `oc.1` (`none` = "no solution") after `oc.2`
applications of `U_f`. The rounds are `(m, i)` for `m = 1, …, n − 1` and `i = 1, 2`, in this order,
then the enumeration. A weight function (its total mass is `1`, a fact, not an obligation of the
definition). "Alg. 1 returns `o`" is stated as: every `oc` of nonzero weight has `oc.1 = o`. -/
noncomputable def searchAlg1Weight {n : ℕ} (f : Qubits n → Bool) :
    Option (Qubits n) × ℕ → ℝ≥0∞ :=
  searchAlg1Rounds f ((List.range (n - 1)).flatMap fun i => [i + 1, i + 1]) 0

/-- Nannicini p.94, Thm. 4.29: the expected number of applications of `U_f` made by Alg. 1. -/
noncomputable def searchAlg1ExpectedCost {n : ℕ} (f : Qubits n → Bool) : ℝ≥0∞ :=
  ∑' oc : Option (Qubits n) × ℕ, (oc.2 : ℝ≥0∞) * searchAlg1Weight f oc

/-! ### Sanity tests -/

example (x : ℝ) : circDist x (x + 1) = 0 := by
  rw [circDist, show x - (x + 1) = ((-1 : ℤ) : ℝ) by push_cast; ring, round_intCast]
  simp

example : circDist (9 / 10) (1 / 10) = 1 / 5 := by
  have h : round ((9 / 10 : ℝ) - 1 / 10) = 1 := by
    rw [round_eq, Int.floor_eq_iff]; norm_num
  rw [circDist, h]
  norm_num [abs_of_neg]

example (h : ℕ) (ω : ℕ → ℝ) : ipeDigits h ω 0 = false := by
  simp [ipeDigits]

/-- `h = 1`, `ω_1 = 5/8`: the three digits are `101`, most significant first (`0.101 = 5/8`). -/
example : ipeDigits 1 (fun _ => 5 / 8) 1 = true ∧ ipeDigits 1 (fun _ => 5 / 8) 2 = false ∧
    ipeDigits 1 (fun _ => 5 / 8) 3 = true := by
  have hk : ipeInitIndex 1 (fun _ => 5 / 8) = 5 := by
    rw [ipeInitIndex, show (8 : ℝ) * (5 / 8) = ((5 : ℤ) : ℝ) by norm_num, round_intCast]
    rfl
  refine ⟨?_, ?_, ?_⟩ <;> simp [ipeDigits, ipeLowPair, hk] <;> decide

example (p : ℕ → Bool) (j : ℕ) : binFracFrom p j j = if p j then 2⁻¹ else 0 := by
  simp [binFracFrom]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (α : EuclideanSpace ℂ ι) :
    ampGoodState α ∅ = 0 := by
  ext j; simp [ampGoodState]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (α : EuclideanSpace ℂ ι) :
    ampBadState α ∅ = α := by
  ext j; simp [ampBadState, probEvent]

example : aeAngle (![true] : Qubits 1) = Real.pi / 2 := by
  simp [aeAngle, bitsToNat]
  ring

example {n : ℕ} (c : ℕ) :
    searchAlg1Enum (fun _ : Qubits n => false) c (none, c + 2 ^ n) = 1 := by
  simp [searchAlg1Enum]

example {n : ℕ} (f : Qubits n → Bool) (c : ℕ) : searchAlg1Rounds f [] c = searchAlg1Enum f c := by
  funext oc; rfl

end QAlgorithms
