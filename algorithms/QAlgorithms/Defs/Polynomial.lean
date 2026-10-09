import QAlgorithms.Defs.Adversary

/-!
# The polynomial method (shared definition layer)

Polynomials are Mathlib's `MvPolynomial σ ℝ`; a Boolean input `x : σ → Bool` is evaluated as the
0/1 point `boolPoint x`.
-/

namespace QAlgorithms

open scoped Nat

/-- Childs p.106–107 (§21.3–21.4): a multilinear polynomial (degree at most `1` in each variable). -/
def IsMultilinear {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ i, p.degreeOf i ≤ 1

/-- Childs p.107 (§21.3): a bit string as a 0/1 point, at which polynomials are evaluated
(`MvPolynomial.eval (boolPoint x) p` is the source's `p(x)`). -/
def boolPoint {σ : Type*} (x : σ → Bool) : σ → ℝ :=
  fun i => if x i then 1 else 0

/-- Childs p.107 (Lemma 21.2): `P(k) = E_{|x| = k}[p(x)]`, the uniform average of `p` over the
`n`-bit strings of Hamming weight `k` (there are `C(n, k)` of them, a positive number for
`k ≤ n`; statements quantify `k ≤ n`). -/
noncomputable def weightAverage {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (k : ℕ) : ℝ :=
  ((Nat.choose n k : ℝ))⁻¹ *
    ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => hammingWeight x = k),
      MvPolynomial.eval (boolPoint x) p

/-- Childs p.113 (§22.5): the triple `(m, a, b)` is valid: `m ∈ {0, …, n}`, `a ∣ m`, `b ∣ n − m`
(with `a, b ≥ 1`, which the formula `⌈i/a⌉`, `⌊(n − i)/b⌋` presupposes). -/
def ValidKutinTriple (n m a b : ℕ) : Prop :=
  m ≤ n ∧ 1 ≤ a ∧ 1 ≤ b ∧ a ∣ m ∧ b ∣ n - m

/-- Childs p.113 ((22.6)): Kutin's input `x^{m,a,b}`, `x_i = ⌈i/a⌉` for `1 ≤ i ≤ m` and
`x_i = n − ⌊(n − i)/b⌋` for `m < i ≤ n` (positions and values in `{1, …, n}`), stored 0-based:
position `p : Fin n` is `i = p + 1` and value `v` is stored as `v − 1`. The formula is evaluated
in 1-based natural-number arithmetic (`⌈i/a⌉ = (i + a − 1)/a`); for a valid triple the values
lie in `{1, …, n}`, and otherwise they are clamped into range. -/
def kutinInput (n m a b : ℕ) : Fin n → Fin n :=
  fun p =>
    ⟨min ((if (p : ℕ) + 1 ≤ m then ((p : ℕ) + 1 + a - 1) / a else n - (n - ((p : ℕ) + 1)) / b) - 1)
      (n - 1), by have := p.isLt; omega⟩

/-- Childs p.113 ((22.3) and §22.5): the variables `δ^{στ}_{ij} = [x^{στ}_i = j]` of the input
`x^{στ}_i = τ(x^{m,a,b}_{σ(i)})`, for permutations `σ, τ` of `{1, …, n}`. -/
def kutinDelta (n m a b : ℕ) (σ τ : Equiv.Perm (Fin n)) : Fin n × Fin n → ℝ :=
  fun ij => if τ (kutinInput n m a b (σ ij.1)) = ij.2 then 1 else 0

/-- Childs p.113 ((22.7)): `P(m, a, b) = E_{σ,τ}[p({δ^{στ}_{ij}})]`, the average over uniformly
random permutations `σ, τ` of `{1, …, n}`. -/
noncomputable def kutinAverage {n : ℕ} (p : MvPolynomial (Fin n × Fin n) ℝ) (m a b : ℕ) : ℝ :=
  (((n ! : ℕ) : ℝ) ^ 2)⁻¹ *
    ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n), MvPolynomial.eval (kutinDelta n m a b σ τ) p

/-! ### Sanity tests -/

example : IsMultilinear (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ) := by
  intro i
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  rw [MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_X]
  fin_cases i <;> simp

/-- The average of the constant polynomial `1` over a nonempty weight class is `1`. -/
example : weightAverage (1 : MvPolynomial (Fin 2) ℝ) 1 = 1 := by
  simp only [weightAverage, map_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [show (Finset.univ.filter fun x : Fin 2 → Bool => hammingWeight x = 1).card = 2 by decide]
  norm_num

/-- `x^{m,1,1}` is the identity (one-to-one) input, `x^{n,2,b}` pairs up consecutive positions
(two-to-one): at `n = 4`, `x^{4,2,1} = (1, 1, 2, 2)` (stored 0-based). -/
example : kutinInput 4 0 1 1 = id ∧ (List.ofFn (kutinInput 4 4 2 1)).map Fin.val = [0, 0, 1, 1] := by
  refine ⟨funext fun p => ?_, by decide⟩
  fin_cases p <;> decide

end QAlgorithms
