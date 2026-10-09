import QAlgorithms.Defs.Learning

/-!
# The hard instances of the PGM lower bounds (shared definition layer)

S. Arunachalam, *Quantum Algorithms and Learning Theory* (PhD thesis, 2018), §7.5–7.6, cited
"Arunachalam p.N" (PDF pages). A linear code has generator matrix `M ∈ F₂^{d×k}`
(`Matrix (Fin d) (Fin k) (ZMod 2)`) and codewords `Mx`, `x ∈ {0,1}^k`. The shattered set is
represented by its labels: `{s_0, …, s_d}` is `Fin (d + 1)` (`s_0` is `0`, `s_i` is `i` for
`i ∈ [d]`), and `{s_1, …, s_d}` is `Fin d` (`s_i` is `i − 1`).
-/

namespace QAlgorithms.Learning

/-- Arunachalam p.176 (proof of Thm 7.5.6) and p.182 (§7.6.2): the codeword `Mx` read as a
Boolean function on `[d]`, `i ↦ ((Mx)_i = 1)`. -/
def codeConcept {d k : ℕ} (M : Matrix (Fin d) (Fin k) (ZMod 2)) (x : Fin k → ZMod 2) :
    Fin d → Bool :=
  fun i => decide ((M.mulVec x) i = 1)

/-- Arunachalam p.176 (proof of Thm 7.5.6): the concept `c^x` on the shattered set
`{s_0, …, s_d}`, with `c^x(s_0) = 0` and `c^x(s_i) = (Mx)_i` for `i ∈ [d]`. -/
def pacHardConcept {d k : ℕ} (M : Matrix (Fin d) (Fin k) (ZMod 2)) (x : Fin k → ZMod 2) :
    Fin (d + 1) → Bool :=
  Fin.cons false (codeConcept M x)

/-- Arunachalam p.175 (proof of Thm 7.5.6): the distribution `D(s_0) = 1 − 20ε`,
`D(s_i) = 20ε/d` for `i ∈ [d]`. The state `|ψ_x⟩` of Lemma 7.5.7 is
`exampleState (pacHardConcept M x) (pacHardDist d ε)`. -/
noncomputable def pacHardDist (d : ℕ) (ε : ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons (1 - 20 * ε) fun _ => 20 * ε / (d : ℝ)

/-- Arunachalam p.178 (proof of Thm 7.5.8) and p.179 (Lemma 7.5.9): the distribution
`D_x(s_i, b) = (1/d)(1/2 + (1/2)(−1)^{(Mx)_i + b} α)` on `[d] × {0,1}`, with `α = 10ε`, the value
with which the proof of Lemma 7.5.9 computes (`√(D_x D_y) = (1/2d)√((1 ± 10ε)(1 ± 10ε))`); the
text's "α = 20ε" on p.178 contradicts that computation (recorded correction). The sign is `+`
exactly when `b = (Mx)_i`. `|ψ_x⟩` of Lemma 7.5.9 is `agnosticExampleState (agnHardDist M ε x)`. -/
noncomputable def agnHardDist {d k : ℕ} (M : Matrix (Fin d) (Fin k) (ZMod 2)) (ε : ℝ)
    (x : Fin k → ZMod 2) : Fin d × Bool → ℝ :=
  fun p => (1 + 10 * ε * (if p.2 = codeConcept M x p.1 then 1 else -1)) / (2 * (d : ℝ))

/-! ### Sanity tests -/

example {d k : ℕ} (M : Matrix (Fin d) (Fin k) (ZMod 2)) : codeConcept M 0 = fun _ => false := by
  funext i
  simp [codeConcept]

example {d k : ℕ} (M : Matrix (Fin d) (Fin k) (ZMod 2)) (x : Fin k → ZMod 2) :
    pacHardConcept M x 0 = false := rfl

example {d k : ℕ} (M : Matrix (Fin d) (Fin k) (ZMod 2)) (x : Fin k → ZMod 2) (i : Fin d) :
    pacHardConcept M x i.succ = codeConcept M x i := rfl

theorem pacHardDist_sum {d : ℕ} (hd : 1 ≤ d) (ε : ℝ) : ∑ i, pacHardDist d ε i = 1 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  rw [Fin.sum_univ_succ]
  simp only [pacHardDist, Fin.cons_zero, Fin.cons_succ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem agnHardDist_sum {d k : ℕ} (hd : 1 ≤ d) (M : Matrix (Fin d) (Fin k) (ZMod 2)) (ε : ℝ)
    (x : Fin k → ZMod 2) : ∑ p, agnHardDist M ε x p = 1 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have h : ∀ i : Fin d, ∑ b : Bool, agnHardDist M ε x (i, b) = 1 / (d : ℝ) := by
    intro i
    rw [Fintype.sum_bool]
    cases h : codeConcept M x i <;> simp [agnHardDist, h] <;> field_simp <;> ring
  rw [Fintype.sum_prod_type]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end QAlgorithms.Learning
