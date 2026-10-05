import «BQP-counting-core»

/-! The numerical part of the BQP-to-PP reduction. The acceptance representation
and the polynomial-time implementation remain separate construction obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace BQPCounting
open ShiClassPP

theorem coefficient_bound (hh : List Bool → ℕ)
    (Rc : ℕ → List Bool × List Bool → Bool) (x : List Bool) :
    (coefficient hh Rc 1 3 x).natAbs ≤ 4 ^ hh x := by
  exact (BQPChecked.reference6.2.2.2.2.1 Rc x (hh x)
    (fun d => countAccept (Rc d) x (2 * hh x)) count_le (fun _ => rfl)).2.2.2.2.1

/-- The acceptance promise determines the integer sign without an assumed precision lemma. -/
theorem integer_sign (P : Prop) (h : ℕ) (A B : ℤ) (p : ℝ)
    (hB : B.natAbs ≤ 4 ^ h)
    (hp : p = (1 / 2 : ℝ) ^ h * ((A : ℝ) + (B : ℝ) * Real.sqrt 2))
    (hyes : P → (2 : ℝ) / 3 ≤ p) (hno : ¬P → p ≤ (1 : ℝ) / 3) :
    P ↔ 0 < (2 * A - 2 ^ h) * 2 ^ (h + 3)
      + 2 * B * (Nat.sqrt (2 * 4 ^ (h + 3)) : ℤ) := by
  classical
  have hshift := BQPChecked.reference6.1 h A B p hp
  have hsqrt := BQPChecked.reference6.2.2.1 (h + 3)
  have hmargin : (2 : ℝ) ^ h / 3 ≤ ((2 * A - 2 ^ h : ℤ) : ℝ)
        + 2 * (B : ℝ) * Real.sqrt 2 ∨
      ((2 * A - 2 ^ h : ℤ) : ℝ) + 2 * (B : ℝ) * Real.sqrt 2
        ≤ -((2 : ℝ) ^ h / 3) := by
    by_cases hP : P
    · exact Or.inl (hshift.2.1 (hyes hP))
    · exact Or.inr (hshift.2.2 (hno hP))
  have he := BQPChecked.reference6.2.1 h (2 * A - 2 ^ h) B
    (2 ^ (h + 3)) (Nat.sqrt (2 * 4 ^ (h + 3))) rfl
    hsqrt.1 hsqrt.2.1 hsqrt.2.2 hB hmargin
  have hpositive : 0 < (2 : ℝ) ^ h / 3 := by positivity
  rw [← he]
  constructor
  · intro hP
    have hm := hshift.2.1 (hyes hP)
    linarith
  · intro hg
    by_contra hP
    have hm := hshift.2.2 (hno hP)
    linarith

/-- Correctness at every sufficiently large witness length; no all-input budget is assumed. -/
theorem combined_gap_positive_iff (hh : List Bool → ℕ)
    (Rc : ℕ → List Bool × List Bool → Bool) (x : List Bool) (N : ℕ)
    (P : Prop) (p : ℝ) (hpos : 1 ≤ hh x) (hbudget : 3 * hh x + 7 ≤ N)
    (hp : p = (1 / 2 : ℝ) ^ hh x *
      ((coefficient hh Rc 0 4 x : ℝ) + (coefficient hh Rc 1 3 x : ℝ) * Real.sqrt 2))
    (hyes : P → (2 : ℝ) / 3 ≤ p) (hno : ¬P → p ≤ (1 : ℝ) / 3) :
    P ↔ 0 < gap (combinedChecker hh Rc) x N := by
  rw [combined_gap_counts hh Rc x N hpos hbudget]
  have hi := integer_sign P (hh x) (coefficient hh Rc 0 4 x)
    (coefficient hh Rc 1 3 x) p (coefficient_bound hh Rc x) hp hyes hno
  constructor
  · intro hP
    have := hi.mp hP
    omega
  · intro hg
    apply hi.mpr
    omega

theorem gap_pos_iff_majority (R : List Bool × List Bool → Bool) (x : List Bool) (N : ℕ) :
    0 < gap R x N ↔ 2 * countAccept R x N > 2 ^ N := by
  unfold gap
  rw [sub_pos]
  constructor <;> intro h <;> exact_mod_cast h

/-- A polynomial upper bound supplies one witness exponent on inputs of length at least two. -/
theorem exists_long_budget (hh : List Bool → ℕ) (r : Polynomial ℕ)
    (hr : ∀ x, hh x ≤ r.eval x.length + 1) :
    ∃ k : ℕ, ∀ x : List Bool, 2 ≤ x.length → 3 * hh x + 7 ≤ x.length ^ k := by
  obtain ⟨k, hk⟩ := BQPChecked.reference11.2.2.2.1 r
  refine ⟨k, fun x hx => ?_⟩
  have hb := hk x.length hx
  have hhx := hr x
  omega

/-- Long-input majority correctness. The acceptance representation is an explicit
remaining interface to the quantum path-counting proof, not a new definition of BQP. -/
theorem long_majority (L : Language Bool) (hh : List Bool → ℕ)
    (Rc : ℕ → List Bool × List Bool → Bool) (p : List Bool → ℝ)
    (r : Polynomial ℕ) (hr : ∀ x, hh x ≤ r.eval x.length + 1)
    (hpos : ∀ x, 2 ≤ x.length → 1 ≤ hh x)
    (hp : ∀ x, 2 ≤ x.length → p x = (1 / 2 : ℝ) ^ hh x *
      ((coefficient hh Rc 0 4 x : ℝ) + (coefficient hh Rc 1 3 x : ℝ) * Real.sqrt 2))
    (hyes : ∀ x, x ∈ L → (2 : ℝ) / 3 ≤ p x)
    (hno : ∀ x, x ∉ L → p x ≤ (1 : ℝ) / 3) :
    ∃ k : ℕ, ∀ x : List Bool, 2 ≤ x.length →
      (x ∈ L ↔ 2 * countAccept (combinedChecker hh Rc) x (x.length ^ k) > 2 ^ (x.length ^ k)) := by
  obtain ⟨k, hk⟩ := exists_long_budget hh r hr
  refine ⟨k, fun x hx => ?_⟩
  exact (combined_gap_positive_iff hh Rc x (x.length ^ k) (x ∈ L) (p x)
    (hpos x hx) (hk x hx) (hp x hx) (hyes x) (hno x)).trans
    (gap_pos_iff_majority _ _ _)

/-- Finite dispatch; the long branch preserves the entire input and witness. -/
def shortChecker (c₀ c₁ c₂ : Bool) (R : List Bool × List Bool → Bool)
    (p : List Bool × List Bool) : Bool :=
  match p.1 with
  | [] => c₀
  | [false] => c₁
  | [true] => c₂
  | _ => R p

/-- Constant short branches work for every exponent, including the `0^0` convention.
This proves counting correctness only; a machine for `shortChecker` is still needed. -/
theorem patched_majority (L : Language Bool) (R : List Bool × List Bool → Bool)
    (k : ℕ) (c₀ c₁ c₂ : Bool)
    (h₀ : c₀ = true ↔ [] ∈ L) (h₁ : c₁ = true ↔ [false] ∈ L)
    (h₂ : c₂ = true ↔ [true] ∈ L)
    (hlong : ∀ x : List Bool, 2 ≤ x.length →
      (x ∈ L ↔ 2 * countAccept R x (x.length ^ k) > 2 ^ (x.length ^ k))) :
    ∀ x : List Bool, x ∈ L ↔
      2 * countAccept (shortChecker c₀ c₁ c₂ R) x (x.length ^ k) > 2 ^ (x.length ^ k) := by
  intro x
  cases x with
  | nil =>
      exact h₀.symm.trans (BQPChecked.reference24.2.2.2.2.1
        (shortChecker c₀ c₁ c₂ R) [] c₀ (0 ^ k) (fun _ => rfl)).symm
  | cons b xs =>
      cases xs with
      | nil =>
          cases b
          · exact h₁.symm.trans (BQPChecked.reference24.2.2.2.2.1
              (shortChecker c₀ c₁ c₂ R) [false] c₁ (1 ^ k) (fun _ => rfl)).symm
          · exact h₂.symm.trans (BQPChecked.reference24.2.2.2.2.1
              (shortChecker c₀ c₁ c₂ R) [true] c₂ (1 ^ k) (fun _ => rfl)).symm
      | cons c xs =>
          have he : ∀ w, shortChecker c₀ c₁ c₂ R (b :: c :: xs, w) = R (b :: c :: xs, w) := by
            intro w
            cases b <;> rfl
          simpa only [countAccept, he] using hlong (b :: c :: xs) (by simp)

end BQPCounting
