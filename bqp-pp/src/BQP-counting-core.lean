import «BQP-closed-references»

/-! Counting infrastructure for BQP ⊆ PP. Only the axiom-audited reference exports
are used. The elementary complement proof follows `wave30/done_CLOSE-COMBb.lean`;
the head-bit split is proved here with the coordinate convention the router needs.
This module makes no polynomial-time claim about the concrete router. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace BQPCounting
open ShiClassPP

private lemma count_sum (R : List Bool × List Bool → Bool) (x : List Bool) (m : ℕ) :
    countAccept R x m = ∑ b : Fin m → Bool,
      if R (x, List.ofFn b) = true then 1 else 0 := by
  simp only [countAccept, Finset.card_filter]

theorem count_le (R : List Bool × List Bool → Bool) (x : List Bool) (m : ℕ) :
    countAccept R x m ≤ 2 ^ m := by
  unfold countAccept
  calc
    _ ≤ (Finset.univ : Finset (Fin m → Bool)).card := Finset.card_filter_le _ _
    _ = _ := by simp [Fintype.card_fun]

theorem gap_complement (R : List Bool × List Bool → Bool) (x : List Bool) (m : ℕ) :
    gap (fun p => !(R p)) x m = -gap R x m := by
  have hc : countAccept R x m + countAccept (fun p => !(R p)) x m = 2 ^ m := by
    rw [count_sum, count_sum, ← Finset.sum_add_distrib]
    have h : ∀ b : Fin m → Bool,
        ((if R (x, List.ofFn b) = true then 1 else 0) +
          (if (!(R (x, List.ofFn b))) = true then 1 else 0) : ℕ) = 1 := by
      intro b
      cases hb : R (x, List.ofFn b) <;> simp
    rw [Finset.sum_congr rfl (fun b _ => h b)]
    simp [Fintype.card_fun]
  have hz : (countAccept R x m : ℤ) + countAccept (fun p => !(R p)) x m = 2 ^ m := by
    exact_mod_cast hc
  simp only [gap]
  linarith

private def headEquiv (m : ℕ) : Bool × (Fin m → Bool) ≃ (Fin (m + 1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun b := (b 0, fun i => b i.succ)
  left_inv := by intro p; simp
  right_inv := by
    intro b
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem gap_first_bit (R R₁ R₂ : List Bool × List Bool → Bool)
    (x : List Bool) (m : ℕ)
    (h : ∀ b : Fin (m + 1) → Bool, R (x, List.ofFn b) =
      if b 0 then R₂ (x, List.ofFn (fun i : Fin m => b i.succ))
      else R₁ (x, List.ofFn (fun i : Fin m => b i.succ))) :
    gap R x (m + 1) = gap R₁ x m + gap R₂ x m := by
  have hc : countAccept R x (m + 1) = countAccept R₁ x m + countAccept R₂ x m := by
    rw [count_sum, count_sum, count_sum]
    rw [← Fintype.sum_equiv (headEquiv m)
      (fun p => if R (x, List.ofFn (Fin.cons p.1 p.2)) = true then (1 : ℕ) else 0)
      (fun b => if R (x, List.ofFn b) = true then (1 : ℕ) else 0) (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [hu, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [h, Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte]
  simp only [gap, hc]
  push_cast
  ring

theorem gap_suffix (m n : ℕ) (R : List Bool × List Bool → Bool)
    (F : (Fin n → Bool) → List Bool × List Bool → Bool) (x : List Bool)
    (h : ∀ b : Fin (m + n) → Bool, R (x, List.ofFn b) =
      F (fun j => b (Fin.natAdd m j))
        (x, List.ofFn (fun i => b (Fin.castAdd n i)))) :
    gap R x (m + n) = ∑ v : Fin n → Bool, gap (F v) x m :=
  (BQPChecked.reference23.1 m n R F x h).2

/-- The explicit bucket router, including the balanced tail for unused bucket codes. -/
def combinedChecker (hh : List Bool → ℕ) (Rc : ℕ → List Bool × List Bool → Bool)
    (p : List Bool × List Bool) : Bool :=
  let x := p.1
  let w := p.2
  let v := (w.drop (2 * hh x)).foldr (fun b r => (bif b then 1 else 0) + 2 * r) 0
  let A := 2 ^ (hh x + 4)
  let S := Nat.sqrt (2 * 4 ^ (hh x + 3))
  if v < A then Rc 0 (x, w.take (2 * hh x))
  else if v < 2 * A then !(Rc 4 (x, w.take (2 * hh x)))
  else if v < 2 * A + 2 * S then Rc 1 (x, w.take (2 * hh x))
  else if v < 2 * A + 4 * S then !(Rc 3 (x, w.take (2 * hh x)))
  else if v < 2 * A + 4 * S + 16 then false
  else (w.take (2 * hh x)).headI

/-- All three counting-helper premises of the recovered router theorem are discharged. -/
theorem combined_gap (hh : List Bool → ℕ) (Rc : ℕ → List Bool × List Bool → Bool)
    (x : List Bool) (N : ℕ) (hpos : 1 ≤ hh x) (hbudget : 3 * hh x + 7 ≤ N) :
    gap (combinedChecker hh Rc) x N =
      2 * ((gap (Rc 0) x (2 * hh x) - gap (Rc 4) x (2 * hh x) - 2 ^ hh x)
        * 2 ^ (hh x + 3) + (gap (Rc 1) x (2 * hh x) - gap (Rc 3) x (2 * hh x))
        * (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)) := by
  exact ((BQPChecked.reference10 gap_suffix gap_complement gap_first_bit).2.1
    hh Rc (combinedChecker hh Rc) (by
      intro x w v A S hv hA hS
      subst v; subst A; subst S
      rfl)).1 x N hpos hbudget

/-- The two integer coefficients are differences of actual accepting counts. -/
def coefficient (hh : List Bool → ℕ) (Rc : ℕ → List Bool × List Bool → Bool)
    (a b : ℕ) (x : List Bool) : ℤ :=
  (countAccept (Rc a) x (2 * hh x) : ℤ) - countAccept (Rc b) x (2 * hh x)

theorem combined_gap_counts (hh : List Bool → ℕ) (Rc : ℕ → List Bool × List Bool → Bool)
    (x : List Bool) (N : ℕ) (hpos : 1 ≤ hh x) (hbudget : 3 * hh x + 7 ≤ N) :
    gap (combinedChecker hh Rc) x N =
      2 * ((2 * coefficient hh Rc 0 4 x - 2 ^ hh x) * 2 ^ (hh x + 3)
        + 2 * coefficient hh Rc 1 3 x * (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)) := by
  rw [combined_gap hh Rc x N hpos hbudget]
  simp only [gap, coefficient]
  ring

end BQPCounting
