import Definitions.Def_ShiClassPP
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiBQP_explicit_combined_checker_and_the_conditional_pp_membership

namespace BQPReferenceValidation.Source10
/-
RF-BUILDc -- the EXPLICIT combined checker `Rf` for `BQP ⊆ PP`, and its gap identity,
stated for the published counting scaffold `ShiClassPP.countAccept` / `ShiClassPP.gap`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Finset

/-- little-endian value of a bit list -/
private def vB (l : List Bool) : ℕ :=
  l.foldr (fun b r => (bif b then 1 else 0) + 2 * r) 0

private lemma vB_cons (b : Bool) (t : List Bool) :
    vB (b :: t) = (bif b then 1 else 0) + 2 * vB t := rfl

/-- the explicit case dispatcher: `v` is the case index, `p` the (input, inner witness) pair -/
private def ck (hh : List Bool → ℕ) (Rc : ℕ → List Bool × List Bool → Bool)
    (x : List Bool) (v : ℕ) : List Bool × List Bool → Bool :=
  fun p =>
    if v < 2 ^ (hh x + 4) then Rc 0 p
    else if v < 2 * 2 ^ (hh x + 4) then !(Rc 4 p)
    else if v < 2 * 2 ^ (hh x + 4) + 2 * Nat.sqrt (2 * 4 ^ (hh x + 3)) then Rc 1 p
    else if v < 2 * 2 ^ (hh x + 4) + 4 * Nat.sqrt (2 * 4 ^ (hh x + 3)) then !(Rc 3 p)
    else if v < 2 * 2 ^ (hh x + 4) + 4 * Nat.sqrt (2 * 4 ^ (hh x + 3)) + 16 then false
    else p.2.headI

private lemma ck_def (hh : List Bool → ℕ) (Rc : ℕ → List Bool × List Bool → Bool)
    (x : List Bool) (v : ℕ) :
    ck hh Rc x v = fun p =>
      (if v < 2 ^ (hh x + 4) then Rc 0 p
      else if v < 2 * 2 ^ (hh x + 4) then !(Rc 4 p)
      else if v < 2 * 2 ^ (hh x + 4) + 2 * Nat.sqrt (2 * 4 ^ (hh x + 3)) then Rc 1 p
      else if v < 2 * 2 ^ (hh x + 4) + 4 * Nat.sqrt (2 * 4 ^ (hh x + 3)) then !(Rc 3 p)
      else if v < 2 * 2 ^ (hh x + 4) + 4 * Nat.sqrt (2 * 4 ^ (hh x + 3)) + 16 then false
      else p.2.headI) := rfl

/-- the combined checker itself -/
private def rfOf (hh : List Bool → ℕ) (Rc : ℕ → List Bool × List Bool → Bool) :
    List Bool × List Bool → Bool :=
  fun p => ck hh Rc p.1 (vB (p.2.drop (2 * hh p.1))) (p.1, p.2.take (2 * hh p.1))

private lemma sumRange2 (G : ℕ → ℤ) : ∀ M : ℕ,
    (∑ k ∈ Finset.range M, (G (2 * k) + G (2 * k + 1)))
      = ∑ j ∈ Finset.range (2 * M), G j := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih, show 2 * (M + 1) = 2 * M + 1 + 1 from by ring,
        Finset.sum_range_succ, Finset.sum_range_succ]
      ring

private lemma sumVB : ∀ (n : ℕ) (G : ℕ → ℤ),
    (∑ v : Fin n → Bool, G (vB (List.ofFn v))) = ∑ k ∈ Finset.range (2 ^ n), G k := by
  intro n
  induction n with
  | zero =>
      intro G
      have hu : (Finset.univ : Finset (Fin 0 → Bool)) = {fun _ => false} := by
        refine Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_univ _, ?_⟩
        intro y _
        funext i
        exact absurd i.isLt (by omega)
      rw [hu, Finset.sum_singleton]
      simp [vB]
  | succ n ih =>
      intro G
      have e1 : (∑ p : Bool × (Fin n → Bool), G (vB (List.ofFn (Fin.cons p.1 p.2))))
          = ∑ v : Fin (n + 1) → Bool, G (vB (List.ofFn v)) :=
        Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)) _ _ (fun _ => rfl)
      have e2 : ∀ (b : Bool) (w : Fin n → Bool),
          List.ofFn (Fin.cons b w : Fin (n + 1) → Bool) = b :: List.ofFn w := by
        intro b w
        rw [List.ofFn_succ]
        simp
      rw [← e1, Fintype.sum_prod_type]
      simp only [e2, vB_cons]
      rw [Fintype.sum_bool]
      have hT : (∑ w : Fin n → Bool, G ((bif true then 1 else 0) + 2 * vB (List.ofFn w)))
          = ∑ k ∈ Finset.range (2 ^ n), G (1 + 2 * k) := ih (fun t => G (1 + 2 * t))
      have hF : (∑ w : Fin n → Bool, G ((bif false then 1 else 0) + 2 * vB (List.ofFn w)))
          = ∑ k ∈ Finset.range (2 ^ n), G (0 + 2 * k) := ih (fun t => G (0 + 2 * t))
      rw [hT, hF, ← Finset.sum_add_distrib]
      have hcg : (∑ k ∈ Finset.range (2 ^ n), (G (1 + 2 * k) + G (0 + 2 * k)))
          = ∑ k ∈ Finset.range (2 ^ n), (G (2 * k) + G (2 * k + 1)) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [show 1 + 2 * k = 2 * k + 1 from by omega, show 0 + 2 * k = 2 * k from by omega]
        ring
      rw [hcg, sumRange2 G (2 ^ n), show (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n from by ring]

private lemma sum_const_Ico (G : ℕ → ℤ) (t t' : ℕ) (c : ℤ)
    (hc : ∀ k, t ≤ k → k < t' → G k = c) :
    (∑ k ∈ Finset.Ico t t', G k) = ((t' - t : ℕ) : ℤ) * c := by
  have hall : ∀ k ∈ Finset.Ico t t', G k = c := fun k hk =>
    hc k (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2
  rw [Finset.sum_congr rfl hall, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

private lemma sum_buckets (G : ℕ → ℤ) (t1 t2 t3 t4 t5 t6 : ℕ) (c1 c2 c3 c4 c5 : ℤ)
    (h1 : t1 ≤ t2) (h2 : t2 ≤ t3) (h3 : t3 ≤ t4) (h4 : t4 ≤ t5) (h5 : t5 ≤ t6)
    (g1 : ∀ k, k < t1 → G k = c1)
    (g2 : ∀ k, t1 ≤ k → k < t2 → G k = c2)
    (g3 : ∀ k, t2 ≤ k → k < t3 → G k = c3)
    (g4 : ∀ k, t3 ≤ k → k < t4 → G k = c4)
    (g5 : ∀ k, t4 ≤ k → k < t5 → G k = c5)
    (g6 : ∀ k, t5 ≤ k → k < t6 → G k = 0) :
    (∑ k ∈ Finset.range t6, G k)
      = (t1 : ℤ) * c1 + ((t2 - t1 : ℕ) : ℤ) * c2 + ((t3 - t2 : ℕ) : ℤ) * c3
        + ((t4 - t3 : ℕ) : ℤ) * c4 + ((t5 - t4 : ℕ) : ℤ) * c5 := by
  have hA : (∑ k ∈ Finset.Ico 0 t1, G k) = ((t1 - 0 : ℕ) : ℤ) * c1 :=
    sum_const_Ico G 0 t1 c1 (fun k _ hk2 => g1 k hk2)
  have hB : (∑ k ∈ Finset.Ico t1 t2, G k) = ((t2 - t1 : ℕ) : ℤ) * c2 :=
    sum_const_Ico G t1 t2 c2 g2
  have hC : (∑ k ∈ Finset.Ico t2 t3, G k) = ((t3 - t2 : ℕ) : ℤ) * c3 :=
    sum_const_Ico G t2 t3 c3 g3
  have hD : (∑ k ∈ Finset.Ico t3 t4, G k) = ((t4 - t3 : ℕ) : ℤ) * c4 :=
    sum_const_Ico G t3 t4 c4 g4
  have hE : (∑ k ∈ Finset.Ico t4 t5, G k) = ((t5 - t4 : ℕ) : ℤ) * c5 :=
    sum_const_Ico G t4 t5 c5 g5
  have hZ : (∑ k ∈ Finset.Ico t5 t6, G k) = ((t6 - t5 : ℕ) : ℤ) * 0 :=
    sum_const_Ico G t5 t6 0 g6
  have l16 : t1 ≤ t6 := by omega
  have l26 : t2 ≤ t6 := by omega
  have l36 : t3 ≤ t6 := by omega
  have l46 : t4 ≤ t6 := by omega
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive G (Nat.zero_le t1) l16,
    ← Finset.sum_Ico_consecutive G h1 l26,
    ← Finset.sum_Ico_consecutive G h2 l36,
    ← Finset.sum_Ico_consecutive G h3 l46,
    ← Finset.sum_Ico_consecutive G h4 h5, hA, hB, hC, hD, hE, hZ]
  simp only [Nat.sub_zero, mul_zero, add_zero]
  ring

private lemma sqrtBound (h : ℕ) : Nat.sqrt (2 * 4 ^ (h + 3)) ≤ 2 ^ (h + 4) := by
  have a1 : (2 : ℕ) ^ (h + 4) * 2 ^ (h + 4) = 4 ^ (h + 4) := by
    rw [← mul_pow]
    norm_num
  have e1 : (2 : ℕ) ^ (h + 4) * 2 ^ (h + 4) = 4 * 4 ^ (h + 3) := by
    rw [a1, show h + 4 = h + 3 + 1 from by omega, pow_succ]
    ring
  have e2 : 2 * 4 ^ (h + 3) ≤ 2 ^ (h + 4) * 2 ^ (h + 4) := by
    rw [e1]
    have hz : (0 : ℕ) ≤ 4 ^ (h + 3) := Nat.zero_le _
    omega
  calc Nat.sqrt (2 * 4 ^ (h + 3)) ≤ Nat.sqrt (2 ^ (h + 4) * 2 ^ (h + 4)) :=
        Nat.sqrt_le_sqrt e2
    _ = 2 ^ (h + 4) := Nat.sqrt_eq _

private lemma fitBound (h : ℕ) :
    2 * 2 ^ (h + 4) + 4 * Nat.sqrt (2 * 4 ^ (h + 3)) + 16 ≤ 2 ^ (h + 7) := by
  have hS := sqrtBound h
  have hp : (16 : ℕ) ≤ 2 ^ (h + 4) := by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (h + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h7 : (2 : ℕ) ^ (h + 7) = 8 * 2 ^ (h + 4) := by ring
  omega

theorem _root_.BQPReferenceValidation.candidate10 :
      -- (H2) `LINCOMBb` conjunct (a): the N-ary split
      
      (∀ (m n : ℕ) (R : List Bool × List Bool → Bool)
          (F : (Fin n → Bool) → List Bool × List Bool → Bool) (x : List Bool),
          (∀ b : Fin (m + n) → Bool, R (x, List.ofFn b)
            = F (fun j : Fin n => b (Fin.natAdd m j))
                (x, List.ofFn (fun i : Fin m => b (Fin.castAdd n i)))) →
          ShiClassPP.gap R x (m + n) = ∑ v : Fin n → Bool, ShiClassPP.gap (F v) x m) →
      -- (H3) the complement flips the gap
      (∀ (R : List Bool × List Bool → Bool) (x : List Bool) (m : ℕ),
          ShiClassPP.gap (fun p => !(R p)) x m = -ShiClassPP.gap R x m) →
      -- (H4) the first-bit split
      (∀ (R R₁ R₂ : List Bool × List Bool → Bool) (x : List Bool) (m : ℕ),
          (∀ b : Fin (m + 1) → Bool, R (x, List.ofFn b)
            = if b 0 then R₂ (x, List.ofFn (fun i : Fin m => b i.succ))
              else R₁ (x, List.ofFn (fun i : Fin m => b i.succ))) →
          ShiClassPP.gap R x (m + 1) = ShiClassPP.gap R₁ x m + ShiClassPP.gap R₂ x m) →
      -- (1) THE CASE BUDGET FITS: `h + 7` case bits hold every bucket.
      (∀ h : ℕ, 2 * 2 ^ (h + 4) + 4 * Nat.sqrt (2 * 4 ^ (h + 3)) + 16 ≤ 2 ^ (h + 7))
    ∧ -- (2) THE EXPLICIT COMBINED CHECKER and its gap identity.
      (∀ (hh : List Bool → ℕ) (Rc : ℕ → List Bool × List Bool → Bool)
          (Rf : List Bool × List Bool → Bool),
          (∀ (x w : List Bool) (v A S : ℕ),
              v = (w.drop (2 * hh x)).foldr (fun b r => (bif b then 1 else 0) + 2 * r) 0 →
              A = 2 ^ (hh x + 4) → S = Nat.sqrt (2 * 4 ^ (hh x + 3)) →
              Rf (x, w)
                = (if v < A then Rc 0 (x, w.take (2 * hh x))
                  else if v < 2 * A then !(Rc 4 (x, w.take (2 * hh x)))
                  else if v < 2 * A + 2 * S then Rc 1 (x, w.take (2 * hh x))
                  else if v < 2 * A + 4 * S then !(Rc 3 (x, w.take (2 * hh x)))
                  else if v < 2 * A + 4 * S + 16 then false
                  else (w.take (2 * hh x)).headI)) →
          -- (2a) the raw gap identity, at ANY witness length `N ≥ 3 * h + 7`
          (∀ (x : List Bool) (N : ℕ), 1 ≤ hh x → 3 * hh x + 7 ≤ N →
              ShiClassPP.gap Rf x N
                = 2 * ((ShiClassPP.gap (Rc 0) x (2 * hh x)
                          - ShiClassPP.gap (Rc 4) x (2 * hh x) - 2 ^ hh x)
                        * 2 ^ (hh x + 3)
                    + (ShiClassPP.gap (Rc 1) x (2 * hh x) - ShiClassPP.gap (Rc 3) x (2 * hh x))
                        * (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)))
        ∧ -- (2b) the consumer's form, in terms of the two integers `Av`, `Bv`
          (∀ (x : List Bool) (k : ℕ) (Av Bv : ℤ), 1 ≤ hh x →
              3 * hh x + 7 ≤ x.length ^ k →
              2 * Av = ShiClassPP.gap (Rc 0) x (2 * hh x) - ShiClassPP.gap (Rc 4) x (2 * hh x) →
              2 * Bv = ShiClassPP.gap (Rc 1) x (2 * hh x) - ShiClassPP.gap (Rc 3) x (2 * hh x) →
              ShiClassPP.gap Rf x (x.length ^ k)
                = 2 * ((2 * Av - 2 ^ hh x) * 2 ^ (hh x + 3)
                    + 2 * Bv * (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)))
        ∧ -- (2c) the same, read straight off the four counts
          (∀ (x : List Bool) (k : ℕ) (Nc : ℕ → ℕ), 1 ≤ hh x →
              3 * hh x + 7 ≤ x.length ^ k →
              (∀ d : ℕ, ShiClassPP.countAccept (Rc d) x (2 * hh x) = Nc d) →
              ShiClassPP.gap Rf x (x.length ^ k)
                = 2 * ((2 * ((Nc 0 : ℤ) - (Nc 4 : ℤ)) - 2 ^ hh x) * 2 ^ (hh x + 3)
                    + 2 * ((Nc 1 : ℤ) - (Nc 3 : ℤ))
                        * (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)))
        ∧ -- (2d) THE HEADLINE, now conditional ONLY on `PolyTimeChecker Rf`.  Feeding
          -- (2b) into `ASM-CONS` conjunct (5) -- taken here as a hypothesis, since it is
          -- an accepted theorem -- puts `L` in the strict-majority counting class.
          (∀ (L : Language Bool) (k : ℕ) (Av Bv : List Bool → ℤ),
              (∀ (L' : Language Bool) (k' : ℕ) (hh' : List Bool → ℕ)
                  (Av' Bv' : List Bool → ℤ) (Rf' : List Bool × List Bool → Bool),
                  PvsNP.PolyTimeChecker Rf' →
                  (∀ x : List Bool, (Bv' x).natAbs ≤ 4 ^ hh' x) →
                  (∀ x : List Bool, x ∈ L' →
                      (2 : ℝ) / 3 ≤ (1 / 2 : ℝ) ^ hh' x
                        * ((Av' x : ℝ) + (Bv' x : ℝ) * Real.sqrt 2)) →
                  (∀ x : List Bool, x ∉ L' →
                      (1 / 2 : ℝ) ^ hh' x * ((Av' x : ℝ) + (Bv' x : ℝ) * Real.sqrt 2)
                        ≤ (1 : ℝ) / 3) →
                  (∀ x : List Bool, ShiClassPP.gap Rf' x (x.length ^ k')
                      = 2 * ((2 * Av' x - 2 ^ hh' x) * 2 ^ (hh' x + 3)
                          + 2 * Bv' x * (Nat.sqrt (2 * 4 ^ (hh' x + 3)) : ℤ))) →
                  L' ∈ ShiClassPP.PP) →
              PvsNP.PolyTimeChecker Rf →
              (∀ x : List Bool, 1 ≤ hh x) →
              (∀ x : List Bool, 3 * hh x + 7 ≤ x.length ^ k) →
              (∀ x : List Bool, 2 * Av x = ShiClassPP.gap (Rc 0) x (2 * hh x)
                  - ShiClassPP.gap (Rc 4) x (2 * hh x)) →
              (∀ x : List Bool, 2 * Bv x = ShiClassPP.gap (Rc 1) x (2 * hh x)
                  - ShiClassPP.gap (Rc 3) x (2 * hh x)) →
              (∀ x : List Bool, (Bv x).natAbs ≤ 4 ^ hh x) →
              (∀ x : List Bool, x ∈ L →
                  (2 : ℝ) / 3 ≤ (1 / 2 : ℝ) ^ hh x
                    * ((Av x : ℝ) + (Bv x : ℝ) * Real.sqrt 2)) →
              (∀ x : List Bool, x ∉ L →
                  (1 / 2 : ℝ) ^ hh x * ((Av x : ℝ) + (Bv x : ℝ) * Real.sqrt 2)
                    ≤ (1 : ℝ) / 3) →
              L ∈ ShiClassPP.PP))
    ∧ -- (3) NON-VACUITY: the defining equation IS satisfiable, its side conditions ARE
      -- simultaneously satisfiable, the dispatch genuinely reaches two different buckets
      -- with two different answers, and the realised right-hand side is not identically `0`.
      (∃ (hh : List Bool → ℕ) (Rc : ℕ → List Bool × List Bool → Bool)
          (Rf : List Bool × List Bool → Bool) (x : List Bool) (k : ℕ),
          (∀ (x0 w : List Bool) (v A S : ℕ),
              v = (w.drop (2 * hh x0)).foldr (fun b r => (bif b then 1 else 0) + 2 * r) 0 →
              A = 2 ^ (hh x0 + 4) → S = Nat.sqrt (2 * 4 ^ (hh x0 + 3)) →
              Rf (x0, w)
                = (if v < A then Rc 0 (x0, w.take (2 * hh x0))
                  else if v < 2 * A then !(Rc 4 (x0, w.take (2 * hh x0)))
                  else if v < 2 * A + 2 * S then Rc 1 (x0, w.take (2 * hh x0))
                  else if v < 2 * A + 4 * S then !(Rc 3 (x0, w.take (2 * hh x0)))
                  else if v < 2 * A + 4 * S + 16 then false
                  else (w.take (2 * hh x0)).headI))
        ∧ 1 ≤ hh x
        ∧ 3 * hh x + 7 ≤ x.length ^ k
        ∧ Rf (x, [false, false]) = false
        ∧ Rf (x, [false, false, false, false, false, false, false, true]) = true
        ∧ (2 : ℤ) * ((2 * 2 - 2 ^ hh x) * 2 ^ (hh x + 3)
            + 2 * 0 * (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)) ≠ 0) := by
  intro hsplit hcompl hperm
  have hcnt : ∀ (R : List Bool × List Bool → Bool) (x : List Bool) (m : ℕ),
      ShiClassPP.countAccept R x m
        = (Finset.univ.filter
            (fun b : Fin m → Bool => R (x, List.ofFn b) = true)).card := fun _ _ _ => rfl
  have hgp : ∀ (R : List Bool × List Bool → Bool) (x : List Bool) (m : ℕ),
      ShiClassPP.gap R x m = 2 * (ShiClassPP.countAccept R x m : ℤ) - 2 ^ m :=
    fun _ _ _ => rfl
  refine ⟨fitBound, ?_, ?_⟩
  · intro hh Rc Rf hRf
    have hfalse : ∀ (y : List Bool) (m : ℕ),
        ShiClassPP.gap (fun _ => false) y m = -(2 ^ m) := by
      intro y m
      have hu : (Finset.univ.filter (fun b : Fin m → Bool =>
            ((fun _ => false) : List Bool × List Bool → Bool) (y, List.ofFn b) = true))
          = (∅ : Finset (Fin m → Bool)) :=
        Finset.filter_false_of_mem (fun b _ => by simp)
      rw [hgp, hcnt, hu, Finset.card_empty]
      simp
    have htrue : ∀ (y : List Bool) (m : ℕ), ShiClassPP.gap (fun _ => true) y m = 2 ^ m := by
      intro y m
      have hu : (Finset.univ.filter (fun b : Fin m → Bool =>
            ((fun _ => true) : List Bool × List Bool → Bool) (y, List.ofFn b) = true))
          = (Finset.univ : Finset (Fin m → Bool)) :=
        Finset.filter_true_of_mem (fun b _ => rfl)
      rw [hgp, hcnt, hu, Finset.card_univ, Fintype.card_pi_const, Fintype.card_bool]
      push_cast
      ring
    have hzero : ∀ (y : List Bool) (m' : ℕ),
        ShiClassPP.gap (fun p : List Bool × List Bool => p.2.headI) y (m' + 1) = 0 := by
      intro y m'
      have hb0 : ∀ b : Fin (m' + 1) → Bool,
          (fun p : List Bool × List Bool => p.2.headI) (y, List.ofFn b)
            = if b 0 then ((fun _ => true) : List Bool × List Bool → Bool)
                (y, List.ofFn (fun i : Fin m' => b i.succ))
              else ((fun _ => false) : List Bool × List Bool → Bool)
                (y, List.ofFn (fun i : Fin m' => b i.succ)) := by
        intro b
        cases hb : b 0 <;> simp [List.ofFn_succ, hb]
      rw [hperm (fun p : List Bool × List Bool => p.2.headI) (fun _ => false)
        (fun _ => true) y m' hb0, hfalse, htrue]
      ring
    have hcore : ∀ (x : List Bool) (N : ℕ), 1 ≤ hh x → 3 * hh x + 7 ≤ N →
        ShiClassPP.gap Rf x N
          = 2 * ((ShiClassPP.gap (Rc 0) x (2 * hh x)
                    - ShiClassPP.gap (Rc 4) x (2 * hh x) - 2 ^ hh x)
                  * 2 ^ (hh x + 3)
              + (ShiClassPP.gap (Rc 1) x (2 * hh x) - ShiClassPP.gap (Rc 3) x (2 * hh x))
                  * (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)) := by
      intro x N h1 hN
      obtain ⟨n, rfl⟩ : ∃ n, N = 2 * hh x + n := ⟨N - 2 * hh x, by omega⟩
      have hn7 : hh x + 7 ≤ n := by omega
      have ht : ∀ b : Fin (2 * hh x + n) → Bool,
          (List.ofFn b).take (2 * hh x)
            = List.ofFn (fun i : Fin (2 * hh x) => b (Fin.castAdd n i)) := by
        intro b
        rw [List.ofFn_add]
        exact List.take_left' (by simp)
      have hd : ∀ b : Fin (2 * hh x + n) → Bool,
          (List.ofFn b).drop (2 * hh x)
            = List.ofFn (fun j : Fin n => b (Fin.natAdd (2 * hh x) j)) := by
        intro b
        rw [List.ofFn_add]
        exact List.drop_left' (by simp)
      have hF : ∀ b : Fin (2 * hh x + n) → Bool,
          Rf (x, List.ofFn b)
            = ck hh Rc x (vB (List.ofFn (fun j : Fin n => b (Fin.natAdd (2 * hh x) j))))
                (x, List.ofFn (fun i : Fin (2 * hh x) => b (Fin.castAdd n i))) := by
        intro b
        have hx1 := hRf x (List.ofFn b)
            (vB (List.ofFn (fun j : Fin n => b (Fin.natAdd (2 * hh x) j))))
            (2 ^ (hh x + 4)) (Nat.sqrt (2 * 4 ^ (hh x + 3)))
            (by rw [hd b]; rfl) rfl rfl
        simp only [ck, hx1, ht b]
      have hsp : ShiClassPP.gap Rf x (2 * hh x + n)
          = ∑ v : Fin n → Bool, ShiClassPP.gap (ck hh Rc x (vB (List.ofFn v))) x (2 * hh x) :=
        hsplit (2 * hh x) n Rf (fun v => ck hh Rc x (vB (List.ofFn v))) x hF
      have hsv : (∑ v : Fin n → Bool,
            ShiClassPP.gap (ck hh Rc x (vB (List.ofFn v))) x (2 * hh x))
          = ∑ k ∈ Finset.range (2 ^ n), ShiClassPP.gap (ck hh Rc x k) x (2 * hh x) :=
        sumVB n (fun w => ShiClassPP.gap (ck hh Rc x w) x (2 * hh x))
      obtain ⟨m', hm'⟩ : ∃ m', 2 * hh x = m' + 1 := ⟨2 * hh x - 1, by omega⟩
      have hzero2 : ShiClassPP.gap (fun p : List Bool × List Bool => p.2.headI)
          x (2 * hh x) = 0 := by
        rw [hm']
        exact hzero x m'
      have hfalse2 : ShiClassPP.gap (fun _ => false) x (2 * hh x) = -(2 ^ (2 * hh x)) := hfalse x _
      have hval : ∀ k : ℕ,
          ShiClassPP.gap (ck hh Rc x k) x (2 * hh x)
            = if k < 2 ^ (hh x + 4) then ShiClassPP.gap (Rc 0) x (2 * hh x)
              else if k < 2 * 2 ^ (hh x + 4) then -ShiClassPP.gap (Rc 4) x (2 * hh x)
              else if k < 2 * 2 ^ (hh x + 4) + 2 * Nat.sqrt (2 * 4 ^ (hh x + 3)) then
                ShiClassPP.gap (Rc 1) x (2 * hh x)
              else if k < 2 * 2 ^ (hh x + 4) + 4 * Nat.sqrt (2 * 4 ^ (hh x + 3)) then
                -ShiClassPP.gap (Rc 3) x (2 * hh x)
              else if k < 2 * 2 ^ (hh x + 4) + 4 * Nat.sqrt (2 * 4 ^ (hh x + 3)) + 16 then
                -(2 ^ (2 * hh x))
              else 0 := by
        intro k
        by_cases c1 : k < 2 ^ (hh x + 4)
        · simp only [ck_def, if_pos c1]
        · by_cases c2 : k < 2 * 2 ^ (hh x + 4)
          · simp only [ck_def, if_neg c1, if_pos c2]
            exact hcompl (Rc 4) x (2 * hh x)
          · by_cases c3 : k < 2 * 2 ^ (hh x + 4) + 2 * Nat.sqrt (2 * 4 ^ (hh x + 3))
            · simp only [ck_def, if_neg c1, if_neg c2, if_pos c3]
            · by_cases c4 : k < 2 * 2 ^ (hh x + 4) + 4 * Nat.sqrt (2 * 4 ^ (hh x + 3))
              · simp only [ck_def, if_neg c1, if_neg c2, if_neg c3, if_pos c4]
                exact hcompl (Rc 3) x (2 * hh x)
              · by_cases c5 :
                    k < 2 * 2 ^ (hh x + 4) + 4 * Nat.sqrt (2 * 4 ^ (hh x + 3)) + 16
                · simp only [ck_def, if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_pos c5]
                  exact hfalse2
                · simp only [ck_def, if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5]
                  exact hzero2
      have hfit : 2 * 2 ^ (hh x + 4) + 4 * Nat.sqrt (2 * 4 ^ (hh x + 3)) + 16 ≤ 2 ^ n :=
        le_trans (fitBound (hh x)) (Nat.pow_le_pow_right (by norm_num) (by omega))
      set A := 2 ^ (hh x + 4) with hAdef
      set S := Nat.sqrt (2 * 4 ^ (hh x + 3)) with hSdef
      have b1 : ∀ k, k < A → ShiClassPP.gap (ck hh Rc x k) x (2 * hh x)
          = ShiClassPP.gap (Rc 0) x (2 * hh x) :=
        fun k hk => by rw [hval k, if_pos hk]
      have b2 : ∀ k, A ≤ k → k < 2 * A →
          ShiClassPP.gap (ck hh Rc x k) x (2 * hh x) = -ShiClassPP.gap (Rc 4) x (2 * hh x) :=
        fun k hk1 hk2 => by rw [hval k, if_neg (by omega), if_pos hk2]
      have b3 : ∀ k, 2 * A ≤ k → k < 2 * A + 2 * S →
          ShiClassPP.gap (ck hh Rc x k) x (2 * hh x) = ShiClassPP.gap (Rc 1) x (2 * hh x) :=
        fun k hk1 hk2 => by
          rw [hval k, if_neg (by omega), if_neg (by omega), if_pos hk2]
      have b4 : ∀ k, 2 * A + 2 * S ≤ k → k < 2 * A + 4 * S →
          ShiClassPP.gap (ck hh Rc x k) x (2 * hh x) = -ShiClassPP.gap (Rc 3) x (2 * hh x) :=
        fun k hk1 hk2 => by
          rw [hval k, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hk2]
      have b5 : ∀ k, 2 * A + 4 * S ≤ k → k < 2 * A + 4 * S + 16 →
          ShiClassPP.gap (ck hh Rc x k) x (2 * hh x) = -(2 ^ (2 * hh x)) :=
        fun k hk1 hk2 => by
          rw [hval k, if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_pos hk2]
      have b6 : ∀ k, 2 * A + 4 * S + 16 ≤ k → k < 2 ^ n →
          ShiClassPP.gap (ck hh Rc x k) x (2 * hh x) = 0 :=
        fun k hk1 _ => by
          rw [hval k, if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_neg (by omega)]
      have hb : (∑ k ∈ Finset.range (2 ^ n), ShiClassPP.gap (ck hh Rc x k) x (2 * hh x))
          = (A : ℤ) * ShiClassPP.gap (Rc 0) x (2 * hh x)
            + ((2 * A - A : ℕ) : ℤ) * (-ShiClassPP.gap (Rc 4) x (2 * hh x))
            + ((2 * A + 2 * S - 2 * A : ℕ) : ℤ) * ShiClassPP.gap (Rc 1) x (2 * hh x)
            + ((2 * A + 4 * S - (2 * A + 2 * S) : ℕ) : ℤ)
                * (-ShiClassPP.gap (Rc 3) x (2 * hh x))
            + ((2 * A + 4 * S + 16 - (2 * A + 4 * S) : ℕ) : ℤ) * (-(2 ^ (2 * hh x))) :=
        sum_buckets (fun k => ShiClassPP.gap (ck hh Rc x k) x (2 * hh x))
          A (2 * A) (2 * A + 2 * S) (2 * A + 4 * S) (2 * A + 4 * S + 16) (2 ^ n)
          (ShiClassPP.gap (Rc 0) x (2 * hh x)) (-ShiClassPP.gap (Rc 4) x (2 * hh x))
          (ShiClassPP.gap (Rc 1) x (2 * hh x))
          (-ShiClassPP.gap (Rc 3) x (2 * hh x)) (-(2 ^ (2 * hh x)))
          (by omega) (by omega) (by omega) (by omega) hfit b1 b2 b3 b4 b5 b6
      have d2 : 2 * A - A = A := by omega
      have d3 : 2 * A + 2 * S - 2 * A = 2 * S := by omega
      have d4 : 2 * A + 4 * S - (2 * A + 2 * S) = 2 * S := by omega
      have d5 : 2 * A + 4 * S + 16 - (2 * A + 4 * S) = 16 := by omega
      rw [hsp, hsv, hb, d2, d3, d4, d5, hAdef]
      push_cast
      have q1 : (2 : ℤ) ^ (hh x + 4) = 2 ^ hh x * 16 := by
        rw [pow_add]
        norm_num
      have q2 : (2 : ℤ) ^ (hh x + 3) = 2 ^ hh x * 8 := by
        rw [pow_add]
        norm_num
      have q3 : (2 : ℤ) ^ (2 * hh x) = 2 ^ hh x * 2 ^ hh x := by
        rw [two_mul, pow_add]
      rw [q1, q2, q3]
      ring
    have hgap : ∀ (x : List Bool) (k : ℕ) (Av Bv : ℤ), 1 ≤ hh x →
        3 * hh x + 7 ≤ x.length ^ k →
        2 * Av = ShiClassPP.gap (Rc 0) x (2 * hh x)
            - ShiClassPP.gap (Rc 4) x (2 * hh x) →
        2 * Bv = ShiClassPP.gap (Rc 1) x (2 * hh x)
            - ShiClassPP.gap (Rc 3) x (2 * hh x) →
        ShiClassPP.gap Rf x (x.length ^ k)
          = 2 * ((2 * Av - 2 ^ hh x) * 2 ^ (hh x + 3)
              + 2 * Bv * (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)) := by
      intro x k Av Bv h1 hN hA hB
      rw [hcore x (x.length ^ k) h1 hN, ← hA, ← hB]
    refine ⟨hcore, hgap, ?_, ?_⟩
    · intro x k Nc h1 hN hNc
      have e0 : ShiClassPP.gap (Rc 0) x (2 * hh x) = 2 * (Nc 0 : ℤ) - 2 ^ (2 * hh x) := by
        rw [hgp, hNc 0]
      have e1 : ShiClassPP.gap (Rc 1) x (2 * hh x) = 2 * (Nc 1 : ℤ) - 2 ^ (2 * hh x) := by
        rw [hgp, hNc 1]
      have e3 : ShiClassPP.gap (Rc 3) x (2 * hh x) = 2 * (Nc 3 : ℤ) - 2 ^ (2 * hh x) := by
        rw [hgp, hNc 3]
      have e4 : ShiClassPP.gap (Rc 4) x (2 * hh x) = 2 * (Nc 4 : ℤ) - 2 ^ (2 * hh x) := by
        rw [hgp, hNc 4]
      rw [hcore x (x.length ^ k) h1 hN, e0, e1, e3, e4]
      ring
    · intro L k Av Bv hcons hpt h1 hN hA hB hBb hin hout
      exact hcons L k hh Av Bv Rf hpt hBb hin hout
        (fun x => hgap x k (Av x) (Bv x) (h1 x) (hN x) (hA x) (hB x))
  · refine ⟨fun _ => 1, fun _ _ => false, rfOf (fun _ => 1) (fun _ _ => false),
      [true, true], 4, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x0 w v A S hv hA hS
      subst hv
      subst hA
      subst hS
      rfl
    · norm_num
    · decide
    · rfl
    · rfl
    · norm_num

end BQPReferenceValidation.Source10

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate10
    let target ← getConstInfo ``ShiBQP.explicit_combined_checker_and_the_conditional_pp_membership
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.explicit_combined_checker_and_the_conditional_pp_membership"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.explicit_combined_checker_and_the_conditional_pp_membership"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.explicit_combined_checker_and_the_conditional_pp_membership"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate10
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.explicit_combined_checker_and_the_conditional_pp_membership; axioms {axioms}"
