import QIP.Uniform.SynPT
import QIP.Circuit.Predicates
import QIP.Circuit.Relabel
import QIP.Pair.Interleave


/-!
# Q34 — polynomial-time gate-list transformations

Relabelling, inversion and adjoints, Toffoli and controlled gates, the zero test `ztGates`
(through a closed form of its recursion), and the segment index `segIdx`.
-/

namespace ShiQIP.Uniform

open ShiQIP

/-! ### Relabelling and inversion -/

theorem relabel_eq (τ : ℕ → ℕ) (g : Gate) : g.relabel τ =
    Gate.ofCd (g.cd.1, τ g.cd.2.1, if g.cd.1 = 4 then τ g.cd.2.2 else 0) := by
  cases g <;> rfl

@[fun_prop] theorem PT.fp_relabel {α : Type} [Rep α] {τ : α → ℕ → ℕ} {g : α → Gate}
    (hτ : PT fun p : α × ℕ => τ p.1 p.2) (hg : PT g) : PT fun x => (g x).relabel (τ x) := by
  have h₁ : PT fun x => τ x (g x).cd.2.1 :=
    PT.comp (show PT fun x => (x, (g x).cd.2.1) by fun_prop) hτ
  have h₂ : PT fun x => τ x (g x).cd.2.2 :=
    PT.comp (show PT fun x => (x, (g x).cd.2.2) by fun_prop) hτ
  exact (show PT fun x => Gate.ofCd ((g x).cd.1, τ x (g x).cd.2.1,
    if (g x).cd.1 = 4 then τ x (g x).cd.2.2 else 0) by fun_prop).of_eq fun x => (relabel_eq _ _).symm

theorem inv_eq (g : Gate) : g.inv =
    if g.cd.1 = 1 then List.replicate 3 g else if g.cd.1 = 2 then List.replicate 7 g else [g] := by
  cases g <;> rfl

@[fun_prop] theorem PT.fp_inv {α : Type} [Rep α] {g : α → Gate} (hg : PT g) :
    PT fun x => (g x).inv :=
  (show PT fun x => if (g x).cd.1 = 1 then List.replicate 3 (g x) else if (g x).cd.1 = 2 then
    List.replicate 7 (g x) else [g x] by fun_prop).of_eq fun x => (inv_eq _).symm

@[fun_prop] theorem PT.fp_adjointGates {α : Type} [Rep α] {l : α → List Gate} (hl : PT l) :
    PT fun x => adjointGates (l x) := by
  unfold adjointGates; fun_prop

/-! ### Fixed gate templates -/

@[fun_prop] theorem PT.fp_swapGates {α : Type} [Rep α] {i j : α → ℕ} (hi : PT i) (hj : PT j) :
    PT fun x => swapGates (i x) (j x) := by unfold swapGates; fun_prop

@[fun_prop] theorem PT.fp_tdgGates {α : Type} [Rep α] {i : α → ℕ} (hi : PT i) :
    PT fun x => tdgGates (i x) := by unfold tdgGates; fun_prop

@[fun_prop] theorem PT.fp_sdgGates {α : Type} [Rep α] {i : α → ℕ} (hi : PT i) :
    PT fun x => sdgGates (i x) := by unfold sdgGates; fun_prop

@[fun_prop] theorem PT.fp_cczGates {α : Type} [Rep α] {a b c : α → ℕ} (ha : PT a) (hb : PT b)
    (hc : PT c) : PT fun x => cczGates (a x) (b x) (c x) := by unfold cczGates; fun_prop

@[fun_prop] theorem PT.fp_toffoliGates {α : Type} [Rep α] {a b c : α → ℕ} (ha : PT a) (hb : PT b)
    (hc : PT c) : PT fun x => toffoliGates (a x) (b x) (c x) := by unfold toffoliGates; fun_prop

@[fun_prop] theorem PT.fp_ncaGates {α : Type} [Rep α] {a b c : α → ℕ} (ha : PT a) (hb : PT b)
    (hc : PT c) : PT fun x => ncaGates (a x) (b x) (c x) := by unfold ncaGates; fun_prop

/-! ### Controlled gates -/

theorem ctrlGate_eq (c a : ℕ) (g : Gate) : ctrlGate c a g =
    if g.cd.1 = 0 then sdgGates g.cd.2.1 ++ [.h g.cd.2.1] ++ tdgGates g.cd.2.1 ++
        [.cnot c g.cd.2.1, .t g.cd.2.1, .h g.cd.2.1, .s g.cd.2.1]
    else if g.cd.1 = 1 then [.t c, .t g.cd.2.1, .cnot c g.cd.2.1] ++ tdgGates g.cd.2.1 ++
        [.cnot c g.cd.2.1]
    else if g.cd.1 = 2 then toffoliGates c g.cd.2.1 a ++ [.t a] ++ toffoliGates c g.cd.2.1 a
    else if g.cd.1 = 3 then [.cnot c g.cd.2.1]
    else toffoliGates c g.cd.2.1 g.cd.2.2 := by
  cases g <;> rfl

@[fun_prop] theorem PT.fp_ctrlGate {α : Type} [Rep α] {c a : α → ℕ} {g : α → Gate} (hc : PT c)
    (ha : PT a) (hg : PT g) : PT fun x => ctrlGate (c x) (a x) (g x) := by
  have : PT fun x => if (g x).cd.1 = 0 then sdgGates (g x).cd.2.1 ++ [.h (g x).cd.2.1] ++
        tdgGates (g x).cd.2.1 ++
        [.cnot (c x) (g x).cd.2.1, .t (g x).cd.2.1, .h (g x).cd.2.1, .s (g x).cd.2.1]
      else if (g x).cd.1 = 1 then [.t (c x), .t (g x).cd.2.1, .cnot (c x) (g x).cd.2.1] ++
        tdgGates (g x).cd.2.1 ++ [.cnot (c x) (g x).cd.2.1]
      else if (g x).cd.1 = 2 then toffoliGates (c x) (g x).cd.2.1 (a x) ++ [.t (a x)] ++
        toffoliGates (c x) (g x).cd.2.1 (a x)
      else if (g x).cd.1 = 3 then [.cnot (c x) (g x).cd.2.1]
      else toffoliGates (c x) (g x).cd.2.1 (g x).cd.2.2 := by fun_prop
  exact this.of_eq fun x => (ctrlGate_eq _ _ _).symm

@[fun_prop] theorem PT.fp_ctrlGates {α : Type} [Rep α] {c a : α → ℕ} {gs : α → List Gate}
    (hc : PT c) (ha : PT a) (hgs : PT gs) : PT fun x => ctrlGates (c x) (a x) (gs x) := by
  unfold ctrlGates; fun_prop

/-! ### The zero test -/

/-- The control/target/ancilla triples of the zero test. -/
def ztTriples (c : ℕ) (S anc : List ℕ) : List (ℕ × (ℕ × ℕ)) := (c :: anc).zip (S.zip anc)

/-- The closed form of `ztGates`. -/
def ztClosed (c t : ℕ) (S anc : List ℕ) : List Gate :=
  (ztTriples c S anc).flatMap (fun q => ncaGates q.1 q.2.1 q.2.2) ++
    (if S.length ≤ anc.length then [.cnot ((c :: anc).getD S.length 0) t] else []) ++
    (ztTriples c S anc).reverse.flatMap (fun q => ncaGates q.1 q.2.1 q.2.2)

theorem ztGates_eq : ∀ (c t : ℕ) (S anc : List ℕ), ztGates c t S anc = ztClosed c t S anc
  | c, t, [], anc => by simp [ztGates, ztClosed, ztTriples]
  | c, t, s :: S, [] => by simp [ztGates, ztClosed, ztTriples]
  | c, t, s :: S, a :: anc => by
    rw [ztGates, ztGates_eq a t S anc]
    simp only [ztClosed, ztTriples, List.zip_cons_cons, List.flatMap_cons, List.reverse_cons,
      List.flatMap_append, List.flatMap_nil, List.length_cons, List.getD_cons_succ,
      Nat.add_le_add_iff_right, List.append_assoc]
    simp

@[fun_prop] theorem PT.fp_ztGates {α : Type} [Rep α] {c t : α → ℕ} {S anc : α → List ℕ}
    (hc : PT c) (ht : PT t) (hS : PT S) (hanc : PT anc) :
    PT fun x => ztGates (c x) (t x) (S x) (anc x) :=
  (show PT fun x => ztClosed (c x) (t x) (S x) (anc x) by unfold ztClosed ztTriples; fun_prop).of_eq
    fun x => (ztGates_eq _ _ _ _).symm

/-! ### Segments -/

@[fun_prop] theorem PT.fp_psum {α : Type} [Rep α] {a : α → List ℕ} {i : α → ℕ} (ha : PT a)
    (hi : PT i) : PT fun x => psum (a x) (i x) := by unfold psum; fun_prop

@[fun_prop] theorem PT.fp_zw {α : Type} [Rep α] {a b : α → List ℕ} (ha : PT a) (hb : PT b) :
    PT fun x => zw (a x) (b x) := by unfold zw; fun_prop

theorem segIdx_eq : ∀ (a : List ℕ) (v : ℕ),
    segIdx a v = ((List.range a.length).filter fun i => decide (psum a (i + 1) ≤ v)).length
  | [], v => rfl
  | x :: a, v => by
    rw [segIdx]
    by_cases hv : v < x
    · rw [if_pos hv]
      symm
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro i _
      rw [decide_eq_true_iff]
      simp only [psum, List.take_succ_cons, List.sum_cons]
      omega
    · rw [if_neg hv, segIdx_eq a (v - x), List.length_cons, List.range_succ_eq_map,
        List.filter_cons]
      have h0 : psum (x :: a) (0 + 1) ≤ v := by simp [psum]; omega
      simp only [h0, decide_true, if_true, List.length_cons, List.filter_map, List.length_map]
      congr 2
      apply List.filter_congr
      intro i _
      simp only [Function.comp_apply, psum, List.take_succ_cons, List.sum_cons, Nat.succ_eq_add_one]
      apply decide_eq_decide.mpr
      omega

@[fun_prop] theorem PT.fp_segIdx {α : Type} [Rep α] {a : α → List ℕ} {v : α → ℕ} (ha : PT a)
    (hv : PT v) : PT fun x => segIdx (a x) (v x) :=
  (show PT fun x => ((List.range (a x).length).filter fun i =>
    decide (psum (a x) (i + 1) ≤ v x)).length by fun_prop).of_eq fun x => (segIdx_eq _ _).symm

end ShiQIP.Uniform
