import ReversibleFiniteCodec

set_option autoImplicit false

namespace ShiReversibleFormula

/-- Bounded-arity Boolean formulas used only within one fixed machine step. -/
inductive Formula (ι : Type) where
  | constant : Bool → Formula ι
  | input : ι → Formula ι
  | neg : Formula ι → Formula ι
  | conj : Formula ι → Formula ι → Formula ι

def Formula.eval {ι : Type} (x : ι → Bool) : Formula ι → Bool
  | .constant b => b
  | .input i => x i
  | .neg p => !(p.eval x)
  | .conj p q => p.eval x && q.eval x

def Formula.size {ι : Type} : Formula ι → Nat
  | .constant _ => 1
  | .input _ => 1
  | .neg p => p.size + 1
  | .conj p q => p.size + q.size + 1

def Formula.disj {ι : Type} (p q : Formula ι) : Formula ι :=
  .neg (.conj (.neg p) (.neg q))

@[simp] theorem Formula.eval_disj {ι : Type} (p q : Formula ι) (x : ι → Bool) :
    (p.disj q).eval x = (p.eval x || q.eval x) := by
  cases hp : p.eval x <;> cases hq : q.eval x <;> simp [Formula.disj, Formula.eval, hp, hq]

@[simp] theorem Formula.size_disj {ι : Type} (p q : Formula ι) :
    (p.disj q).size = p.size + q.size + 4 := by
  simp [Formula.disj, Formula.size]
  omega

def disjoin {ι : Type} (ps : List (Formula ι)) : Formula ι :=
  ps.foldr Formula.disj (.constant false)

@[simp] theorem eval_disjoin {ι : Type} (ps : List (Formula ι)) (x : ι → Bool) :
    (disjoin ps).eval x = ps.any (fun p => p.eval x) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change (p.disj (disjoin ps)).eval x = _
    rw [Formula.eval_disj, ih]
    rfl

theorem size_disjoin {ι : Type} (ps : List (Formula ι)) (bound : Nat)
    (h : ∀ p ∈ ps, p.size ≤ bound) :
    (disjoin ps).size ≤ 1 + ps.length * (bound + 4) := by
  induction ps with
  | nil => simp [disjoin, Formula.size]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht := ih (fun q hq => h q (by simp [hq]))
    simp only [disjoin, List.foldr_cons, Formula.size_disj, List.length_cons]
    change p.size + (disjoin ps).size + 4 ≤ _
    rw [Nat.succ_mul]
    omega

/-- A fixed finite function is expanded into AND/NOT formulas on one-hot control bits. -/
noncomputable def unaryTable {α β ι : Type} [Fintype α] [DecidableEq β]
    (f : α → β) (inputs : α → Formula ι) (b : β) : Formula ι :=
  disjoin (Finset.univ.toList.map (fun a =>
    .conj (.constant (decide (f a = b))) (inputs a)))

theorem eval_unaryTable {α β ι : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (inputs : α → Formula ι) (x : ι → Bool) (a : α) (b : β)
    (h : ∀ c, (inputs c).eval x = ShiReversibleCoding.oneHot a c) :
    (unaryTable f inputs b).eval x = ShiReversibleCoding.oneHot (f a) b := by
  rw [unaryTable, eval_disjoin, List.any_map]
  change Finset.univ.toList.any (fun c => decide (f c = b) && (inputs c).eval x) = _
  simp_rw [h]
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, Finset.mem_toList, Finset.mem_univ,
    true_and, ShiReversibleCoding.oneHot, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨c, hfc, hac⟩
    subst c
    exact hfc
  · intro hfb
    exact ⟨a, hfb, rfl⟩

theorem size_unaryTable {α β ι : Type} [Fintype α] [DecidableEq β]
    (f : α → β) (inputs : α → Formula ι) (b : β) (bound : Nat)
    (h : ∀ a, (inputs a).size ≤ bound) :
    (unaryTable f inputs b).size ≤ 1 + Fintype.card α * (bound + 6) := by
  unfold unaryTable
  have hs := size_disjoin (Finset.univ.toList.map (fun a =>
    Formula.conj (Formula.constant (decide (f a = b))) (inputs a))) (bound + 2) (by
      intro p hp
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
      have ha := h a
      simp only [Formula.size]
      omega)
  simpa [Nat.add_assoc] using hs

/-- Branch selection expands into bounded-arity gates on each output bit. -/
def Formula.mux {ι : Type} (selector yes no : Formula ι) : Formula ι :=
  (Formula.conj selector yes).disj (Formula.conj (.neg selector) no)

@[simp] theorem Formula.eval_mux {ι : Type} (selector yes no : Formula ι)
    (x : ι → Bool) :
    (selector.mux yes no).eval x = cond (selector.eval x) (yes.eval x) (no.eval x) := by
  cases hs : selector.eval x <;> simp [Formula.mux, Formula.eval, hs]

@[simp] theorem Formula.size_mux {ι : Type} (selector yes no : Formula ι) :
    (selector.mux yes no).size = 2 * selector.size + yes.size + no.size + 7 := by
  simp [Formula.mux, Formula.size]
  omega

noncomputable def binaryTable {α β γ ι : Type} [Fintype α] [Fintype β] [DecidableEq γ]
    (f : α → β → γ) (left : α → Formula ι) (right : β → Formula ι)
    (c : γ) : Formula ι :=
  unaryTable (fun p : α × β => f p.1 p.2)
    (fun p => .conj (left p.1) (right p.2)) c

theorem eval_binaryTable {α β γ ι : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → β → γ) (left : α → Formula ι) (right : β → Formula ι)
    (x : ι → Bool) (a : α) (b : β) (c : γ)
    (hl : ∀ d, (left d).eval x = ShiReversibleCoding.oneHot a d)
    (hr : ∀ d, (right d).eval x = ShiReversibleCoding.oneHot b d) :
    (binaryTable f left right c).eval x = ShiReversibleCoding.oneHot (f a b) c := by
  apply eval_unaryTable _ _ x (a, b) c
  rintro ⟨d, e⟩
  simp [Formula.eval, hl, hr, ShiReversibleCoding.oneHot, Bool.decide_and]

theorem size_binaryTable {α β γ ι : Type} [Fintype α] [Fintype β] [DecidableEq γ]
    (f : α → β → γ) (left : α → Formula ι) (right : β → Formula ι)
    (c : γ) (lb rb : Nat) (hl : ∀ a, (left a).size ≤ lb)
    (hr : ∀ b, (right b).size ≤ rb) :
    (binaryTable f left right c).size ≤ 1 +
      Fintype.card α * Fintype.card β * (lb + rb + 7) := by
  have hs := size_unaryTable (fun p : α × β => f p.1 p.2)
    (fun p => Formula.conj (left p.1) (right p.2)) c (lb + rb + 1) (by
      intro p
      have h₁ := hl p.1
      have h₂ := hr p.2
      simp only [Formula.size]
      omega)
  simpa [binaryTable, Nat.add_assoc] using hs

end ShiReversibleFormula
