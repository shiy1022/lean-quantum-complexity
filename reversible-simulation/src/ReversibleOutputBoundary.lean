import ReversibleBooleanFormula
import ReversibleBoundedTape

set_option autoImplicit false
namespace ShiReversibleFormula
open ShiReversibleCoding

/-- A virtual slot beyond the stack capacity is the empty marker. -/
def emptySlot {capacity : Nat} {ι : Type} (empty : Fin capacity → Formula ι) (j : Nat) : Formula ι :=
  if h : j < capacity then empty ⟨j, h⟩ else .constant true

/-- The length boundary is an occupied predecessor and an empty current cell, with endpoint conventions. -/
def lengthFlag {capacity : Nat} {ι : Type} (empty : Fin capacity → Formula ι) (ell : Nat) : Formula ι :=
  .conj (if ell = 0 then .constant true else .neg (emptySlot empty (ell - 1))) (emptySlot empty ell)

theorem emptySlot_eval {capacity : Nat} {ι α : Type}
    (empty : Fin capacity → Formula ι) (x : ι → Bool) (xs : List α) (hx : xs.length ≤ capacity)
    (h : ∀ i, (empty i).eval x = decide (xs[i.val]? = none)) (j : Nat) :
    (emptySlot empty j).eval x = decide (xs.length ≤ j) := by
  by_cases hj : j < capacity
  · simp only [emptySlot, dif_pos hj]
    rw [h]
    simp only [List.getElem?_eq_none_iff]
  · have hs : xs.length ≤ j := by omega
    simp [emptySlot, hj, Formula.eval, hs]

/-- Valid stack prefixes select exactly their actual length, including empty and full stacks. -/
theorem lengthFlag_eval {capacity : Nat} {ι α : Type}
    (empty : Fin capacity → Formula ι) (x : ι → Bool) (xs : List α) (hx : xs.length ≤ capacity)
    (h : ∀ i, (empty i).eval x = decide (xs[i.val]? = none)) (ell : Nat) :
    (lengthFlag empty ell).eval x = decide (xs.length = ell) := by
  by_cases he : ell = 0
  · subst ell
    simp only [lengthFlag, if_pos rfl, Formula.eval, Bool.true_and]
    rw [emptySlot_eval empty x xs hx h]
    simp [Formula.eval]
  · simp only [lengthFlag, if_neg he, Formula.eval]
    rw [emptySlot_eval empty x xs hx h, emptySlot_eval empty x xs hx h]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega

theorem emptySlot_size {capacity : Nat} {ι : Type} (empty : Fin capacity → Formula ι)
    (b : Nat) (hb : 1 ≤ b) (h : ∀ i, (empty i).size ≤ b) (j : Nat) : (emptySlot empty j).size ≤ b := by
  by_cases hj : j < capacity
  · simpa [emptySlot, hj] using h ⟨j, hj⟩
  · simpa [emptySlot, hj, Formula.size] using hb

theorem lengthFlag_size {capacity : Nat} {ι : Type} (empty : Fin capacity → Formula ι)
    (b : Nat) (hb : 1 ≤ b) (h : ∀ i, (empty i).size ≤ b) (ell : Nat) :
    (lengthFlag empty ell).size ≤ 2 * b + 2 := by
  have hc := emptySlot_size empty b hb h ell
  have hp := emptySlot_size empty b hb h (ell - 1)
  by_cases he : ell = 0
  · subst ell
    change 1 + (emptySlot empty 0).size + 1 ≤ 2 * b + 2
    omega
  · simp only [lengthFlag, if_neg he, Formula.size]
    omega

/-- Select an arbitrary formula value using one-hot selector formulas. -/
noncomputable def selected {α ι : Type} [Fintype α] (flags values : α → Formula ι) : Formula ι :=
  disjoin (Finset.univ.toList.map (fun a => .conj (flags a) (values a)))

theorem selected_eval {α ι : Type} [Fintype α] [DecidableEq α]
    (flags values : α → Formula ι) (x : ι → Bool) (a : α)
    (h : ∀ b, (flags b).eval x = oneHot a b) : (selected flags values).eval x = (values a).eval x := by
  rw [selected, eval_disjoin, List.any_map]
  change Finset.univ.toList.any (fun b => (flags b).eval x && (values b).eval x) = _
  simp_rw [h]
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, Finset.mem_toList, Finset.mem_univ, true_and, Formula.eval,
    Bool.and_eq_true, h, oneHot, decide_eq_true_eq]
  constructor
  · rintro ⟨b, hab, hv⟩
    subst b
    exact hv
  · intro hv
    exact ⟨a, rfl, hv⟩

theorem selected_size {α ι : Type} [Fintype α] (flags values : α → Formula ι) (b c : Nat)
    (hf : ∀ a, (flags a).size ≤ b) (hv : ∀ a, (values a).size ≤ c) :
    (selected flags values).size ≤ 1 + Fintype.card α * (b + c + 5) := by
  have hs := size_disjoin (Finset.univ.toList.map (fun a => Formula.conj (flags a) (values a)))
    (b + c + 1) (by
      intro p hp
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
      have h₁ := hf a
      have h₂ := hv a
      simp only [Formula.size]
      omega)
  simpa [selected, Nat.add_assoc] using hs

/-- Capacity-dependent enumeration uses the explicit increasing finite range, never quotient choice. -/
def selectedFin {n : Nat} {ι : Type} (flags values : Fin n → Formula ι) : Formula ι :=
  disjoin ((List.finRange n).map (fun a => .conj (flags a) (values a)))

theorem selectedFin_eval {n : Nat} {ι : Type} (flags values : Fin n → Formula ι)
    (x : ι → Bool) (a : Fin n) (h : ∀ b, (flags b).eval x = oneHot a b) :
    (selectedFin flags values).eval x = (values a).eval x := by
  rw [selectedFin, eval_disjoin, List.any_map]
  change (List.finRange n).any (fun b => (flags b).eval x && (values b).eval x) = _
  simp_rw [h]
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true, oneHot,
    decide_eq_true_eq]
  constructor
  · rintro ⟨b, hab, hv⟩
    subst b
    exact hv
  · intro hv
    exact ⟨a, rfl, hv⟩

theorem selectedFin_size {n : Nat} {ι : Type} (flags values : Fin n → Formula ι) (b c : Nat)
    (hf : ∀ a, (flags a).size ≤ b) (hv : ∀ a, (values a).size ≤ c) :
    (selectedFin flags values).size ≤ 1 + n * (b + c + 5) := by
  have hs := size_disjoin ((List.finRange n).map (fun a => Formula.conj (flags a) (values a)))
    (b + c + 1) (by
      intro p hp
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
      have h₁ := hf a
      have h₂ := hv a
      simp only [Formula.size]
      omega)
  simpa [selectedFin, Nat.add_assoc] using hs

end ShiReversibleFormula
