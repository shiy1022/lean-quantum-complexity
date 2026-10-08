import ReversibleOutputBoundary
import ReversibleOutput

set_option autoImplicit false
namespace ShiReversibleFormula

/-- The bit layout of the existing unary-length output serialization. -/
def outputBit (xs : List Bool) (j : Nat) : Bool :=
  if j < xs.length then true
  else if xs.length + 1 ≤ j ∧ j < 2 * xs.length + 1 then
    (xs[j - xs.length - 1]?).getD false
  else false

theorem outputCode_bit (capacity : Nat) (xs : List Bool) (j : Nat) :
    (ShiReversible.outputCode capacity xs)[j]?.getD false = outputBit xs j := by
  by_cases hp : j < xs.length
  · simp [ShiReversible.outputCode, List.append_assoc, List.getElem?_append,
      hp, outputBit]
  · have hn : xs.length ≤ j := by omega
    by_cases he : j = xs.length
    · subst j
      simp [ShiReversible.outputCode, List.append_assoc, List.getElem?_append,
        outputBit]
    · have hd : xs.length + 1 ≤ j := by omega
      have hz : j - xs.length ≠ 0 := by omega
      have hi : j - xs.length - 1 + 1 = j - xs.length := by omega
      by_cases ht : j < 2 * xs.length + 1
      · have hb : j - xs.length - 1 < xs.length := by omega
        simp [ShiReversible.outputCode, List.append_assoc, List.getElem?_append,
          List.getElem?_cons, hp, hz, hd, ht, hb, outputBit]
      · have hb : xs.length ≤ j - xs.length - 1 := by omega
        have hb' : ¬ j - xs.length - 1 < xs.length := by omega
        simp [ShiReversible.outputCode, List.append_assoc, List.getElem?_append,
          List.getElem?_cons, hp, hz, hd, ht, hb, hb', outputBit, List.getElem?_replicate]
        split <;> rfl

/-- Payload positions for one selected length; positions outside capacity are zero. -/
def outputValue {capacity : Nat} {ι : Type} (payload : Fin capacity → Formula ι)
    (ell j : Nat) : Formula ι :=
  if j < ell then .constant true
  else if h : ell + 1 ≤ j ∧ j < 2 * ell + 1 ∧ j - ell - 1 < capacity then
    payload ⟨j - ell - 1, h.2.2⟩
  else .constant false

def outputFormula {capacity : Nat} {ι : Type}
    (empty payload : Fin capacity → Formula ι) (j : Nat) : Formula ι :=
  selectedFin (fun ell : Fin (capacity + 1) => lengthFlag empty ell.val)
    (fun ell => outputValue payload ell.val j)

theorem outputFormula_eval {capacity : Nat} {ι : Type}
    (empty payload : Fin capacity → Formula ι) (x : ι → Bool) (xs : List Bool)
    (hx : xs.length ≤ capacity)
    (he : ∀ i, (empty i).eval x = decide (xs[i.val]? = none))
    (hp : ∀ i, (payload i).eval x = (xs[i.val]?).getD false) (j : Nat) :
    (outputFormula empty payload j).eval x = outputBit xs j := by
  classical
  have hl : ∀ ell : Fin (capacity + 1), (lengthFlag empty ell.val).eval x =
      ShiReversibleCoding.oneHot (⟨xs.length, by omega⟩ : Fin (capacity + 1)) ell := by
    intro ell
    rw [lengthFlag_eval empty x xs hx he]
    simp [ShiReversibleCoding.oneHot, Fin.ext_iff]
  rw [outputFormula, selectedFin_eval _ _ x _ hl]
  simp only [outputValue, outputBit]
  split
  · rfl
  · split
    · rw [hp]
      simp_all [Formula.eval]
    · rename_i h₁ h₂
      have hn : ¬ (xs.length + 1 ≤ j ∧ j < 2 * xs.length + 1) := by
        intro h
        apply h₂
        exact ⟨h.1, h.2, by omega⟩
      rw [if_neg hn]
      rfl

theorem outputValue_size {capacity : Nat} {ι : Type}
    (payload : Fin capacity → Formula ι) (b : Nat) (hb : 1 ≤ b)
    (hp : ∀ i, (payload i).size ≤ b) (ell j : Nat) :
    (outputValue payload ell j).size ≤ b := by
  unfold outputValue
  split
  · exact hb
  · split
    · exact hp _
    · exact hb

theorem outputFormula_size {capacity : Nat} {ι : Type}
    (empty payload : Fin capacity → Formula ι) (b c : Nat) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (he : ∀ i, (empty i).size ≤ b) (hp : ∀ i, (payload i).size ≤ c) (j : Nat) :
    (outputFormula empty payload j).size ≤ 1 + (capacity + 1) * (2 * b + c + 7) := by
  unfold outputFormula
  apply (selectedFin_size (fun ell : Fin (capacity + 1) => lengthFlag empty ell.val)
    (fun ell => outputValue payload ell.val j) (2 * b + 2) c
    (fun ell => lengthFlag_size empty b hb he ell.val)
    (fun ell => outputValue_size payload c hc hp ell.val j)).trans
  ring_nf <;> exact le_rfl

end ShiReversibleFormula
