import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

set_option autoImplicit false

namespace ShiReversibleCoding

variable {α : Type} [Fintype α] [DecidableEq α]

/-- One indicator bit for each value in a fixed finite alphabet. -/
def oneHot (a : α) : α → Bool := fun b => decide (a = b)

noncomputable def oneHotDecode (bits : α → Bool) : Option α := Finset.univ.toList.find? bits

theorem oneHot_injective : Function.Injective (oneHot (α := α)) := by
  intro a b h
  have he := congrFun h a
  simpa [oneHot, eq_comm] using he

private theorem findUnique (ls : List α) (a : α) (h : a ∈ ls) :
    ls.find? (oneHot a) = some a := by
  induction ls with
  | nil => simp at h
  | cons b ls ih =>
    by_cases hb : a = b
    · subst b; simp [oneHot]
    · have ha : a ∈ ls := by simpa [hb] using h
      simpa [oneHot, hb] using ih ha

@[simp] theorem oneHotDecode_encode (a : α) : oneHotDecode (oneHot a) = some a := by
  apply findUnique
  simp

noncomputable def oneHotBits (a : α) : Fin (Fintype.card α) → Bool :=
  fun i => oneHot a ((Fintype.equivFin α).symm i)

noncomputable def oneHotBitsDecode (bits : Fin (Fintype.card α) → Bool) : Option α :=
  oneHotDecode (fun a => bits (Fintype.equivFin α a))

@[simp] theorem oneHotBitsDecode_encode (a : α) :
    oneHotBitsDecode (oneHotBits a) = some a := by
  simpa [oneHotBitsDecode, oneHotBits] using oneHotDecode_encode a

noncomputable def oneHotList (a : α) : List Bool := List.ofFn (oneHotBits a)

@[simp] theorem oneHotList_length (a : α) : (oneHotList a).length = Fintype.card α := by
  simp [oneHotList]

noncomputable def oneHotListDecode (bits : List Bool) : Option α :=
  if h : bits.length = Fintype.card α then
    oneHotBitsDecode (fun i => bits.get ⟨i.val, by omega⟩)
  else none

@[simp] theorem oneHotListDecode_encode (a : α) : oneHotListDecode (oneHotList a) = some a := by
  unfold oneHotListDecode
  rw [dif_pos (oneHotList_length a)]
  simp only [oneHotList, List.get_eq_getElem,
    List.getElem_ofFn]
  exact oneHotBitsDecode_encode a

theorem oneHotList_injective : Function.Injective (oneHotList (α := α)) := by
  intro a b h
  have he := congrArg (oneHotListDecode (α := α)) h
  simpa using he

end ShiReversibleCoding
