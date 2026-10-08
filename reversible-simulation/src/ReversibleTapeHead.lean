import ReversibleBoundedTape

set_option autoImplicit false

namespace ShiReversibleCoding

variable {α : Type}

def tapeHead {capacity : Nat} (cells : Fin capacity → Option α) : Option α :=
  if h : 0 < capacity then cells ⟨0, h⟩ else none

@[simp] theorem tapeHead_encode (capacity : Nat) (xs : List α)
    (h : xs.length ≤ capacity) : tapeHead (tapeEncode capacity xs) = xs.head? := by
  by_cases hc : 0 < capacity
  · simp [tapeHead, tapeEncode, hc, List.head?_eq_getElem?]
  · have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    simp [tapeHead, hc]

/-- The popped stack remains representable even when it was empty. -/
theorem tapePop_decode (capacity : Nat) (xs : List α) (h : xs.length ≤ capacity) :
    tapeDecode (tapePop (tapeEncode capacity xs)) = xs.tail := by
  rw [tapePop_encode capacity xs h, tapeDecode_encode]
  simp only [List.length_tail]
  omega

/-- A push is decoded exactly when its new cell fits; overflow is explicitly excluded. -/
theorem tapePush_decode (capacity : Nat) (a : α) (xs : List α)
    (h : xs.length < capacity) :
    tapeDecode (tapePush a (tapeEncode capacity xs)) = a :: xs := by
  rw [tapePush_encode, tapeDecode_encode]
  simp only [List.length_cons]
  omega

end ShiReversibleCoding
