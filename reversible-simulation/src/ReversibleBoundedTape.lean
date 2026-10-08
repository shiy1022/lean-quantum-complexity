import Mathlib.Data.List.OfFn
import Mathlib.Tactic

set_option autoImplicit false

namespace ShiReversibleCoding

variable {α : Type}

/-- Constant-capacity stack slots. `none` is the empty padding marker. -/
def tapeEncode (capacity : Nat) (xs : List α) : Fin capacity → Option α :=
  fun i => xs[i.val]?

def tapeDecode {capacity : Nat} (cells : Fin capacity → Option α) : List α :=
  (List.ofFn cells).filterMap id

theorem tapeEncode_list (capacity : Nat) (xs : List α) (h : xs.length ≤ capacity) :
    List.ofFn (tapeEncode capacity xs) =
      xs.map some ++ List.replicate (capacity - xs.length) none := by
  induction capacity generalizing xs with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    simp [tapeEncode]
  | succ capacity ih =>
    cases xs with
    | nil => simp [tapeEncode, List.ofFn_const, List.replicate_succ]
    | cons a xs =>
      have hx : xs.length ≤ capacity := by simpa using h
      change List.ofFn (fun i : Fin (capacity + 1) => (a :: xs)[i.val]?) = _
      rw [List.ofFn_succ]
      simp only [Fin.val_zero, Fin.val_succ, List.getElem?_cons_zero,
        List.getElem?_cons_succ, List.map_cons, List.cons_append, List.length_cons,
        Nat.add_sub_add_right]
      change some a :: List.ofFn (tapeEncode capacity xs) =
        some a :: (xs.map some ++ List.replicate (capacity - xs.length) none)
      exact congrArg (List.cons (some a)) (ih xs hx)

@[simp] theorem tapeDecode_encode (capacity : Nat) (xs : List α)
    (h : xs.length ≤ capacity) : tapeDecode (tapeEncode capacity xs) = xs := by
  rw [tapeDecode, tapeEncode_list capacity xs h]
  simp [List.filterMap_map, List.filterMap_replicate, Function.comp_def]

theorem tapeDecode_length {capacity : Nat} (cells : Fin capacity → Option α) :
    (tapeDecode cells).length ≤ capacity := by
  simpa [tapeDecode] using List.length_filterMap_le id (List.ofFn cells)

theorem tapeEncode_injective (capacity : Nat) (xs ys : List α)
    (hx : xs.length ≤ capacity) (hy : ys.length ≤ capacity)
    (h : tapeEncode capacity xs = tapeEncode capacity ys) : xs = ys := by
  simpa [tapeDecode_encode capacity xs hx, tapeDecode_encode capacity ys hy] using
    congrArg tapeDecode h

def tapePush {capacity : Nat} (a : α) (cells : Fin capacity → Option α) :
    Fin capacity → Option α :=
  fun i => if h : i.val = 0 then some a else cells ⟨i.val - 1, by omega⟩

def tapePop {capacity : Nat} (cells : Fin capacity → Option α) : Fin capacity → Option α :=
  fun i => if h : i.val + 1 < capacity then cells ⟨i.val + 1, h⟩ else none

theorem tapePush_encode (capacity : Nat) (a : α) (xs : List α) :
    tapePush a (tapeEncode capacity xs) = tapeEncode capacity (a :: xs) := by
  funext i
  by_cases hi : i.val = 0
  · simp [tapePush, tapeEncode, hi]
  · have hs : i.val - 1 + 1 = i.val := by omega
    simp only [tapePush, dif_neg hi, tapeEncode]
    rw [← hs]
    simp

theorem tapePop_encode (capacity : Nat) (xs : List α) (h : xs.length ≤ capacity) :
    tapePop (tapeEncode capacity xs) = tapeEncode capacity xs.tail := by
  funext i
  by_cases hi : i.val + 1 < capacity
  · simp [tapePop, tapeEncode, hi, List.getElem?_tail]
  · have hb : xs.length ≤ i.val + 1 := by omega
    simp [tapePop, tapeEncode, hi, List.getElem?_tail, List.getElem?_eq_none hb]

end ShiReversibleCoding
