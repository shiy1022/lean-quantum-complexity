import ReversibleFiniteCodec

set_option autoImplicit false

namespace ShiReversibleCoding

theorem fixedBlock_extract {α β : Type} (f : α → List β) (width : Nat)
    (hw : ∀ a, (f a).length = width) (xs : List α) (i : Nat) (hi : i < xs.length) :
    ((xs.flatMap f).drop (i * width)).take width = f xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, Nat.zero_mul, List.drop_zero, List.getElem_cons_zero]
      rw [← hw a]
      exact List.take_append_length
    | succ i =>
      have hit : i < xs.length := by simpa using hi
      have he : (i + 1) * width = (f a).length + i * width := by
        rw [hw a, Nat.add_mul]
        omega
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [he, List.drop_length_add_append]
      exact ih i hit

theorem fixedBlock_ofFn {α β : Type} {n : Nat} (f : α → List β) (width : Nat)
    (hw : ∀ a, (f a).length = width) (xs : Fin n → α) (i : Fin n) :
    (((List.ofFn xs).flatMap f).drop (i.val * width)).take width = f (xs i) := by
  simpa using fixedBlock_extract f width hw (List.ofFn xs) i.val (by simp)

theorem oneHotBlock_decode {α : Type} [Fintype α] [DecidableEq α] {n : Nat}
    (xs : Fin n → α) (i : Fin n) :
    oneHotListDecode ((((List.ofFn xs).flatMap oneHotList).drop
      (i.val * Fintype.card α)).take (Fintype.card α)) = some (xs i) := by
  rw [fixedBlock_ofFn oneHotList _ oneHotList_length]
  exact oneHotListDecode_encode _

end ShiReversibleCoding
