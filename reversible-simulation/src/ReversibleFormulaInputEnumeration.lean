import ReversibleFormulaRenaming

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleFormula
variable {ι κ μ : Type}

/-- Occurrences are retained, so this enumeration needs no equality test on input coordinates. -/
def Formula.inputList : Formula ι → List ι
  | .constant _ => []
  | .input i => [i]
  | .neg p => p.inputList
  | .conj p q => p.inputList ++ q.inputList

def inputLeftIndex (xs ys : List ι) (i : Fin xs.length) : Fin (xs ++ ys).length :=
  ⟨i.val, by simp only [List.length_append]; omega⟩

def inputRightIndex (xs ys : List ι) (i : Fin ys.length) : Fin (xs ++ ys).length :=
  ⟨xs.length + i.val, by simp only [List.length_append]; omega⟩

theorem inputLeftIndex_get (xs ys : List ι) (i : Fin xs.length) :
    (xs ++ ys)[(inputLeftIndex xs ys i).val] = xs[i.val] := by
  simp [inputLeftIndex, List.getElem_append, i.isLt]

theorem inputRightIndex_get (xs ys : List ι) (i : Fin ys.length) :
    (xs ++ ys)[(inputRightIndex xs ys i).val] = ys[i.val] := by
  have hi : ¬ xs.length + i.val < xs.length := by omega
  simp [inputRightIndex, List.getElem_append, hi]

/-- A fixed leaf becomes a formula over one finite slot per input occurrence. -/
def Formula.intern : (p : Formula ι) → Formula (Fin p.inputList.length)
  | .constant b => .constant b
  | .input _ => .input ⟨0, by simp [Formula.inputList]⟩
  | .neg p => .neg p.intern
  | .conj p q => .conj (p.intern.rename (inputLeftIndex p.inputList q.inputList))
      (q.intern.rename (inputRightIndex p.inputList q.inputList))

theorem Formula.rename_comp (p : Formula ι) (f : ι → κ) (g : κ → μ) :
    (p.rename f).rename g = p.rename (fun i => g (f i)) := by
  induction p <;> simp_all [Formula.rename]

theorem Formula.intern_rename (p : Formula ι) :
    p.intern.rename (fun i => p.inputList[i.val]) = p := by
  induction p with
  | constant b => rfl
  | input i => rfl
  | neg p ih => simpa only [Formula.intern, Formula.rename, Formula.inputList] using congrArg Formula.neg ih
  | conj p q ihp ihq =>
    simp only [Formula.intern, Formula.inputList, Formula.rename, Formula.rename_comp]
    have hl : (fun i => (p.inputList ++ q.inputList)[(inputLeftIndex p.inputList q.inputList i).val]) =
        (fun i : Fin p.inputList.length => p.inputList[i.val]) := by
      funext i; exact inputLeftIndex_get _ _ i
    have hr : (fun i => (p.inputList ++ q.inputList)[(inputRightIndex p.inputList q.inputList i).val]) =
        (fun i : Fin q.inputList.length => q.inputList[i.val]) := by
      funext i; exact inputRightIndex_get _ _ i
    rw [hl, hr, ihp, ihq]

theorem Formula.intern_size (p : Formula ι) : p.intern.size = p.size := by
  simpa only [Formula.rename_size] using congrArg Formula.size p.intern_rename

theorem Formula.inputList_length_le_size (p : Formula ι) : p.inputList.length ≤ p.size := by
  induction p <;> simp_all [Formula.inputList, Formula.size] <;> omega

end ShiReversibleFormula
