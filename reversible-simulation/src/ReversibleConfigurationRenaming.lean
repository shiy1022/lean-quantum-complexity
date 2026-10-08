import ReversibleFormulaConfiguration
import ReversibleFormulaRenaming

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleTM
open ShiReversibleFormula ShiReversibleCoding
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.σ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _
variable {tm : Turing.FinTM2} {capacity : Nat} {ι κ : Type}

theorem FormulaCfg.fields_ext (p q : FormulaCfg tm capacity ι)
    (hl : p.label = q.label) (hm : p.memory = q.memory) (hc : p.cells = q.cells) : p = q := by
  cases p; cases q
  cases hl; cases hm; cases hc
  rfl

/-- Rename addresses without changing configuration coordinates or formula shape. -/
def FormulaCfg.rename (p : FormulaCfg tm capacity ι) (r : ι → κ) :
    FormulaCfg tm capacity κ where
  label l := (p.label l).rename r
  memory v := (p.memory v).rename r
  cells k i a := (p.cells k i a).rename r

theorem FormulaCfg.rename_headCodes (p : FormulaCfg tm capacity ι) (r : ι → κ)
    (k : tm.K) (a : Option (MachineSymbol tm)) :
    ((p.rename r).headCodes k a) = (p.headCodes k a).rename r := by
  unfold FormulaCfg.headCodes
  split <;> rfl

theorem FormulaCfg.rename_load (p : FormulaCfg tm capacity ι) (r : ι → κ)
    (f : tm.σ → tm.σ) : (p.load f).rename r = (p.rename r).load f := by
  apply FormulaCfg.fields_ext
  · rfl
  · funext v; exact rename_unaryTable _ _ _ _
  · rfl

theorem FormulaCfg.rename_peek (p : FormulaCfg tm capacity ι) (r : ι → κ)
    (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    (p.peek k f).rename r = (p.rename r).peek k f := by
  apply FormulaCfg.fields_ext
  · rfl
  · funext v
    change (binaryTable (fun s a => f s (decodeCellSymbol k a)) p.memory (p.headCodes k) v).rename r =
      binaryTable (fun s a => f s (decodeCellSymbol k a)) (p.rename r).memory ((p.rename r).headCodes k) v
    simp only [binaryTable, rename_unaryTable, Formula.rename, FormulaCfg.rename_headCodes]
    rfl
  · rfl

theorem FormulaCfg.rename_goto (p : FormulaCfg tm capacity ι) (r : ι → κ)
    (f : tm.σ → tm.Λ) : (p.goto f).rename r = (p.rename r).goto f := by
  apply FormulaCfg.fields_ext
  · funext l; exact rename_unaryTable _ _ _ _
  · rfl
  · rfl

theorem FormulaCfg.rename_halt (p : FormulaCfg tm capacity ι) (r : ι → κ) :
    p.halt.rename r = (p.rename r).halt := by rfl

theorem FormulaCfg.rename_mux (s : Formula ι) (p q : FormulaCfg tm capacity ι)
    (r : ι → κ) : (FormulaCfg.mux s p q).rename r =
      FormulaCfg.mux (s.rename r) (p.rename r) (q.rename r) := by
  rfl

theorem FormulaCfg.rename_push (p : FormulaCfg tm capacity ι) (r : ι → κ)
    (k : tm.K) (f : tm.σ → MachineSymbol tm) :
    (p.push k f).rename r = (p.rename r).push k f := by
  classical
  apply FormulaCfg.fields_ext
  · rfl
  · rfl
  · funext j i a
    by_cases hj : j = k
    · subst j
      simp only [FormulaCfg.rename, FormulaCfg.push, Function.update_self]
      split
      · exact rename_unaryTable _ _ _ _
      · rfl
    · simp [FormulaCfg.rename, FormulaCfg.push, Function.update_of_ne hj]

theorem FormulaCfg.rename_pop (p : FormulaCfg tm capacity ι) (r : ι → κ)
    (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    (p.pop k f).rename r = (p.rename r).pop k f := by
  classical
  apply FormulaCfg.fields_ext
  · rfl
  · simpa only [FormulaCfg.pop, FormulaCfg.rename, FormulaCfg.peek] using
      congrArg FormulaCfg.memory (p.rename_peek r k f)
  · funext j i a
    by_cases hj : j = k
    · subst j
      simp only [FormulaCfg.rename, FormulaCfg.pop, Function.update_self]
      split <;> rfl
    · simp [FormulaCfg.rename, FormulaCfg.pop, FormulaCfg.peek, Function.update_of_ne hj]

end ShiReversibleTM
