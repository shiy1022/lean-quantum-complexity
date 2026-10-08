import ReversibleConfigurationRenaming
import ReversibleTickFormulas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleTM
open ShiReversibleFormula
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _
variable {tm : Turing.FinTM2} {capacity : Nat} {ι κ : Type}

theorem statementFormulas_rename (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hq : pushSymbols q ⊆ machineSymbols tm) (p : FormulaCfg tm capacity ι) (r : ι → κ) :
    (statementFormulas q hq p).rename r = statementFormulas q hq (p.rename r) := by
  induction q generalizing p with
  | push k f q ih => simp only [statementFormulas, ih, FormulaCfg.rename_push]
  | peek k f q ih => simp only [statementFormulas, ih, FormulaCfg.rename_peek]
  | pop k f q ih => simp only [statementFormulas, ih, FormulaCfg.rename_pop]
  | load f q ih => simp only [statementFormulas, ih, FormulaCfg.rename_load]
  | branch f q s ihq ihs =>
    simp only [statementFormulas, FormulaCfg.rename_mux, ihq, ihs, rename_unaryTable]
    rfl
  | goto f => exact p.rename_goto r f
  | halt => exact p.rename_halt r

theorem dispatchFormulas_rename (ls : List tm.Λ) (p : FormulaCfg tm capacity ι)
    (r : ι → κ) : (dispatchFormulas ls p).rename r = dispatchFormulas ls (p.rename r) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [dispatchFormulas, FormulaCfg.rename_mux, statementFormulas_rename, ih]
    rfl

theorem tickFormulas_rename (p : FormulaCfg tm capacity ι) (r : ι → κ) :
    (tickFormulas p).rename r = tickFormulas (p.rename r) :=
  dispatchFormulas_rename _ p r

end ShiReversibleTM
