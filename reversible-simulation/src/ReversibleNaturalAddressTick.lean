import ReversibleNaturalAddressConfiguration
import ReversibleTickFormulas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleTM
open ShiReversibleFormula
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _
variable {tm : Turing.FinTM2} {ι : Type}

/-- Fixed statement recursion with natural addresses and explicit runtime boundary checks. -/
noncomputable def naturalStatementFormulas (capacity : Nat) :
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (pushSymbols q ⊆ machineSymbols tm) → NaturalFormulaCfg tm ι → NaturalFormulaCfg tm ι
  | .push k f q, hq, p => naturalStatementFormulas capacity q
      (fun _a ha => hq (Finset.mem_union_right _ ha)) (p.push k (pushedSymbol k f q hq))
  | .peek k f q, hq, p => naturalStatementFormulas capacity q hq (p.peek capacity k f)
  | .pop k f q, hq, p => naturalStatementFormulas capacity q hq (p.pop capacity k f)
  | .load f q, hq, p => naturalStatementFormulas capacity q hq (p.load f)
  | .branch f q r, hq, p => NaturalFormulaCfg.mux (unaryTable f p.memory true)
      (naturalStatementFormulas capacity q (fun _a ha => hq (Finset.mem_union_left _ ha)) p)
      (naturalStatementFormulas capacity r (fun _a ha => hq (Finset.mem_union_right _ ha)) p)
  | .goto f, _, p => p.goto f
  | .halt, _, p => p.halt

theorem naturalStatementFormulas_restrict (capacity : Nat)
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : pushSymbols q ⊆ machineSymbols tm)
    (p : NaturalFormulaCfg tm ι) :
    (naturalStatementFormulas capacity q hq p).restrict capacity =
      statementFormulas q hq (p.restrict capacity) := by
  induction q generalizing p with
  | push k f q ih =>
    simp only [naturalStatementFormulas, statementFormulas, ih, NaturalFormulaCfg.restrict_push]
  | peek k f q ih =>
    simp only [naturalStatementFormulas, statementFormulas, ih, NaturalFormulaCfg.restrict_peek]
  | pop k f q ih =>
    simp only [naturalStatementFormulas, statementFormulas, ih, NaturalFormulaCfg.restrict_pop]
  | load f q ih =>
    simp only [naturalStatementFormulas, statementFormulas, ih, NaturalFormulaCfg.restrict_load]
  | branch f q r ihq ihr =>
    simp only [naturalStatementFormulas, statementFormulas, NaturalFormulaCfg.restrict_mux, ihq, ihr]
    rfl
  | goto f => exact p.restrict_goto capacity f
  | halt => exact p.restrict_halt capacity

noncomputable def naturalDispatchFormulas (capacity : Nat) :
    List tm.Λ → NaturalFormulaCfg tm ι → NaturalFormulaCfg tm ι
  | [], p => p
  | l :: ls, p => NaturalFormulaCfg.mux (p.label (some l))
      (naturalStatementFormulas capacity (tm.m l) (machineSymbols_contains_push tm l) p)
      (naturalDispatchFormulas capacity ls p)

theorem naturalDispatchFormulas_restrict (capacity : Nat) (ls : List tm.Λ)
    (p : NaturalFormulaCfg tm ι) :
    (naturalDispatchFormulas capacity ls p).restrict capacity = dispatchFormulas ls (p.restrict capacity) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [naturalDispatchFormulas, dispatchFormulas, NaturalFormulaCfg.restrict_mux,
      naturalStatementFormulas_restrict, ih]
    rfl

noncomputable def naturalTickFormulas (capacity : Nat) (p : NaturalFormulaCfg tm ι) :
    NaturalFormulaCfg tm ι := naturalDispatchFormulas capacity Finset.univ.toList p

theorem naturalTickFormulas_restrict (capacity : Nat) (p : NaturalFormulaCfg tm ι) :
    (naturalTickFormulas capacity p).restrict capacity = tickFormulas (p.restrict capacity) :=
  naturalDispatchFormulas_restrict capacity _ p

end ShiReversibleTM
