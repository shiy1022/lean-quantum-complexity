import ReversibleGuardedPrimitiveAgreement
import ReversibleNaturalTickCompilation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _
variable {tm : Turing.FinTM2}

/-- The finite syntax tree has no runtime capacity or cell-position argument. -/
noncomputable def guardedStatementFormulas :
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (pushSymbols q ⊆ machineSymbols tm) → GuardedTickCfg tm → GuardedTickCfg tm
  | .push k f q, hq, p => guardedStatementFormulas q
      (fun _a ha => hq (Finset.mem_union_right _ ha)) (p.push k (pushedSymbol k f q hq))
  | .peek k f q, hq, p => guardedStatementFormulas q hq (p.peek k f)
  | .pop k f q, hq, p => guardedStatementFormulas q hq (p.pop k f)
  | .load f q, hq, p => guardedStatementFormulas q hq (p.load f)
  | .branch f q r, hq, p => GuardedTickCfg.mux (guardedUnaryTable f p.memory true)
      (guardedStatementFormulas q (fun _a ha => hq (Finset.mem_union_left _ ha)) p)
      (guardedStatementFormulas r (fun _a ha => hq (Finset.mem_union_right _ ha)) p)
  | .goto f, _, p => p.goto f
  | .halt, _, p => p.halt

theorem guardedStatementFormulas_agree (capacity position : Nat)
    (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : pushSymbols q ⊆ machineSymbols tm)
    (p : GuardedTickCfg tm) (n : NaturalFormulaCfg tm (NaturalConfigurationBit tm))
    (h : p.Agrees capacity position n) :
    (guardedStatementFormulas q hq p).Agrees capacity position (naturalStatementFormulas capacity q hq n) := by
  induction q generalizing p n with
  | push k f q ih => exact ih _ _ _ (h.push k (pushedSymbol k f q hq))
  | peek k f q ih => exact ih _ _ _ (h.peek k f)
  | pop k f q ih => exact ih _ _ _ (h.pop k f)
  | load f q ih => exact ih _ _ _ (h.load f)
  | branch f q r ihq ihr =>
    have hy := ihq (fun _a ha => hq (Finset.mem_union_left _ ha)) p n h
    have hn := ihr (fun _a ha => hq (Finset.mem_union_right _ ha)) p n h
    simpa only [guardedStatementFormulas, naturalStatementFormulas,
      TickGuardFormula.evaluate_unaryTable, h.2.1] using hy.mux hn (guardedUnaryTable f p.memory true)
  | goto f => exact h.goto f
  | halt => exact h.halt

noncomputable def guardedDispatchFormulas : List tm.Λ → GuardedTickCfg tm → GuardedTickCfg tm
  | [], p => p
  | l :: ls, p => GuardedTickCfg.mux (p.label (some l))
      (guardedStatementFormulas (tm.m l) (machineSymbols_contains_push tm l) p)
      (guardedDispatchFormulas ls p)

theorem guardedDispatchFormulas_agree (capacity position : Nat) (ls : List tm.Λ)
    (p : GuardedTickCfg tm) (n : NaturalFormulaCfg tm (NaturalConfigurationBit tm))
    (h : p.Agrees capacity position n) :
    (guardedDispatchFormulas ls p).Agrees capacity position (naturalDispatchFormulas capacity ls n) := by
  induction ls with
  | nil => exact h
  | cons l ls ih =>
    simpa only [guardedDispatchFormulas, naturalDispatchFormulas, h.1] using
      (guardedStatementFormulas_agree capacity position _ _ p n h).mux ih (p.label (some l))

noncomputable def guardedTickFormulas (p : GuardedTickCfg tm) : GuardedTickCfg tm :=
  guardedDispatchFormulas Finset.univ.toList p

theorem guardedTickFormulas_agree (capacity position : Nat) (p : GuardedTickCfg tm)
    (n : NaturalFormulaCfg tm (NaturalConfigurationBit tm)) (h : p.Agrees capacity position n) :
    (guardedTickFormulas p).Agrees capacity position (naturalTickFormulas capacity n) :=
  guardedDispatchFormulas_agree capacity position _ p n h

theorem guardedTickFormulas_inputs_agree (tm : Turing.FinTM2) (capacity position : Nat) :
    (guardedTickFormulas (GuardedTickCfg.inputs tm)).Agrees capacity position
      (naturalTickFormulas capacity (naturalInputFormulas tm)) :=
  guardedTickFormulas_agree capacity position _ _ (GuardedTickCfg.inputs_agree tm capacity position)

noncomputable def guardedTickCell (tm : Turing.FinTM2) (k : tm.K)
    (a : Option (MachineSymbol tm)) : TickGuardFormula tm :=
  (guardedTickFormulas (GuardedTickCfg.inputs tm)).cells k .position a

/-- A fixed finite guard tree reproduces the actual bounded tick's cell assignments. -/
theorem guardedTickCell_rawCompile (tm : Turing.FinTM2) (capacity base : Nat)
    (k : tm.K) (i : Fin capacity) (a : Option (MachineSymbol tm)) :
    ((guardedTickCell tm k a).evaluate capacity i.val).rawCompile (naturalConfigurationAddress tm capacity) base =
      ((tickFormulas (FormulaCfg.inputs tm capacity)).cells k i a).rawCompile Fin.val base := by
  have hg := (guardedTickFormulas_inputs_agree tm capacity i.val).2.2 k .position a
  have hx := congrArg (fun p => p.cells k i a) (naturalTickFormulas_inputs tm capacity)
  have he : (guardedTickCell tm k a).evaluate capacity i.val =
      ((tickFormulas (FormulaCfg.inputs tm capacity)).cells k i a).rename (naturalInputAddress tm capacity) :=
    hg.trans hx
  rw [he, Formula.rename_rawCompile]
  have haddr : (fun j => naturalConfigurationAddress tm capacity (naturalInputAddress tm capacity j)) =
      (Fin.val : Fin (configurationWidth tm capacity) → Nat) := by
    funext j; exact naturalInputAddress_value tm capacity j
  rw [haddr]

/-- The selected formula belongs to one fixed finite leaf list for this machine/stack/symbol. -/
theorem guardedTickCell_fixed_leaf (tm : Turing.FinTM2) (capacity base : Nat)
    (k : tm.K) (i : Fin capacity) (a : Option (MachineSymbol tm)) :
    ∃ leaf ∈ (guardedTickCell tm k a).leaves,
      (leaf.rename (tickSymbolicCoordinateEval capacity i.val)).rawCompile
        (naturalConfigurationAddress tm capacity) base =
      ((tickFormulas (FormulaCfg.inputs tm capacity)).cells k i a).rawCompile Fin.val base := by
  exact ⟨(guardedTickCell tm k a).eval (TickIndexGuard.eval capacity i.val),
    DecisionTree.eval_mem_leaves _ _, guardedTickCell_rawCompile tm capacity base k i a⟩

end ShiReversibleGenerator
