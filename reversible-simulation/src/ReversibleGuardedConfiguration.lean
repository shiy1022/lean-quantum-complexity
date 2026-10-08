import ReversibleTickGuardSyntax

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM ShiReversibleCoding
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.σ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance (tm : Turing.FinTM2) (k : tm.K) : DecidableEq (tm.Γ k) := Classical.decEq _

structure GuardedTickCfg (tm : Turing.FinTM2) where
  label : Option tm.Λ → TickGuardFormula tm
  memory : tm.σ → TickGuardFormula tm
  cells : tm.K → TickIndexExpr → Option (MachineSymbol tm) → TickGuardFormula tm

variable {tm : Turing.FinTM2}

def GuardedTickCfg.Agrees (p : GuardedTickCfg tm) (capacity position : Nat)
    (q : NaturalFormulaCfg tm (NaturalConfigurationBit tm)) : Prop :=
  (∀ l, (p.label l).evaluate capacity position = q.label l) ∧
  (∀ v, (p.memory v).evaluate capacity position = q.memory v) ∧
  (∀ k i a, (p.cells k i a).evaluate capacity position = q.cells k (i.eval capacity position) a)

def GuardedTickCfg.inputs (tm : Turing.FinTM2) : GuardedTickCfg tm where
  label l := .leaf (.input (.inl (.inl l)))
  memory v := .leaf (.input (.inl (.inr v)))
  cells k i a := .leaf (.input (.inr ((k, i), a)))

noncomputable def GuardedTickCfg.headCodes (p : GuardedTickCfg tm) (k : tm.K) :
    Option (MachineSymbol tm) → TickGuardFormula tm :=
  fun a => .branch ⟨.literal 1, .capacity⟩ (p.cells k (.literal 0) a)
    (.leaf (.constant (oneHot none a)))

noncomputable def GuardedTickCfg.load (p : GuardedTickCfg tm) (f : tm.σ → tm.σ) : GuardedTickCfg tm :=
  { p with memory := guardedUnaryTable f p.memory }

noncomputable def GuardedTickCfg.peek (p : GuardedTickCfg tm) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) : GuardedTickCfg tm :=
  { p with memory := guardedBinaryTable (fun v a => f v (decodeCellSymbol k a)) p.memory (p.headCodes k) }

noncomputable def GuardedTickCfg.goto (p : GuardedTickCfg tm) (f : tm.σ → tm.Λ) : GuardedTickCfg tm :=
  { p with label := guardedUnaryTable (fun v => some (f v)) p.memory }

noncomputable def GuardedTickCfg.halt (p : GuardedTickCfg tm) : GuardedTickCfg tm :=
  { p with label := fun l => .leaf (.constant (oneHot none l)) }

noncomputable def GuardedTickCfg.push (p : GuardedTickCfg tm) (k : tm.K)
    (f : tm.σ → MachineSymbol tm) : GuardedTickCfg tm :=
  { p with cells := Function.update p.cells k (fun i a =>
      .branch ⟨i, .literal 0⟩ (guardedUnaryTable (fun v => some (f v)) p.memory a)
        (p.cells k (.sub i 1) a)) }

noncomputable def GuardedTickCfg.pop (p : GuardedTickCfg tm) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) : GuardedTickCfg tm :=
  { p.peek k f with cells := Function.update p.cells k (fun i a =>
      .branch ⟨.add i 2, .capacity⟩ (p.cells k (.add i 1) a)
        (.leaf (.constant (oneHot none a)))) }

def tickGuardMux (s p q : TickGuardFormula tm) : TickGuardFormula tm :=
  s.bind (fun a => DecisionTree.combine (fun b c => a.mux b c) p q)

def GuardedTickCfg.mux (s : TickGuardFormula tm) (p q : GuardedTickCfg tm) : GuardedTickCfg tm where
  label l := tickGuardMux s (p.label l) (q.label l)
  memory v := tickGuardMux s (p.memory v) (q.memory v)
  cells k i a := tickGuardMux s (p.cells k i a) (q.cells k i a)

theorem GuardedTickCfg.inputs_agree (tm : Turing.FinTM2) (capacity position : Nat) :
    (GuardedTickCfg.inputs tm).Agrees capacity position (naturalInputFormulas tm) := by
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

theorem tickGuardMux_evaluate (s p q : TickGuardFormula tm) (capacity position : Nat) :
    (tickGuardMux s p q).evaluate capacity position =
      (s.evaluate capacity position).mux (p.evaluate capacity position) (q.evaluate capacity position) := by
  simp only [tickGuardMux, DecisionTree.evaluate, DecisionTree.eval_bind, DecisionTree.eval_combine]
  rfl

end ShiReversibleGenerator
