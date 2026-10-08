import ReversibleGuardedFormula
import ReversibleNaturalTickInputs

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Fixed syntax; capacity and position are the only runtime parameters. -/
inductive TickIndexExpr where
  | position : TickIndexExpr
  | capacity : TickIndexExpr
  | literal : Nat → TickIndexExpr
  | add : TickIndexExpr → Nat → TickIndexExpr
  | sub : TickIndexExpr → Nat → TickIndexExpr

def TickIndexExpr.eval (capacity position : Nat) : TickIndexExpr → Nat
  | .position => position
  | .capacity => capacity
  | .literal n => n
  | .add p n => p.eval capacity position + n
  | .sub p n => p.eval capacity position - n

def TickIndexExpr.allowance : TickIndexExpr → Nat
  | .position | .capacity => 0
  | .literal n => n
  | .add p n => p.allowance + n
  | .sub p _ => p.allowance

theorem TickIndexExpr.eval_bound (p : TickIndexExpr) (capacity position : Nat) :
    p.eval capacity position ≤ capacity + position + p.allowance := by
  induction p with
  | position => simp [TickIndexExpr.eval, TickIndexExpr.allowance]
  | capacity => simp [TickIndexExpr.eval, TickIndexExpr.allowance]
  | literal n => simp [TickIndexExpr.eval, TickIndexExpr.allowance]
  | add p n ih => simp only [TickIndexExpr.eval, TickIndexExpr.allowance]; omega
  | sub p n ih => exact (Nat.sub_le _ _).trans ih

structure TickIndexGuard where
  left : TickIndexExpr
  right : TickIndexExpr

def TickIndexGuard.eval (capacity position : Nat) (g : TickIndexGuard) : Bool :=
  decide (g.left.eval capacity position ≤ g.right.eval capacity position)

abbrev TickSymbolicCoordinate (tm : Turing.FinTM2) :=
  (Option tm.Λ ⊕ tm.σ) ⊕ ((tm.K × TickIndexExpr) × Option (MachineSymbol tm))

def tickSymbolicCoordinateEval {tm : Turing.FinTM2} (capacity position : Nat) :
    TickSymbolicCoordinate tm → NaturalConfigurationBit tm
  | .inl z => .inl z
  | .inr ((k, p), a) => .inr ((k, p.eval capacity position), a)

abbrev TickGuardFormula (tm : Turing.FinTM2) :=
  DecisionTree TickIndexGuard (Formula (TickSymbolicCoordinate tm))

def DecisionTree.evaluate {tm : Turing.FinTM2} (p : TickGuardFormula tm)
    (capacity position : Nat) : Formula (NaturalConfigurationBit tm) :=
  (p.eval (TickIndexGuard.eval capacity position)).rename (tickSymbolicCoordinateEval capacity position)

theorem TickGuardFormula.evaluate_branch {tm : Turing.FinTM2} (g : TickIndexGuard)
    (p q : TickGuardFormula tm) (capacity position : Nat) :
    DecisionTree.evaluate (.branch g p q) capacity position =
      if g.eval capacity position then p.evaluate capacity position else q.evaluate capacity position := by
  cases h : g.eval capacity position <;> simp [DecisionTree.evaluate, DecisionTree.eval, h]

theorem TickGuardFormula.evaluate_neg {tm : Turing.FinTM2} (p : TickGuardFormula tm)
    (capacity position : Nat) :
    (p.map Formula.neg).evaluate capacity position = .neg (p.evaluate capacity position) := by
  simp only [DecisionTree.evaluate, DecisionTree.eval_map, Formula.rename]

theorem TickGuardFormula.evaluate_conj {tm : Turing.FinTM2} (p q : TickGuardFormula tm)
    (capacity position : Nat) :
    (DecisionTree.combine Formula.conj p q).evaluate capacity position =
      .conj (p.evaluate capacity position) (q.evaluate capacity position) := by
  simp only [DecisionTree.evaluate, DecisionTree.eval_combine, Formula.rename]

theorem TickGuardFormula.evaluate_unaryTable {tm : Turing.FinTM2} {α β : Type}
    [Fintype α] [DecidableEq β] (f : α → β) (inputs : α → TickGuardFormula tm) (b : β)
    (capacity position : Nat) :
    (guardedUnaryTable f inputs b).evaluate capacity position =
      unaryTable f (fun a => (inputs a).evaluate capacity position) b := by
  simp only [DecisionTree.evaluate, guardedUnaryTable_eval, rename_unaryTable]

theorem TickGuardFormula.evaluate_binaryTable {tm : Turing.FinTM2} {α β γ : Type}
    [Fintype α] [Fintype β] [DecidableEq γ] (f : α → β → γ)
    (left : α → TickGuardFormula tm) (right : β → TickGuardFormula tm) (c : γ)
    (capacity position : Nat) :
    (guardedBinaryTable f left right c).evaluate capacity position =
      binaryTable f (fun a => (left a).evaluate capacity position)
        (fun b => (right b).evaluate capacity position) c := by
  simp only [DecisionTree.evaluate, guardedBinaryTable_eval, binaryTable, rename_unaryTable,
    Formula.rename]

end ShiReversibleGenerator
