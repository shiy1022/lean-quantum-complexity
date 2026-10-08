import ReversibleTickGuardSyntax
import ReversibleIndexUpdateSequence

set_option autoImplicit false
namespace ShiReversibleGenerator

inductive TickIndexSeed where
  | position : TickIndexSeed
  | capacity : TickIndexSeed
  | literal : Nat → TickIndexSeed

def TickIndexSeed.eval (capacity position : Nat) : TickIndexSeed → Nat
  | .position => position
  | .capacity => capacity
  | .literal n => n

def TickIndexExpr.seed : TickIndexExpr → TickIndexSeed
  | .position => .position
  | .capacity => .capacity
  | .literal n => .literal n
  | .add p _ | .sub p _ => p.seed

def TickIndexExpr.updates : TickIndexExpr → List IndexUpdate
  | .position | .capacity | .literal _ => []
  | .add p n => p.updates ++ [.add n]
  | .sub p n => p.updates ++ [.sub n]

theorem TickIndexExpr.recipe_eval (p : TickIndexExpr) (capacity position : Nat) :
    indexUpdateValue p.updates (p.seed.eval capacity position) = p.eval capacity position := by
  induction p with
  | position => rfl
  | capacity => rfl
  | literal n => rfl
  | add p n ih =>
    simp only [TickIndexExpr.updates, TickIndexExpr.seed, indexUpdateValue_append, ih,
      indexUpdateValue, IndexUpdate.apply, TickIndexExpr.eval]
  | sub p n ih =>
    simp only [TickIndexExpr.updates, TickIndexExpr.seed, indexUpdateValue_append, ih,
      indexUpdateValue, IndexUpdate.apply, TickIndexExpr.eval]

variable {R : Type}

def TickIndexSeed.source (capacity position : R) : TickIndexSeed → R
  | .capacity => capacity
  | .position | .literal _ => position

def TickIndexSeed.coefficient : TickIndexSeed → Nat
  | .position | .capacity => 1
  | .literal _ => 0

def TickIndexSeed.offset : TickIndexSeed → Nat
  | .position | .capacity => 0
  | .literal n => n

theorem TickIndexSeed.affine_eval (s : TickIndexSeed) (capacity position : R) (cs : R → Nat) :
    s.coefficient * cs (s.source capacity position) + s.offset = s.eval (cs capacity) (cs position) := by
  cases s <;> simp [TickIndexSeed.coefficient, TickIndexSeed.source, TickIndexSeed.offset, TickIndexSeed.eval]

theorem TickIndexSeed.source_bound (s : TickIndexSeed) (capacity position : R) (cs : R → Nat) :
    cs (s.source capacity position) ≤ cs capacity + cs position := by
  cases s <;> simp [TickIndexSeed.source]

end ShiReversibleGenerator
