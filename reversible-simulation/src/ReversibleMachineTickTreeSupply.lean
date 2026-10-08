import ReversibleSharedGuardedEmitter

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

abbrev TickTreeKind (tm : Turing.FinTM2) := (Option tm.Λ ⊕ tm.σ) ⊕ (tm.K × Option (MachineSymbol tm))

noncomputable def tickTreeForKind (tm : Turing.FinTM2) : TickTreeKind tm → TickGuardFormula tm
  | .inl (.inl l) => (guardedTickFormulas (GuardedTickCfg.inputs tm)).label l
  | .inl (.inr v) => (guardedTickFormulas (GuardedTickCfg.inputs tm)).memory v
  | .inr (k, a) => guardedTickCell tm k a

noncomputable def machineTickTrees (tm : Turing.FinTM2) : List (TickGuardFormula tm) :=
  List.ofFn (fun j : Fin (Fintype.card (TickTreeKind tm)) =>
    tickTreeForKind tm ((Fintype.equivFin (TickTreeKind tm)).symm j))

/-- This tree only determines a finite common slot supply; its branch test is never run. -/
def guardedTreeSupply {tm : Turing.FinTM2} : List (TickGuardFormula tm) → TickGuardFormula tm
  | [] => .leaf (.constant false)
  | t :: ts => .branch ⟨.literal 0, .literal 0⟩ t (guardedTreeSupply ts)

theorem guardedTreeSupply_contains {tm : Turing.FinTM2} (ts : List (TickGuardFormula tm))
    (t : TickGuardFormula tm) (ht : t ∈ ts) (p : Formula (TickSymbolicCoordinate tm)) (hp : p ∈ t.leaves) :
    p ∈ (guardedTreeSupply ts).leaves := by
  induction ts with
  | nil => simp at ht
  | cons q ts ih =>
    rcases List.mem_cons.mp ht with h | h
    · subst t; simp [guardedTreeSupply, DecisionTree.leaves, hp]
    · have h' := ih h
      simp [guardedTreeSupply, DecisionTree.leaves, h']

noncomputable def machineTickSupply (tm : Turing.FinTM2) : TickGuardFormula tm :=
  guardedTreeSupply (machineTickTrees tm)

theorem tickTreeForKind_mem (tm : Turing.FinTM2) (kind : TickTreeKind tm) :
    tickTreeForKind tm kind ∈ machineTickTrees tm := by
  simp only [machineTickTrees, List.mem_ofFn]
  refine ⟨(Fintype.equivFin (TickTreeKind tm)) kind, ?_⟩
  simp

theorem machineTickSupply_contains (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (p : Formula (TickSymbolicCoordinate tm)) (hp : p ∈ (tickTreeForKind tm kind).leaves) :
    p ∈ (machineTickSupply tm).leaves :=
  guardedTreeSupply_contains _ _ (tickTreeForKind_mem tm kind) p hp

end ShiReversibleGenerator
