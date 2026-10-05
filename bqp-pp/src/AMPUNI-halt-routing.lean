import «AMPUNI-subroutine-lift»

set_option autoImplicit false
open Turing Turing.TM2
namespace ShiTMHaltRouting
variable {K L R V : Type} {G : K → Type} [DecidableEq K]

/-- Relabel a body and route every internal halt to an explicit exit label.
This includes halts nested under branches, pushes, pops, and state updates. -/
def stmt (f : L → R) (exitLabel : R) : Stmt G L V → Stmt G R V
  | .push k g q => .push k g (stmt f exitLabel q)
  | .peek k g q => .peek k g (stmt f exitLabel q)
  | .pop k g q => .pop k g (stmt f exitLabel q)
  | .load g q => .load g (stmt f exitLabel q)
  | .branch g q r => .branch g (stmt f exitLabel q) (stmt f exitLabel r)
  | .goto g => .goto (f ∘ g)
  | .halt => .goto (fun _ => exitLabel)

def cfg (f : L → R) (exitLabel : R) (c : Cfg G L V) : Cfg G R V :=
  ⟨some (c.l.elim exitLabel f), c.var, c.stk⟩

theorem stepAux_route (f : L → R) (exitLabel : R) (q : Stmt G L V)
    (v : V) (S : ∀ k, List (G k)) :
    stepAux (stmt f exitLabel q) v S = cfg f exitLabel (stepAux q v S) := by
  induction q generalizing v S with
  | push k g q ih => exact ih _ _
  | peek k g q ih => exact ih _ _
  | pop k g q ih => exact ih _ _
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases h : g v <;> simp [stmt, stepAux, h, ihq, ihr]
  | goto g => rfl
  | halt => rfl

/-- A source body step that halts is now an active handoff, with exactly the
same state and stacks available to the cleanup controller. -/
theorem halted_step_routes (f : L → R) (exitLabel : R) (q : Stmt G L V)
    (v v' : V) (S T : ∀ k, List (G k))
    (h : stepAux q v S = ⟨none, v', T⟩) :
    stepAux (stmt f exitLabel q) v S = ⟨some exitLabel, v', T⟩ := by
  rw [stepAux_route, h]
  rfl

/-- Ordinary body transitions keep their exact state and stack effects. -/
theorem active_step_routes (f : L → R) (exitLabel : R) (q : Stmt G L V)
    (v v' : V) (S T : ∀ k, List (G k)) (l : L)
    (h : stepAux q v S = ⟨some l, v', T⟩) :
    stepAux (stmt f exitLabel q) v S = ⟨some (f l), v', T⟩ := by
  rw [stepAux_route, h]
  rfl

end ShiTMHaltRouting
