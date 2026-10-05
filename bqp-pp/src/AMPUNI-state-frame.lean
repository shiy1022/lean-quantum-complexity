import «AMPUNI-subroutine-full-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMStateFrame
variable {K L V W : Type} [DecidableEq K] {G : K → Type}

/-- Add finite auxiliary state without changing a source computation. -/
def stmt : Stmt G L V → Stmt G L (V × W)
  | .push k f q => .push k (fun v => f v.1) (stmt q)
  | .peek k f q => .peek k (fun v x => (f v.1 x, v.2)) (stmt q)
  | .pop k f q => .pop k (fun v x => (f v.1 x, v.2)) (stmt q)
  | .load f q => .load (fun v => (f v.1, v.2)) (stmt q)
  | .branch f a b => .branch (fun v => f v.1) (stmt a) (stmt b)
  | .goto f => .goto (fun v => f v.1)
  | .halt => .halt

def cfg (w : W) (c : Cfg G L V) : Cfg G L (V × W) :=
  ⟨c.l, (c.var, w), c.stk⟩

theorem stepAux_stmt (q : Stmt G L V) (v : V) (w : W) (S : ∀ k, List (G k)) :
    stepAux (stmt q) (v, w) S = cfg w (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => exact ih v (Function.update S k (f v::S k))
  | peek k f q ih => exact ih (f v (S k).head?) S
  | pop k f q ih => exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => exact ih (f v) S
  | branch f a b iha ihb =>
      simp only [stmt, stepAux]
      cases f v
      · exact ihb v S
      · exact iha v S
  | goto f => rfl
  | halt => rfl

def machine (M : L → Stmt G L V) : L → Stmt G L (V × W) := fun l => stmt (M l)

theorem run_frame (M : L → Stmt G L V) (w : W) (c : Option (Cfg G L V)) :
    ShiTMSubroutine.run (machine M) (c.map (cfg w)) =
      (ShiTMSubroutine.run M c).map (cfg w) := by
  cases c with
  | none => rfl
  | some c =>
      rcases c with ⟨l, v, S⟩
      cases l with
      | none => rfl
      | some l =>
          change some (stepAux (stmt (M l)) (v, w) S) = some (cfg w (stepAux (M l) v S))
          rw [stepAux_stmt]

theorem run_iter_frame (M : L → Stmt G L V) (w : W) (n : Nat)
    (c : Option (Cfg G L V)) :
    (ShiTMSubroutine.run (machine M))^[n] (c.map (cfg w)) =
      ((ShiTMSubroutine.run M)^[n] c).map (cfg w) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, run_frame]
      exact ih _

end ShiTMStateFrame
