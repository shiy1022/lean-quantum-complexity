import «AMPUNI-stack-frame»
import «AMPUNI-subroutine-full-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMRightFrame
variable {K H L V W : Type} [DecidableEq K] [DecidableEq H]
    {G : K → Type} {E : H → Type}

def cfg (A : ∀ h, List (E h)) (w : W) (c : Cfg G L V) :
    Cfg (ShiTMStackFrame.Gam E G) L (W × V) :=
  ⟨c.l, (w,c.var), ShiTMStackFrame.extendStacks A c.stk⟩

def stmt : Stmt G L V → Stmt (ShiTMStackFrame.Gam E G) L (W × V)
  | .push k f q => .push (.inr k) (fun v => f v.2) (stmt q)
  | .peek k f q => .peek (.inr k) (fun v x => (v.1,f v.2 x)) (stmt q)
  | .pop k f q => .pop (.inr k) (fun v x => (v.1,f v.2 x)) (stmt q)
  | .load f q => .load (fun v => (v.1,f v.2)) (stmt q)
  | .branch f a b => .branch (fun v => f v.2) (stmt a) (stmt b)
  | .goto f => .goto (fun v => f v.2)
  | .halt => .halt

private theorem update_right (A : ∀ h, List (E h)) (S : ∀ k, List (G k))
    (k : K) (xs : List (G k)) :
    Function.update (ShiTMStackFrame.extendStacks A S) (.inr k) xs =
      ShiTMStackFrame.extendStacks A (Function.update S k xs) := by
  funext j
  cases j with
  | inl h => simp [ShiTMStackFrame.extendStacks]
  | inr j =>
      by_cases hj : j = k
      · subst j; simp [ShiTMStackFrame.extendStacks]
      · simp [ShiTMStackFrame.extendStacks, hj]

theorem stepAux_stmt (q : Stmt G L V) (v : V) (w : W)
    (A : ∀ h, List (E h)) (S : ∀ k, List (G k)) :
    stepAux (stmt q) (w,v) (ShiTMStackFrame.extendStacks A S) =
      cfg A w (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
      simp only [stmt, stepAux, ShiTMStackFrame.extendStacks]
      rw [update_right]
      exact ih v (Function.update S k (f v::S k))
  | peek k f q ih => exact ih (f v (S k).head?) S
  | pop k f q ih =>
      simp only [stmt, stepAux, ShiTMStackFrame.extendStacks]
      rw [update_right]
      exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => exact ih (f v) S
  | branch f a b iha ihb =>
      simp only [stmt, stepAux]
      cases f v
      · exact ihb v S
      · exact iha v S
  | goto f => rfl
  | halt => rfl

def machine (M : L → Stmt G L V) : L → Stmt (ShiTMStackFrame.Gam E G) L (W × V) :=
  fun l => stmt (M l)

theorem run_frame (M : L → Stmt G L V) (A : ∀ h, List (E h)) (w : W)
    (c : Option (Cfg G L V)) :
    ShiTMSubroutine.run (machine M) (c.map (cfg A w)) =
      (ShiTMSubroutine.run M c).map (cfg A w) := by
  cases c with
  | none => rfl
  | some c =>
      rcases c with ⟨l,v,S⟩
      cases l with
      | none => rfl
      | some l =>
          change some (stepAux (stmt (M l)) (w,v) (ShiTMStackFrame.extendStacks A S)) = _
          rw [stepAux_stmt]
          rfl

theorem run_iter_frame (M : L → Stmt G L V) (A : ∀ h, List (E h)) (w : W)
    (n : Nat) (c : Option (Cfg G L V)) :
    (ShiTMSubroutine.run (machine M))^[n] (c.map (cfg A w)) =
      ((ShiTMSubroutine.run M)^[n] c).map (cfg A w) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, run_frame]
      exact ih _

end ShiTMRightFrame
