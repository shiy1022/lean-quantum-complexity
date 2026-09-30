import «AMPUNI-subroutine-full-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2
namespace ShiTMStateReindex

variable {K L V V' : Type} [DecidableEq K] {G : K → Type}

/-- Change only the finite-state representation of a TM2 statement. -/
def stmt (e : V ≃ V') : Stmt G L V → Stmt G L V'
  | .push k f q =>
      .push k (fun v => f (e.symm v)) (stmt e q)
  | .peek k f q =>
      .peek k (fun v x => e (f (e.symm v) x)) (stmt e q)
  | .pop k f q =>
      .pop k (fun v x => e (f (e.symm v) x)) (stmt e q)
  | .load f q =>
      .load (fun v => e (f (e.symm v))) (stmt e q)
  | .branch f a b =>
      .branch (fun v => f (e.symm v)) (stmt e a) (stmt e b)
  | .goto f => .goto (fun v => f (e.symm v))
  | .halt => .halt

def cfg (e : V ≃ V') (c : Cfg G L V) : Cfg G L V' :=
  ⟨c.l, e c.var, c.stk⟩

theorem stepAux_stmt (e : V ≃ V') (q : Stmt G L V)
    (v : V) (S : ∀ k, List (G k)) :
    stepAux (stmt e q) (e v) S =
      cfg e (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
      simpa only [stmt, stepAux, e.symm_apply_apply] using
        ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      simpa only [stmt, stepAux, e.symm_apply_apply] using
        ih (f v (S k).head?) S
  | pop k f q ih =>
      simpa only [stmt, stepAux, e.symm_apply_apply] using
        ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih =>
      simpa only [stmt, stepAux, e.symm_apply_apply] using
        ih (f v) S
  | branch f a b iha ihb =>
      simp only [stmt, stepAux, e.symm_apply_apply]
      cases f v
      · exact ihb v S
      · exact iha v S
  | goto f => simp [stmt, stepAux, cfg]
  | halt => rfl

def machine (e : V ≃ V') (M : L → Stmt G L V) :
    L → Stmt G L V' :=
  fun l => stmt e (M l)

theorem run_frame (e : V ≃ V') (M : L → Stmt G L V)
    (c : Option (Cfg G L V)) :
    ShiTMSubroutine.run (machine e M) (c.map (cfg e)) =
      (ShiTMSubroutine.run M c).map (cfg e) := by
  cases c with
  | none => rfl
  | some c =>
      rcases c with ⟨l, v, S⟩
      cases l with
      | none => rfl
      | some l =>
          change some (stepAux (stmt e (M l)) (e v) S) = _
          rw [stepAux_stmt]
          rfl

theorem run_iter_frame (e : V ≃ V') (M : L → Stmt G L V)
    (n : Nat) (c : Option (Cfg G L V)) :
    (ShiTMSubroutine.run (machine e M))^[n]
      (c.map (cfg e)) =
    ((ShiTMSubroutine.run M)^[n] c).map (cfg e) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,
        Function.iterate_succ_apply, run_frame]
      exact ih _

end ShiTMStateReindex
