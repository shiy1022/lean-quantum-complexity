import «AMPUNI-subroutine-lift»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPStackEmbedding
open Turing Turing.TM2
variable {K J L V A : Type} [DecidableEq K] [DecidableEq J]

/-- Reuse a machine body on any injectively selected family of homogeneous
stacks. Finite program trees remain finite; no tape inspection is hidden here. -/
def stmt (e : K ↪ J) : Stmt (fun _ : K => A) L V → Stmt (fun _ : J => A) L V
  | .push k f q => .push (e k) f (stmt e q)
  | .peek k f q => .peek (e k) f (stmt e q)
  | .pop k f q => .pop (e k) f (stmt e q)
  | .load f q => .load f (stmt e q)
  | .branch f q r => .branch f (stmt e q) (stmt e r)
  | .goto f => .goto f
  | .halt => .halt

noncomputable def cfg (e : K ↪ J) (rest : J → List A) (c : Cfg (fun _ : K => A) L V) :
    Cfg (fun _ : J => A) L V := ⟨c.l,c.var,Function.extend e c.stk rest⟩

theorem extend_update (e : K ↪ J) (S : K → List A) (rest : J → List A)
    (k : K) (t : List A) :
    Function.update (Function.extend e S rest) (e k) t =
      Function.extend e (Function.update S k t) rest := by
  classical
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i,rfl⟩ := hj
    by_cases h : i = k
    · subst i; simp [e.injective.extend_apply]
    · have hn : e i ≠ e k := fun he => h (e.injective he)
      simp [Function.update_of_ne hn, e.injective.extend_apply, h]
  · have hn : j ≠ e k := by intro h; exact hj ⟨k,h.symm⟩
    simp [Function.update_of_ne hn, Function.extend_apply' _ _ _ hj]

theorem stepAux_stmt (e : K ↪ J) (rest : J → List A)
    (q : Stmt (fun _ : K => A) L V) (v : V) (S : K → List A) :
    stepAux (stmt e q) v (Function.extend e S rest) = cfg e rest (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
      simp only [stmt, stepAux, e.injective.extend_apply, extend_update]
      exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      simpa only [stmt, stepAux, e.injective.extend_apply] using ih (f v (S k).head?) S
  | pop k f q ih =>
      simp only [stmt, stepAux, e.injective.extend_apply, extend_update]
      exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => exact ih (f v) S
  | branch f q r ihq ihr =>
      cases h : f v <;> simp [stmt, stepAux, h, ihq, ihr]
  | goto f => rfl
  | halt => rfl

def machine (e : K ↪ J) (M : L → Stmt (fun _ : K => A) L V) :
    L → Stmt (fun _ : J => A) L V := fun l => stmt e (M l)

theorem run_frame (e : K ↪ J) (rest : J → List A)
    (M : L → Stmt (fun _ : K => A) L V) (c : Option (Cfg (fun _ : K => A) L V)) :
    ShiTMSubroutine.run (machine e M) (c.map (cfg e rest)) =
      (ShiTMSubroutine.run M c).map (cfg e rest) := by
  cases c with
  | none => rfl
  | some c =>
      rcases c with ⟨l,v,S⟩
      cases l with
      | none => rfl
      | some l =>
          change some (stepAux (stmt e (M l)) v (Function.extend e S rest)) =
            some (cfg e rest (stepAux (M l) v S))
          rw [stepAux_stmt]

theorem run_iter (e : K ↪ J) (rest : J → List A)
    (M : L → Stmt (fun _ : K => A) L V) (n : ℕ) (c : Option (Cfg (fun _ : K => A) L V)) :
    (ShiTMSubroutine.run (machine e M))^[n] (c.map (cfg e rest)) =
      ((ShiTMSubroutine.run M)^[n] c).map (cfg e rest) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, run_frame]
      exact ih (ShiTMSubroutine.run M c)

end BQPStackEmbedding
