import «AMPUNI-subroutine-lift»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPUnaryParser
open Turing Turing.TM2
abbrev K := Fin 2
abbrev Gam : K → Type := fun _ => Bool

def program (_ : Unit) : Stmt Gam Unit Bool :=
  .pop 0 (fun _ a => a.getD false) (.branch id
    (.push 1 (fun _ => true) (.goto (fun _ => ())))
    (.load (fun _ => false) .halt))

def tapes (s a : List Bool) : ∀ k : K, List (Gam k) :=
  fun k => if k = 0 then s else a

def cfg (v : Bool) (s a : List Bool) : Cfg Gam Unit Bool := ⟨some (),v,tapes s a⟩

@[simp] theorem tape0 (s a : List Bool) : tapes s a 0 = s := rfl
@[simp] theorem tape1 (s a : List Bool) : tapes s a 1 = a := rfl
@[simp] theorem update0 (s a t : List Bool) :
    Function.update (tapes s a) 0 t = tapes t a := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update1 (s a t : List Bool) :
    Function.update (tapes s a) 1 t = tapes s t := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem mark_step (v : Bool) (s a : List Bool) :
    ShiTMSubroutine.run program (some (cfg v (true::s) a)) =
    some (cfg true s (true::a)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem end_step (v : Bool) (s a : List Bool) :
    ShiTMSubroutine.run program (some (cfg v (false::s) a)) =
    some (⟨none,false,tapes s a⟩ : Cfg Gam Unit Bool) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

private theorem replicate_append_cons (n : ℕ) (bs : List Bool) :
    List.replicate n true ++ true :: bs = true :: (List.replicate n true ++ bs) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons true) ih

/-- Consume exactly one terminated unary field, preserving the entire following
input and any earlier counter contents, in n+1 concrete transitions. -/
theorem parse_run (n : ℕ) (v : Bool) (s a : List Bool) :
    (ShiTMSubroutine.run program)^[n+1]
      (some (cfg v (List.replicate n true ++ false::s) a)) =
    some (⟨none,false,tapes s (List.replicate n true ++ a)⟩ : Cfg Gam Unit Bool) := by
  induction n generalizing v a with
  | zero => exact end_step v s a
  | succ n ih =>
      change (ShiTMSubroutine.run program)^[n+1+1] _ = _
      simp only [List.replicate_succ, List.cons_append, Function.iterate_succ_apply, mark_step]
      simpa only [Function.iterate_succ_apply, replicate_append_cons] using ih true (true::a)

end BQPUnaryParser
