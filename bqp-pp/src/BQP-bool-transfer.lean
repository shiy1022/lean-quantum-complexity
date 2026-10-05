import «AMPUNI-subroutine-lift»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPBoolTransfer
open Turing Turing.TM2
abbrev K := Fin 2
abbrev Gam : K → Type := fun _ => Bool

def program (_ : Unit) : Stmt Gam Unit Bool :=
  .peek 0 (fun _ a => a.isSome) (.branch id
    (.pop 0 (fun _ a => a.getD false)
      (.push 1 id (.goto (fun _ => ()))))
    (.load (fun _ => false) .halt))

def tapes (s out : List Bool) : K → List Bool := fun k => if k = 0 then s else out

def cfg (v : Bool) (s out : List Bool) : Cfg Gam Unit Bool :=
  ⟨some (),v,tapes s out⟩

@[simp] theorem tape0 (s out : List Bool) : tapes s out 0 = s := rfl
@[simp] theorem tape1 (s out : List Bool) : tapes s out 1 = out := rfl
@[simp] theorem update0 (s out t : List Bool) :
    Function.update (tapes s out) 0 t = tapes t out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update1 (s out t : List Bool) :
    Function.update (tapes s out) 1 t = tapes s t := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem cons_step (v : Bool) (b : Bool) (s out : List Bool) :
    ShiTMSubroutine.run program (some (cfg v (b::s) out)) = some (cfg b s (b::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem nil_step (v : Bool) (out : List Bool) :
    ShiTMSubroutine.run program (some (cfg v [] out)) =
    some (⟨none,false,tapes [] out⟩ : Cfg Gam Unit Bool) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

/-- Drain a bit stack onto another in exactly its length plus one transitions.
This is the reversal primitive for the adjoint-program archive. -/
theorem transfer_run (s out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run program)^[s.length+1] (some (cfg v s out)) =
    some (⟨none,false,tapes [] (s.reverse ++ out)⟩ : Cfg Gam Unit Bool) := by
  induction s generalizing v out with
  | nil => exact nil_step v out
  | cons b s ih =>
      change (ShiTMSubroutine.run program)^[s.length+1+1] _ = _
      rw [Function.iterate_succ_apply, cons_step]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (out := b::out) (v := b)

end BQPBoolTransfer
