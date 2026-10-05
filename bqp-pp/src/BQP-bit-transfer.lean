import «AMPUNI-subroutine-lift»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPBitTransfer
open Turing Turing.TM2
abbrev K := Fin 2
abbrev Gam : K → Type := fun _ => Bool

def program (_ : Unit) : Stmt Gam Unit (Option Bool) :=
  .pop 0 (fun _ a => a) (.branch Option.isSome
    (.push 1 (fun a => a.getD false) (.goto (fun _ => ())))
    (.load (fun _ => none) .halt))

def tapes (s out : List Bool) : K → List Bool := fun k => if k = 0 then s else out

def cfg (v : Option Bool) (s out : List Bool) : Cfg Gam Unit (Option Bool) :=
  ⟨some (),v,tapes s out⟩

@[simp] theorem tape0 (s out : List Bool) : tapes s out 0 = s := rfl
@[simp] theorem tape1 (s out : List Bool) : tapes s out 1 = out := rfl
@[simp] theorem update0 (s out t : List Bool) :
    Function.update (tapes s out) 0 t = tapes t out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update1 (s out t : List Bool) :
    Function.update (tapes s out) 1 t = tapes s t := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem cons_step (v : Option Bool) (b : Bool) (s out : List Bool) :
    ShiTMSubroutine.run program (some (cfg v (b::s) out)) = some (cfg (some b) s (b::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem nil_step (v : Option Bool) (out : List Bool) :
    ShiTMSubroutine.run program (some (cfg v [] out)) =
    some (⟨none,none,tapes [] out⟩ : Cfg Gam Unit (Option Bool)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

/-- Drain a bit stack onto another in exactly its length plus one transitions.
This is the reversal primitive for the adjoint-program archive. -/
theorem transfer_run (s out : List Bool) (v : Option Bool) :
    (ShiTMSubroutine.run program)^[s.length+1] (some (cfg v s out)) =
    some (⟨none,none,tapes [] (s.reverse ++ out)⟩ : Cfg Gam Unit (Option Bool)) := by
  induction s generalizing v out with
  | nil => exact nil_step v out
  | cons b s ih =>
      change (ShiTMSubroutine.run program)^[s.length+1+1] _ = _
      rw [Function.iterate_succ_apply, cons_step]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (out := b::out) (v := some b)

end BQPBitTransfer
