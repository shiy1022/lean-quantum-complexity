import «AMPUNI-subroutine-lift»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPCopyBits
open Turing Turing.TM2
abbrev K := Fin 4
abbrev Label := Fin 3
abbrev Gam : K → Type := fun _ => Bool

def program : Label → Stmt Gam Label Bool
  | 0 => .peek 0 (fun _ a => a.isSome) (.branch id
      (.pop 0 (fun _ a => a.getD false) (.push 1 id (.push 2 id (.goto (fun _ => 0)))))
      (.load (fun _ => false) (.goto (fun _ => 1))))
  | 1 => .peek 1 (fun _ a => a.isSome) (.branch id
      (.pop 1 (fun _ a => a.getD false) (.push 0 id (.goto (fun _ => 1))))
      (.load (fun _ => false) (.goto (fun _ => 2))))
  | _ => .peek 2 (fun _ a => a.isSome) (.branch id
      (.pop 2 (fun _ a => a.getD false) (.push 3 id (.goto (fun _ => 2))))
      (.load (fun _ => false) .halt))

def tapes (s a b out : List Bool) : K → List Bool :=
  fun k => if k = 0 then s else if k = 1 then a else if k = 2 then b else out
def cfg (l : Label) (v : Bool) (s a b out : List Bool) : Cfg Gam Label Bool :=
  ⟨some l,v,tapes s a b out⟩

@[simp] theorem tape0 (s a b out : List Bool) : tapes s a b out 0 = s := rfl
@[simp] theorem tape1 (s a b out : List Bool) : tapes s a b out 1 = a := rfl
@[simp] theorem tape2 (s a b out : List Bool) : tapes s a b out 2 = b := rfl
@[simp] theorem tape3 (s a b out : List Bool) : tapes s a b out 3 = out := rfl
@[simp] theorem update0 (s a b out t : List Bool) : Function.update (tapes s a b out) 0 t = tapes t a b out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update1 (s a b out t : List Bool) : Function.update (tapes s a b out) 1 t = tapes s t b out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update2 (s a b out t : List Bool) : Function.update (tapes s a b out) 2 t = tapes s a t out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update3 (s a b out t : List Bool) : Function.update (tapes s a b out) 3 t = tapes s a b t := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem copy_cons (v d : Bool) (s a b out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 0 v (d::s) a b out)) = some (cfg 0 d s (d::a) (d::b) out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem copy_nil (v : Bool) (a b out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 0 v [] a b out)) = some (cfg 1 false [] a b out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem restore_cons (v d : Bool) (s a b out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 1 v s (d::a) b out)) = some (cfg 1 d (d::s) a b out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem restore_nil (v : Bool) (s b out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 1 v s [] b out)) = some (cfg 2 false s [] b out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem output_cons (v d : Bool) (s a b out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 2 v s a (d::b) out)) = some (cfg 2 d s a b (d::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem output_nil (v : Bool) (s a out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 2 v s a [] out)) =
    some (⟨none,false,tapes s a [] out⟩ : Cfg Gam Label Bool) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem copy_run (s a b out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run program)^[s.length+1] (some (cfg 0 v s a b out)) =
    some (cfg 1 false [] (s.reverse ++ a) (s.reverse ++ b) out) := by
  induction s generalizing a b v with
  | nil => exact copy_nil v a b out
  | cons d s ih =>
      change (ShiTMSubroutine.run program)^[s.length+1+1] _ = _
      rw [Function.iterate_succ_apply, copy_cons]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (d::a) (d::b) d

theorem restore_run (s a b out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run program)^[a.length+1] (some (cfg 1 v s a b out)) =
    some (cfg 2 false (a.reverse ++ s) [] b out) := by
  induction a generalizing s v with
  | nil => exact restore_nil v s b out
  | cons d a ih =>
      change (ShiTMSubroutine.run program)^[a.length+1+1] _ = _
      rw [Function.iterate_succ_apply, restore_cons]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (d::s) d

theorem output_run (s a b out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run program)^[b.length+1] (some (cfg 2 v s a b out)) =
    some (⟨none,false,tapes s a [] (b.reverse ++ out)⟩ : Cfg Gam Label Bool) := by
  induction b generalizing out v with
  | nil => exact output_nil v s a out
  | cons d b ih =>
      change (ShiTMSubroutine.run program)^[b.length+1+1] _ = _
      rw [Function.iterate_succ_apply, output_cons]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (d::out) d

/-- Retain a complete source bitstring and prepend an identical copy to output,
clearing both work stacks in an exact linear number of transitions. -/
theorem retain_copy_run (s out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run program)^[3*s.length+3] (some (cfg 0 v s [] [] out)) =
    some (⟨none,false,tapes s [] [] (s ++ out)⟩ : Cfg Gam Label Bool) := by
  rw [show 3*s.length+3 = ((s.length+1)+(s.length+1))+(s.length+1) by omega,
    Function.iterate_add_apply, copy_run]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply]
  have hr := restore_run [] s.reverse s.reverse out false
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  rw [hr]
  simpa only [List.length_reverse, List.reverse_reverse] using output_run s [] s.reverse out false

end BQPCopyBits
