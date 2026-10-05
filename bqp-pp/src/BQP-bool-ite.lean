import «AMPUNI-subroutine-lift»
import «BQP-closed-references»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BQPBoolIte
open Turing Turing.TM2
abbrev K := Fin 2
abbrev Gam : K → Type := fun _ => Bool
abbrev Reg := Bool × Bool × Bool × Bool

def program : Bool → Stmt Gam Bool Reg
  | false => .pop 0 (fun _ a => (a.getD false,false,false,false))
      (.pop 0 (fun r a => (r.1,a.getD false,false,false))
        (.pop 0 (fun r a => (r.1,r.2.1,a.getD false,false)) (.goto (fun _ => true))))
  | true => .pop 0 (fun r a => (r.1,r.2.1,r.2.2.1,a.isSome))
      (.branch (fun r => r.2.2.2) (.goto (fun _ => true))
        (.push 1 (fun r => if r.1 then r.2.1 else r.2.2.1)
          (.load (fun _ => (false,false,false,false)) .halt)))

def tapes (s out : List Bool) : K → List Bool := fun k => if k = 0 then s else out

def cfg (l : Bool) (r : Reg) (s out : List Bool) : Cfg Gam Bool Reg :=
  ⟨some l,r,tapes s out⟩

@[simp] theorem tape0 (s out : List Bool) : tapes s out 0 = s := rfl
@[simp] theorem tape1 (s out : List Bool) : tapes s out 1 = out := rfl
@[simp] theorem update0 (s out t : List Bool) : Function.update (tapes s out) 0 t = tapes t out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update1 (s out t : List Bool) : Function.update (tapes s out) 1 t = tapes s t := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem drain_cons (c a b flag d : Bool) (s out : List Bool) :
    ShiTMSubroutine.run program (some (cfg true (c,a,b,flag) (d::s) out)) =
    some (cfg true (c,a,b,true) s out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem drain_nil (c a b flag : Bool) (out : List Bool) :
    ShiTMSubroutine.run program (some (cfg true (c,a,b,flag) [] out)) =
    some (⟨none,(false,false,false,false),tapes [] ((if c then a else b)::out)⟩ : Cfg Gam Bool Reg) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem drain_run (s out : List Bool) (c a b flag : Bool) :
    (ShiTMSubroutine.run program)^[s.length+1] (some (cfg true (c,a,b,flag) s out)) =
    some (⟨none,(false,false,false,false),tapes [] ((if c then a else b)::out)⟩ : Cfg Gam Bool Reg) := by
  induction s generalizing flag with
  | nil => exact drain_nil c a b flag out
  | cons d s ih =>
      rw [List.length_cons, Function.iterate_succ_apply, drain_cons]
      exact ih true

def select (s : List Bool) : Bool := if s.headI then (s.drop 1).headI else (s.drop 2).headI

theorem first_step (s out : List Bool) :
    ShiTMSubroutine.run program (some (cfg false (false,false,false,false) s out)) =
    some (cfg true (s.headI,(s.drop 1).headI,(s.drop 2).headI,false) (s.drop 3) out) := by
  rcases s with _ | ⟨c, _ | ⟨a, _ | ⟨b,s⟩⟩⟩ <;>
    simp [ShiTMSubroutine.run, step, stepAux, program, cfg, List.headI]

theorem select_run (s : List Bool) :
    (ShiTMSubroutine.run program)^[(s.drop 3).length+2]
      (some (cfg false (false,false,false,false) s [])) =
      some (⟨none,(false,false,false,false),tapes [] [select s]⟩ : Cfg Gam Bool Reg) := by
  rw [show (s.drop 3).length+2 = ((s.drop 3).length+1)+1 by omega,
    Function.iterate_succ_apply, first_step]
  exact drain_run (s.drop 3) [] s.headI (s.drop 1).headI (s.drop 2).headI false

abbrev machine : FinTM2 where
  K := K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := 0
  k₁ := 1
  Γ := Gam
  Λ := Bool
  main := false
  ΛFin := inferInstance
  σ := Reg
  initialState := (false,false,false,false)
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := program

theorem initial_eq (s : List Bool) : initList machine s = cfg false (false,false,false,false) s [] := by
  apply congrArg (fun S => (⟨some false,(false,false,false,false),S⟩ : Cfg Gam Bool Reg))
  funext k; fin_cases k <;> rfl

theorem final_eq (out : List Bool) :
    (⟨none,(false,false,false,false),tapes [] out⟩ : Cfg Gam Bool Reg) = haltList machine out := by
  apply congrArg (fun S => (⟨none,(false,false,false,false),S⟩ : Cfg Gam Bool Reg))
  funext k; fin_cases k <;> rfl

def outputs (s : List Bool) : TM2OutputsInTime machine s (some [select s]) (s.length+2) := by
  refine { steps := (s.drop 3).length+2
           steps_le_m := by simp [List.length_drop]
           evals_in_steps := ?_ }
  change (ShiTMSubroutine.run program)^[_] (some (initList machine _)) = some (haltList machine _)
  rw [initial_eq, ← final_eq]
  exact select_run s

theorem polyTime : PvsNP.PolyTimeDecider select := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.X + Polynomial.C 2
            outputsFun := ?_ }⟩
  intro s
  simpa only [id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl,
    List.map_id, Computability.encodeBool, List.pure_def,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] using outputs s

end BQPBoolIte
