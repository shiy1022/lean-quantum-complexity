import «BQP-skip-headers»

set_option autoImplicit false
namespace BQPSkipHeaders
open Turing Turing.TM2

/-- Start the same machine in its second-header state to discard just one field. -/
abbrev oneMachine : FinTM2 := { machine with main := true }

theorem one_initial_eq (s : List Bool) : initList oneMachine s = cfg true false s := by
  apply congrArg (fun S => (⟨some true,false,S⟩ : Cfg Gam Bool Bool))
  funext u; cases u; rfl

theorem one_final_eq (s : List Bool) :
    (⟨none,false,fun _ => s⟩ : Cfg Gam Bool Bool) = haltList oneMachine s := by
  apply congrArg (fun S => (⟨none,false,S⟩ : Cfg Gam Bool Bool))
  funext u; cases u; rfl

set_option backward.isDefEq.respectTransparency false in
def one_outputs (s : List Bool) : TM2OutputsInTime oneMachine s
    (some (dropHeader s)) (s.length+1) := by
  refine { steps := headerTime s
           steps_le_m := (Nat.le_add_right _ _).trans (time_remaining_le s)
           evals_in_steps := ?_ }
  change (ShiTMSubroutine.run program)^[headerTime s] (some (initList oneMachine s)) =
    some (haltList oneMachine _)
  rw [one_initial_eq, ← one_final_eq]
  exact second_run s false

theorem one_polyTime : Nonempty (TM2ComputableInPolyTime id id dropHeader) := by
  refine ⟨{ tm := oneMachine
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.X + Polynomial.C 1
            outputsFun := ?_ }⟩
  intro s
  simpa only [id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl,
    List.map_id, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] using one_outputs s

end BQPSkipHeaders
