import «AMPUNI-subroutine-lift»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPSkipHeaders
open Turing Turing.TM2
abbrev Gam : Unit → Type := fun _ => Bool

def dropHeader : List Bool → List Bool
  | [] => []
  | false::s => s
  | true::s => dropHeader s

def headerTime : List Bool → ℕ
  | [] => 1
  | false::_ => 1
  | true::s => headerTime s + 1

def program (second : Bool) : Stmt Gam Bool Bool :=
  .pop () (fun _ a => a.getD false) (.branch id
    (.goto (fun _ => second))
    (.load (fun _ => false) (if second then .halt else .goto (fun _ => true))))

def cfg (second v : Bool) (s : List Bool) : Cfg Gam Bool Bool := ⟨some second,v,fun _ => s⟩

@[simp] theorem update_tape (s t : List Bool) :
    Function.update (fun _ : Unit => s) () t = fun _ => t := by
  funext u; cases u; simp

theorem true_step (second v : Bool) (s : List Bool) :
    ShiTMSubroutine.run program (some (cfg second v (true::s))) = some (cfg second true s) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem first_nil (v : Bool) :
    ShiTMSubroutine.run program (some (cfg false v [])) = some (cfg true false []) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem first_false (v : Bool) (s : List Bool) :
    ShiTMSubroutine.run program (some (cfg false v (false::s))) = some (cfg true false s) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem second_nil (v : Bool) :
    ShiTMSubroutine.run program (some (cfg true v [])) =
    some (⟨none,false,fun _ => []⟩ : Cfg Gam Bool Bool) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem second_false (v : Bool) (s : List Bool) :
    ShiTMSubroutine.run program (some (cfg true v (false::s))) =
    some (⟨none,false,fun _ => s⟩ : Cfg Gam Bool Bool) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem first_run (s : List Bool) (v : Bool) :
    (ShiTMSubroutine.run program)^[headerTime s] (some (cfg false v s)) =
    some (cfg true false (dropHeader s)) := by
  induction s generalizing v with
  | nil => exact first_nil v
  | cons b s ih =>
      cases b with
      | false => exact first_false v s
      | true =>
          change (ShiTMSubroutine.run program)^[headerTime s+1] _ = _
          rw [Function.iterate_succ_apply, true_step]
          exact ih true

theorem second_run (s : List Bool) (v : Bool) :
    (ShiTMSubroutine.run program)^[headerTime s] (some (cfg true v s)) =
    some (⟨none,false,fun _ => dropHeader s⟩ : Cfg Gam Bool Bool) := by
  induction s generalizing v with
  | nil => exact second_nil v
  | cons b s ih =>
      cases b with
      | false => exact second_false v s
      | true =>
          change (ShiTMSubroutine.run program)^[headerTime s+1] _ = _
          rw [Function.iterate_succ_apply, true_step]
          exact ih true

theorem two_run (s : List Bool) (v : Bool) :
    (ShiTMSubroutine.run program)^[headerTime s + headerTime (dropHeader s)]
      (some (cfg false v s)) =
    some (⟨none,false,fun _ => dropHeader (dropHeader s)⟩ : Cfg Gam Bool Bool) := by
  rw [Nat.add_comm, Function.iterate_add_apply, first_run]
  exact second_run _ false

theorem time_remaining_le (s : List Bool) : headerTime s + (dropHeader s).length ≤ s.length+1 := by
  induction s with
  | nil => simp [headerTime,dropHeader]
  | cons b s ih => cases b <;> simp only [headerTime,dropHeader,List.length_cons] <;> omega

theorem two_time_le (s : List Bool) : headerTime s + headerTime (dropHeader s) ≤ s.length+2 := by
  have h := time_remaining_le s
  have h' := time_remaining_le (dropHeader s)
  omega

abbrev machine : FinTM2 where
  K := Unit
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := ()
  k₁ := ()
  Γ := Gam
  Λ := Bool
  main := false
  ΛFin := inferInstance
  σ := Bool
  initialState := false
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := program

theorem initial_eq (s : List Bool) : initList machine s = cfg false false s := by
  apply congrArg (fun S => (⟨some false,false,S⟩ : Cfg Gam Bool Bool))
  funext u; cases u; rfl

theorem final_eq (s : List Bool) :
    (⟨none,false,fun _ => s⟩ : Cfg Gam Bool Bool) = haltList machine s := by
  apply congrArg (fun S => (⟨none,false,S⟩ : Cfg Gam Bool Bool))
  funext u; cases u; rfl

set_option backward.isDefEq.respectTransparency false in
def outputs (s : List Bool) : TM2OutputsInTime machine s
    (some (dropHeader (dropHeader s))) (s.length+2) := by
  refine { steps := headerTime s + headerTime (dropHeader s), steps_le_m := two_time_le s, evals_in_steps := ?_ }
  change (ShiTMSubroutine.run program)^[headerTime s + headerTime (dropHeader s)]
    (some (initList machine s)) = some (haltList machine (dropHeader (dropHeader s)))
  rw [initial_eq, ← final_eq]
  exact two_run s false

/-- A total linear-time field extractor, including malformed/truncated strings. -/
theorem polyTime : Nonempty (TM2ComputableInPolyTime id id (fun s => dropHeader (dropHeader s))) := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.X + Polynomial.C 2
            outputsFun := ?_ }⟩
  intro s
  simpa only [id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl, List.map_id,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] using outputs s

theorem dropHeader_unary (n : ℕ) (s : List Bool) :
    dropHeader (List.replicate n true ++ false::s) = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append, dropHeader] using ih

/-- Two actual unary fields are discarded, preserving the entire circuit suffix. -/
theorem two_unary (a b : ℕ) (s : List Bool) :
    dropHeader (dropHeader (List.replicate a true ++ false::(List.replicate b true ++ false::s))) = s := by
  rw [dropHeader_unary, dropHeader_unary]

end BQPSkipHeaders
