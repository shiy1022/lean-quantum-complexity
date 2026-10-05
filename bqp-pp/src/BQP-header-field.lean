import «BQP-skip-headers»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPHeaderField
open Turing Turing.TM2
abbrev K := Fin 2
abbrev Gam : K → Type := fun _ => Bool

def count : List Bool → ℕ
  | [] => 0
  | false::_ => 0
  | true::s => count s + 1

def program (drain : Bool) : Stmt Gam Bool Bool :=
  .peek 0 (fun _ a => a.isSome) (.branch id
    (.pop 0 (fun _ a => a.getD false)
      (if drain then .goto (fun _ => true)
       else .branch id (.push 1 (fun _ => true) (.goto (fun _ => false)))
         (.goto (fun _ => true))))
    (.load (fun _ => false) .halt))

def tapes (s out : List Bool) : K → List Bool := fun k => if k = 0 then s else out
def cfg (drain v : Bool) (s out : List Bool) : Cfg Gam Bool Bool :=
  ⟨some drain,v,tapes s out⟩

@[simp] theorem tape0 (s out : List Bool) : tapes s out 0 = s := rfl
@[simp] theorem tape1 (s out : List Bool) : tapes s out 1 = out := rfl
@[simp] theorem update0 (s out t : List Bool) : Function.update (tapes s out) 0 t = tapes t out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update1 (s out t : List Bool) : Function.update (tapes s out) 1 t = tapes s t := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem nil_step (drain v : Bool) (out : List Bool) :
    ShiTMSubroutine.run program (some (cfg drain v [] out)) =
      some (⟨none,false,tapes [] out⟩ : Cfg Gam Bool Bool) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem drain_step (v b : Bool) (s out : List Bool) :
    ShiTMSubroutine.run program (some (cfg true v (b::s) out)) =
      some (cfg true b s out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem true_step (v : Bool) (s out : List Bool) :
    ShiTMSubroutine.run program (some (cfg false v (true::s) out)) =
      some (cfg false true s (true::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem false_step (v : Bool) (s out : List Bool) :
    ShiTMSubroutine.run program (some (cfg false v (false::s) out)) =
      some (cfg true false s out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem drain_run (s out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run program)^[s.length+1] (some (cfg true v s out)) =
      some (⟨none,false,tapes [] out⟩ : Cfg Gam Bool Bool) := by
  induction s generalizing v with
  | nil => exact nil_step true v out
  | cons b s ih =>
      change (ShiTMSubroutine.run program)^[s.length+1+1] _ = _
      rw [Function.iterate_succ_apply, drain_step]
      exact ih b

/-- The first unary field is emitted without its terminator; the entire suffix
is drained, including malformed inputs, so the output configuration is clean. -/
theorem field_run (s out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run program)^[s.length+1] (some (cfg false v s out)) =
      some (⟨none,false,tapes [] (List.replicate (count s) true ++ out)⟩ : Cfg Gam Bool Bool) := by
  induction s generalizing v out with
  | nil => exact nil_step false v out
  | cons b s ih =>
      change (ShiTMSubroutine.run program)^[s.length+1+1] _ = _
      rw [Function.iterate_succ_apply]
      cases b with
      | false => rw [false_step]; exact drain_run s out false
      | true =>
          rw [true_step]
          simpa only [count, List.replicate_succ', List.append_assoc, List.singleton_append] using
            ih (out := true::out) (v := true)

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
  σ := Bool
  initialState := false
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := program

theorem initial_eq (s : List Bool) : initList machine s = cfg false false s [] := by
  apply congrArg (fun S => (⟨some false,false,S⟩ : Cfg Gam Bool Bool))
  funext k; fin_cases k <;> rfl

theorem final_eq (s : List Bool) :
    (⟨none,false,tapes [] s⟩ : Cfg Gam Bool Bool) = haltList machine s := by
  apply congrArg (fun S => (⟨none,false,S⟩ : Cfg Gam Bool Bool))
  funext k; fin_cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
def outputs (s : List Bool) : TM2OutputsInTime machine s
    (some (List.replicate (count s) true)) (s.length+1) := by
  refine { steps := s.length+1, steps_le_m := le_refl _, evals_in_steps := ?_ }
  change (ShiTMSubroutine.run program)^[s.length+1] (some (initList machine s)) =
    some (haltList machine _)
  rw [initial_eq, ← final_eq]
  simpa only [List.append_nil] using field_run s [] false

theorem polyTime : Nonempty (TM2ComputableInPolyTime id id (fun s => List.replicate (count s) true)) := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.X + Polynomial.C 1
            outputsFun := ?_ }⟩
  intro s
  simpa only [id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl,
    List.map_id, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] using outputs s

theorem count_unary (n : ℕ) (s : List Bool) :
    count (List.replicate n true ++ false::s) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append, count, ih]

end BQPHeaderField
