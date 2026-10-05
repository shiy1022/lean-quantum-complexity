import «BQP-opcode-emission»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPBitBlocks
open Turing Turing.TM2
abbrev K := Fin 2
abbrev Gam : K → Type := fun _ => Bool

def program (no yes : List ℕ) (_ : Unit) : Stmt Gam Unit Bool :=
  .peek 0 (fun _ a => a.isSome) (.branch id
    (.pop 0 (fun _ a => a.getD false) (.branch id
      (BQPOpcodeEmission.emit 1 (Equiv.refl Bool) yes (.goto (fun _ => ())))
      (BQPOpcodeEmission.emit 1 (Equiv.refl Bool) no (.goto (fun _ => ())))))
    (.load (fun _ => false) .halt))

def tapes (s out : List Bool) : K → List Bool := fun k => if k = 0 then s else out
def cfg (v : Bool) (s out : List Bool) : Cfg Gam Unit Bool := ⟨some (),v,tapes s out⟩
def render (no yes : List ℕ) : List Bool → List ℕ
  | [] => []
  | b::s => (if b then yes else no) ++ render no yes s

@[simp] theorem tape0 (s out : List Bool) : tapes s out 0 = s := rfl
@[simp] theorem tape1 (s out : List Bool) : tapes s out 1 = out := rfl
@[simp] theorem update0 (s out t : List Bool) : Function.update (tapes s out) 0 t = tapes t out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update1 (s out t : List Bool) : Function.update (tapes s out) 1 t = tapes s t := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem cons_step (no yes : List ℕ) (v b : Bool) (s out : List Bool) :
    ShiTMSubroutine.run (program no yes) (some (cfg v (b::s) out)) =
    some (cfg b s (BQPOpcodeEmission.encode (if b then yes else no) ++ out)) := by
  cases b <;> simp [ShiTMSubroutine.run, step, stepAux, program, cfg, BQPOpcodeEmission.stepAux_emit]

theorem nil_step (no yes : List ℕ) (v : Bool) (out : List Bool) :
    ShiTMSubroutine.run (program no yes) (some (cfg v [] out)) =
    some (⟨none,false,tapes [] out⟩ : Cfg Gam Unit Bool) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

/-- Render one fixed opcode block per source bit using finite machine control.
The source stack is drained and all prior output is preserved. -/
theorem render_run (no yes : List ℕ) (s out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run (program no yes))^[s.length+1] (some (cfg v s out)) =
    some (⟨none,false,tapes [] (BQPOpcodeEmission.encode (render no yes s) ++ out)⟩ : Cfg Gam Unit Bool) := by
  induction s generalizing v out with
  | nil => exact nil_step no yes v out
  | cons b s ih =>
      change (ShiTMSubroutine.run (program no yes))^[s.length+1+1] _ = _
      rw [Function.iterate_succ_apply, cons_step]
      simpa only [render, BQPOpcodeEmission.encode_append, List.append_assoc] using
        ih (out := BQPOpcodeEmission.encode (if b then yes else no) ++ out) (v := b)

end BQPBitBlocks
