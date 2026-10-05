import «BQP-opcode-emission»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPUnaryBlock
open Turing Turing.TM2

abbrev K := Fin 3
abbrev Label := Bool
abbrev State := Bool
abbrev Gam : K → Type := fun _ => Bool

/-- The first loop counts unary marks, emitting moves to the selected wire.
The second loop consumes the saved marks and emits the matching return moves.
The body is fixed finite control, such as H, S, T, X, or their fixed adjoints. -/
def program (body : List ℕ) : Label → Stmt Gam Label State
  | false => .pop 0 (fun _ a => a.isSome)
      (.branch id
        (BQPOpcodeEmission.emit 2 (Equiv.refl Bool) [1]
          (.push 1 (fun _ => true) (.goto (fun _ => false))))
        (BQPOpcodeEmission.emit 2 (Equiv.refl Bool) body (.goto (fun _ => true))))
  | true => .pop 1 (fun _ a => a.isSome)
      (.branch id
        (BQPOpcodeEmission.emit 2 (Equiv.refl Bool) [0] (.goto (fun _ => true)))
        (.load (fun _ => false) .halt))

abbrev machine (body : List ℕ) : FinTM2 where
  K := K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := 0
  k₁ := 2
  Γ := Gam
  Λ := Label
  main := false
  ΛFin := inferInstance
  σ := State
  initialState := false
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := program body

def tapes (xs buf out : List Bool) : ∀ k : K, List (Gam k) :=
  fun k => if k = 0 then xs else if k = 1 then buf else out

def cfg (l v : Bool) (xs buf out : List Bool) : Cfg Gam Label State :=
  ⟨some l,v,tapes xs buf out⟩

@[simp] theorem update_input (xs buf out t : List Bool) :
    Function.update (tapes xs buf out) 0 t = tapes t buf out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update_buffer (xs buf out t : List Bool) :
    Function.update (tapes xs buf out) 1 t = tapes xs t out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update_output (xs buf out t : List Bool) :
    Function.update (tapes xs buf out) 2 t = tapes xs buf t := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape0 (xs buf out : List Bool) : tapes xs buf out 0 = xs := rfl
@[simp] theorem tape1 (xs buf out : List Bool) : tapes xs buf out 1 = buf := rfl
@[simp] theorem tape2 (xs buf out : List Bool) : tapes xs buf out 2 = out := rfl

theorem outward_cons (body : List ℕ) (a v : Bool) (xs buf out : List Bool) :
    ShiTMSubroutine.run (program body) (some (cfg false v (a::xs) buf out)) =
    some (cfg false true xs (true::buf) (BQPOpcodeEmission.bits 1 ++ out)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux,
    BQPOpcodeEmission.stepAux_emit, BQPOpcodeEmission.encode]

theorem outward_nil (body : List ℕ) (v : Bool) (buf out : List Bool) :
    ShiTMSubroutine.run (program body) (some (cfg false v [] buf out)) =
    some (cfg true false [] buf (BQPOpcodeEmission.encode body ++ out)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux,
    BQPOpcodeEmission.stepAux_emit]

theorem inward_cons (body : List ℕ) (a v : Bool) (xs buf out : List Bool) :
    ShiTMSubroutine.run (program body) (some (cfg true v xs (a::buf) out)) =
    some (cfg true true xs buf (BQPOpcodeEmission.bits 0 ++ out)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux,
    BQPOpcodeEmission.stepAux_emit, BQPOpcodeEmission.encode]

theorem inward_nil (body : List ℕ) (v : Bool) (xs out : List Bool) :
    ShiTMSubroutine.run (program body) (some (cfg true v xs [] out)) =
    some (⟨none,false,tapes xs [] out⟩ : Cfg Gam Label State) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux]

end BQPUnaryBlock
