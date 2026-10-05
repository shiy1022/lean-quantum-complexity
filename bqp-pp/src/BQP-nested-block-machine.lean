import «BQP-opcode-emission»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPNestedBlock
open Turing Turing.TM2
abbrev K := Fin 5
abbrev Label := Fin 4
abbrev Gam : K → Type := fun _ => Bool

def program (pre mid post : List ℕ) (l : Label) : Stmt Gam Label Bool :=
  if l = 0 then
    .pop 0 (fun _ a => a.isSome) (.branch id
      (BQPOpcodeEmission.emit 4 (Equiv.refl Bool) [1]
        (.push 2 (fun _ => true) (.goto (fun _ => 0))))
      (BQPOpcodeEmission.emit 4 (Equiv.refl Bool) pre (.goto (fun _ => 1))))
  else if l = 1 then
    .pop 1 (fun _ a => a.isSome) (.branch id
      (BQPOpcodeEmission.emit 4 (Equiv.refl Bool) [1]
        (.push 3 (fun _ => true) (.goto (fun _ => 1))))
      (BQPOpcodeEmission.emit 4 (Equiv.refl Bool) mid (.goto (fun _ => 2))))
  else if l = 2 then
    .pop 3 (fun _ a => a.isSome) (.branch id
      (BQPOpcodeEmission.emit 4 (Equiv.refl Bool) [0] (.goto (fun _ => 2)))
      (BQPOpcodeEmission.emit 4 (Equiv.refl Bool) post (.goto (fun _ => 3))))
  else
    .pop 2 (fun _ a => a.isSome) (.branch id
      (BQPOpcodeEmission.emit 4 (Equiv.refl Bool) [0] (.goto (fun _ => 3)))
      (.load (fun _ => false) .halt))

def tapes (a b c d out : List Bool) : ∀ k : K, List (Gam k) :=
  fun k => if k = 0 then a else if k = 1 then b else if k = 2 then c else if k = 3 then d else out

def cfg (l : Label) (v : Bool) (a b c d out : List Bool) : Cfg Gam Label Bool :=
  ⟨some l,v,tapes a b c d out⟩

@[simp] theorem tape0 (a b c d out : List Bool) : tapes a b c d out 0 = a := rfl
@[simp] theorem update0 (a b c d out t : List Bool) :
    Function.update (tapes a b c d out) 0 t = tapes t b c d out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape1 (a b c d out : List Bool) : tapes a b c d out 1 = b := rfl
@[simp] theorem update1 (a b c d out t : List Bool) :
    Function.update (tapes a b c d out) 1 t = tapes a t c d out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape2 (a b c d out : List Bool) : tapes a b c d out 2 = c := rfl
@[simp] theorem update2 (a b c d out t : List Bool) :
    Function.update (tapes a b c d out) 2 t = tapes a b t d out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape3 (a b c d out : List Bool) : tapes a b c d out 3 = d := rfl
@[simp] theorem update3 (a b c d out t : List Bool) :
    Function.update (tapes a b c d out) 3 t = tapes a b c t out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape4 (a b c d out : List Bool) : tapes a b c d out 4 = out := rfl
@[simp] theorem update4 (a b c d out t : List Bool) :
    Function.update (tapes a b c d out) 4 t = tapes a b c d t := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem step0_cons (pre mid post : List ℕ) (v : Bool) (a b c d out : List Bool) (x : Bool) :
    ShiTMSubroutine.run (program pre mid post) (some (cfg 0 v (x::a) b c d out)) =
    some (cfg 0 true a b (true::c) d (BQPOpcodeEmission.bits 1 ++ out)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux,
    BQPOpcodeEmission.stepAux_emit, BQPOpcodeEmission.encode]

theorem step0_nil (pre mid post : List ℕ) (v : Bool) (a b c d out : List Bool) :
    ShiTMSubroutine.run (program pre mid post) (some (cfg 0 v [] b c d out)) =
    some (cfg 1 false [] b c d (BQPOpcodeEmission.encode pre ++ out)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux,
    BQPOpcodeEmission.stepAux_emit, BQPOpcodeEmission.encode]

theorem step1_cons (pre mid post : List ℕ) (v : Bool) (a b c d out : List Bool) (x : Bool) :
    ShiTMSubroutine.run (program pre mid post) (some (cfg 1 v a (x::b) c d out)) =
    some (cfg 1 true a b c (true::d) (BQPOpcodeEmission.bits 1 ++ out)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux,
    BQPOpcodeEmission.stepAux_emit, BQPOpcodeEmission.encode]

theorem step1_nil (pre mid post : List ℕ) (v : Bool) (a b c d out : List Bool) :
    ShiTMSubroutine.run (program pre mid post) (some (cfg 1 v a [] c d out)) =
    some (cfg 2 false a [] c d (BQPOpcodeEmission.encode mid ++ out)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux,
    BQPOpcodeEmission.stepAux_emit, BQPOpcodeEmission.encode]

theorem step2_cons (pre mid post : List ℕ) (v : Bool) (a b c d out : List Bool) (x : Bool) :
    ShiTMSubroutine.run (program pre mid post) (some (cfg 2 v a b c (x::d) out)) =
    some (cfg 2 true a b c d (BQPOpcodeEmission.bits 0 ++ out)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux,
    BQPOpcodeEmission.stepAux_emit, BQPOpcodeEmission.encode]

theorem step2_nil (pre mid post : List ℕ) (v : Bool) (a b c d out : List Bool) :
    ShiTMSubroutine.run (program pre mid post) (some (cfg 2 v a b c [] out)) =
    some (cfg 3 false a b c [] (BQPOpcodeEmission.encode post ++ out)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux,
    BQPOpcodeEmission.stepAux_emit, BQPOpcodeEmission.encode]

theorem step3_cons (pre mid post : List ℕ) (v : Bool) (a b c d out : List Bool) (x : Bool) :
    ShiTMSubroutine.run (program pre mid post) (some (cfg 3 v a b (x::c) d out)) =
    some (cfg 3 true a b c d (BQPOpcodeEmission.bits 0 ++ out)) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux,
    BQPOpcodeEmission.stepAux_emit, BQPOpcodeEmission.encode]

theorem step3_nil (pre mid post : List ℕ) (v : Bool) (a b c d out : List Bool) :
    ShiTMSubroutine.run (program pre mid post) (some (cfg 3 v a b [] d out)) =
    some (⟨none,false,tapes a b [] d out⟩ : Cfg Gam Label Bool) := by
  simp [ShiTMSubroutine.run, step, cfg, program, stepAux,
    BQPOpcodeEmission.stepAux_emit, BQPOpcodeEmission.encode]

end BQPNestedBlock
