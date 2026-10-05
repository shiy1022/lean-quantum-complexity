import «BQP-opcode-emission»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace BQPOpcodeCount
open Turing Turing.TM2
abbrev K := Fin 2
abbrev Gam : K → Type := fun _ => Bool
abbrev Reg := Bool × Bool × Bool × Bool

def zero : Reg := (false,false,false,false)
def selected (r : Reg) : Bool := !r.1 && !r.2.1 && r.2.2.1 && !r.2.2.2

def program (_ : Unit) : Stmt Gam Unit Reg :=
  .peek 0 (fun _ a => (a.isSome,false,false,false)) (.branch (fun r => r.1)
    (.pop 0 (fun r a => (a.getD false,r.2))
      (.pop 0 (fun r a => (r.1,a.getD false,r.2.2))
        (.pop 0 (fun r a => (r.1,r.2.1,a.getD false,r.2.2.2))
          (.pop 0 (fun r a => (r.1,r.2.1,r.2.2.1,a.getD false))
            (.branch selected (.push 1 (fun _ => true) (.goto (fun _ => ())))
              (.goto (fun _ => ())))))))
    (.load (fun _ => zero) .halt))

def tapes (s out : List Bool) : K → List Bool := fun k => if k = 0 then s else out
def cfg (v : Reg) (s out : List Bool) : Cfg Gam Unit Reg := ⟨some (),v,tapes s out⟩
def nibble (a b c d : Bool) : Reg := (a,b,c,d)
def mark (a b c d : Bool) : ℕ := if selected (nibble a b c d) then 1 else 0

def count : List Bool → ℕ
  | a::b::c::d::s => mark a b c d + count s
  | _ => 0

@[simp] theorem tape0 (s out : List Bool) : tapes s out 0 = s := rfl
@[simp] theorem tape1 (s out : List Bool) : tapes s out 1 = out := rfl
@[simp] theorem update0 (s out t : List Bool) : Function.update (tapes s out) 0 t = tapes t out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update1 (s out t : List Bool) : Function.update (tapes s out) 1 t = tapes s t := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem block_step (v : Reg) (a b c d : Bool) (s out : List Bool) :
    ShiTMSubroutine.run program (some (cfg v (a::b::c::d::s) out)) =
      some (cfg (nibble a b c d) s (List.replicate (mark a b c d) true ++ out)) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [ShiTMSubroutine.run, step, stepAux, program, cfg, nibble, selected, mark]

theorem nil_step (v : Reg) (out : List Bool) :
    ShiTMSubroutine.run program (some (cfg v [] out)) =
      some (⟨none,zero,tapes [] out⟩ : Cfg Gam Unit Reg) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

/-- One transition per four-bit opcode. Only Hadamard's 0010 opcode emits a marker. -/
theorem blocks_run (blocks : List Reg) (out : List Bool) (v : Reg) :
    (ShiTMSubroutine.run program)^[blocks.length+1]
      (some (cfg v ((blocks.map (fun r => [r.1,r.2.1,r.2.2.1,r.2.2.2])).flatten) out)) =
      some (⟨none,zero,tapes []
        (List.replicate ((blocks.map (fun r => if selected r then 1 else 0)).sum) true ++ out)⟩ :
        Cfg Gam Unit Reg) := by
  induction blocks generalizing out v with
  | nil => exact nil_step v out
  | cons r rs ih =>
      rcases r with ⟨a,b,c,d⟩
      change (ShiTMSubroutine.run program)^[rs.length+1+1] _ = _
      rw [Function.iterate_succ_apply]
      simp only [List.map_cons, List.flatten_cons, List.cons_append, List.nil_append]
      rw [block_step]
      have h := ih (out := List.replicate (mark a b c d) true ++ out) (v := nibble a b c d)
      simpa only [List.map_cons, List.sum_cons, mark, nibble, ← List.append_assoc,
        ← List.replicate_add, Nat.add_comm] using h

end BQPOpcodeCount
