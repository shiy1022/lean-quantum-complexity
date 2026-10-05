import «AMPUNI-subroutine-lift»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace BQPBinaryAdd
open Turing Turing.TM2

def value : List Bool → ℕ
  | [] => 0
  | b::s => (if b then 1 else 0) + 2 * value s

def digit (a b carry : Bool) : Bool := xor (xor a b) carry

def nextCarry (a b carry : Bool) : Bool := (a && b) || ((a || b) && carry)

/-- Little-endian addition retains one final carry bit, including a zero carry. -/
def add : List Bool → List Bool → Bool → List Bool
  | [], [], carry => [carry]
  | [], b::t, carry => digit false b carry :: add [] t (nextCarry false b carry)
  | a::s, [], carry => digit a false carry :: add s [] (nextCarry a false carry)
  | a::s, b::t, carry => digit a b carry :: add s t (nextCarry a b carry)
termination_by s t _ => s.length+t.length

theorem add_correct (s t : List Bool) (carry : Bool) :
    value (add s t carry) = value s + value t + (if carry then 1 else 0) := by
  induction s generalizing t carry with
  | nil =>
      induction t generalizing carry with
      | nil => cases carry <;> simp [add, value]
      | cons b t ih =>
          rw [add]
          simp only [value]
          rw [ih]
          cases b <;> cases carry <;> simp [digit, nextCarry, value] <;> omega
  | cons a s ih =>
      cases t with
      | nil =>
          rw [add]
          simp only [value]
          rw [ih]
          cases a <;> cases carry <;> simp [digit, nextCarry, value] <;> omega
      | cons b t =>
          rw [add]
          simp only [value]
          rw [ih]
          cases a <;> cases b <;> cases carry <;>
            simp [digit, nextCarry, value] <;> omega

theorem add_length (s t : List Bool) (carry : Bool) :
    (add s t carry).length = max s.length t.length + 1 := by
  induction s generalizing t carry with
  | nil =>
      induction t generalizing carry with
      | nil => simp [add]
      | cons b t ih => simp [add, ih]
  | cons a s ih =>
      cases t with
      | nil => simp [add, ih]
      | cons b t => simp [add, ih, Nat.add_max_add_right]

abbrev K := Fin 3
abbrev Gam : K → Type := fun _ => Bool
abbrev Reg := Bool × Bool × Bool

def program (_ : Unit) : Stmt Gam Unit Reg :=
  .peek 0 (fun r a => (r.1,a.isSome,false))
    (.peek 1 (fun r a => (r.1,r.2.1,a.isSome))
      (.branch (fun r => r.2.1 || r.2.2)
        (.pop 0 (fun r a => (r.1,a.getD false,false))
          (.pop 1 (fun r b => (r.1,r.2.1,b.getD false))
            (.push 2 (fun r => digit r.2.1 r.2.2 r.1)
              (.load (fun r => (nextCarry r.2.1 r.2.2 r.1,false,false))
                (.goto (fun _ => ()))))))
        (.push 2 (fun r => r.1) (.load (fun _ => (false,false,false)) .halt))))

def tapes (s t out : List Bool) : K → List Bool :=
  fun k => if k = 0 then s else if k = 1 then t else out

def cfg (carry : Bool) (s t out : List Bool) : Cfg Gam Unit Reg :=
  ⟨some (),(carry,false,false),tapes s t out⟩

@[simp] theorem tape0 (s t out : List Bool) : tapes s t out 0 = s := rfl
@[simp] theorem tape1 (s t out : List Bool) : tapes s t out 1 = t := rfl
@[simp] theorem tape2 (s t out : List Bool) : tapes s t out 2 = out := rfl
@[simp] theorem update0 (s t out u : List Bool) :
    Function.update (tapes s t out) 0 u = tapes u t out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update1 (s t out u : List Bool) :
    Function.update (tapes s t out) 1 u = tapes s u out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update2 (s t out u : List Bool) :
    Function.update (tapes s t out) 2 u = tapes s t u := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem nil_step (carry : Bool) (out : List Bool) :
    ShiTMSubroutine.run program (some (cfg carry [] [] out)) =
      some (⟨none,(false,false,false),tapes [] [] (carry::out)⟩ : Cfg Gam Unit Reg) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem both_step (a b carry : Bool) (s t out : List Bool) :
    ShiTMSubroutine.run program (some (cfg carry (a::s) (b::t) out)) =
      some (cfg (nextCarry a b carry) s t (digit a b carry::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem left_step (a carry : Bool) (s out : List Bool) :
    ShiTMSubroutine.run program (some (cfg carry (a::s) [] out)) =
      some (cfg (nextCarry a false carry) s [] (digit a false carry::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem right_step (b carry : Bool) (t out : List Bool) :
    ShiTMSubroutine.run program (some (cfg carry [] (b::t) out)) =
      some (cfg (nextCarry false b carry) [] t (digit false b carry::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

/-- Addition consumes both preloaded inputs in exactly max(widths)+1 steps.
The output stack is reversed, ready for a linear stack-transfer pass. -/
theorem add_run (s t out : List Bool) (carry : Bool) :
    (ShiTMSubroutine.run program)^[max s.length t.length+1]
      (some (cfg carry s t out)) =
      some (⟨none,(false,false,false),tapes [] [] ((add s t carry).reverse++out)⟩ : Cfg Gam Unit Reg) := by
  induction s generalizing t carry out with
  | nil =>
      induction t generalizing carry out with
      | nil => simpa [add] using nil_step carry out
      | cons b t ih =>
          change (ShiTMSubroutine.run program)^[t.length+1+1] _ = _
          rw [Function.iterate_succ_apply, right_step]
          simpa only [add, List.reverse_cons, List.append_assoc, List.singleton_append,
            List.length_nil, Nat.zero_max] using ih (digit false b carry::out) (nextCarry false b carry)
  | cons a s ih =>
      cases t with
      | nil =>
          change (ShiTMSubroutine.run program)^[s.length+1+1] _ = _
          rw [Function.iterate_succ_apply, left_step]
          simpa only [add, List.reverse_cons, List.append_assoc, List.singleton_append,
            List.length_nil, Nat.max_zero] using ih [] (digit a false carry::out) (nextCarry a false carry)
      | cons b t =>
          simp only [List.length_cons, Nat.add_max_add_right]
          rw [Function.iterate_succ_apply, both_step]
          simpa only [add, List.reverse_cons, List.append_assoc, List.singleton_append] using
            ih t (digit a b carry::out) (nextCarry a b carry)

end BQPBinaryAdd
