import «BQP-router-overflow»
import «AMPUNI-subroutine-lift»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace BQPBinaryCompare
open Turing Turing.TM2

def nextBorrow (a b carry : Bool) : Bool := if a then b && carry else b || carry

def borrow : List Bool → List Bool → Bool → Bool
  | [], [], carry => carry
  | [], b::t, carry => borrow [] t (nextBorrow false b carry)
  | a::s, [], carry => borrow s [] (nextBorrow a false carry)
  | a::s, b::t, carry => borrow s t (nextBorrow a b carry)
termination_by s t _ => s.length+t.length

theorem borrow_correct (s t : List Bool) (carry : Bool) :
    borrow s t carry = true ↔
      BQPCounting.suffixValue s < BQPCounting.suffixValue t + (if carry then 1 else 0) := by
  induction s generalizing t carry with
  | nil =>
      induction t generalizing carry with
      | nil => cases carry <;> simp [borrow, BQPCounting.suffixValue]
      | cons b t ih =>
          rw [borrow, ih]
          cases b <;> cases carry <;> simp [nextBorrow, BQPCounting.suffixValue] <;> omega
  | cons a s ih =>
      cases t with
      | nil =>
          rw [borrow, ih]
          cases a <;> cases carry <;> simp [nextBorrow, BQPCounting.suffixValue] <;> omega
      | cons b t =>
          rw [borrow, ih]
          cases a <;> cases b <;> cases carry <;>
            simp [nextBorrow, BQPCounting.suffixValue] <;> omega

abbrev K := Fin 3
abbrev Gam : K → Type := fun _ => Bool
abbrev Reg := Bool × Bool × Bool

def program (_ : Unit) : Stmt Gam Unit Reg :=
  .peek 0 (fun r a => (r.1,a.isSome,false))
    (.peek 1 (fun r a => (r.1,r.2.1,a.isSome))
      (.branch (fun r => r.2.1 || r.2.2)
        (.pop 0 (fun r a => (r.1,a.getD false,false))
          (.pop 1 (fun r b => (nextBorrow r.2.1 (b.getD false) r.1,false,false))
            (.goto (fun _ => ()))))
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
      some (cfg (nextBorrow a b carry) s t out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem left_step (a carry : Bool) (s out : List Bool) :
    ShiTMSubroutine.run program (some (cfg carry (a::s) [] out)) =
      some (cfg (nextBorrow a false carry) s [] out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem right_step (b carry : Bool) (t out : List Bool) :
    ShiTMSubroutine.run program (some (cfg carry [] (b::t) out)) =
      some (cfg (nextBorrow false b carry) [] t out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

/-- A finite bit-serial comparator handles unequal widths and every high bit.
Both source stacks are drained; the result is emitted with clean control state. -/
theorem compare_run (s t out : List Bool) (carry : Bool) :
    (ShiTMSubroutine.run program)^[max s.length t.length+1]
      (some (cfg carry s t out)) =
      some (⟨none,(false,false,false),tapes [] [] (borrow s t carry::out)⟩ : Cfg Gam Unit Reg) := by
  induction s generalizing t carry with
  | nil =>
      induction t generalizing carry with
      | nil => simpa [borrow] using nil_step carry out
      | cons b t ih =>
          change (ShiTMSubroutine.run program)^[t.length+1+1] _ = _
          rw [Function.iterate_succ_apply, right_step]
          simpa only [borrow, List.length_nil, Nat.zero_max] using ih (nextBorrow false b carry)
  | cons a s ih =>
      cases t with
      | nil =>
          change (ShiTMSubroutine.run program)^[s.length+1+1] _ = _
          rw [Function.iterate_succ_apply, left_step]
          simpa only [borrow, List.length_nil, Nat.max_zero] using ih [] (nextBorrow a false carry)
      | cons b t =>
          simp only [List.length_cons, Nat.add_max_add_right]
          rw [Function.iterate_succ_apply, both_step]
          simpa only [borrow] using ih t (nextBorrow a b carry)

 theorem compare_correct (s t : List Bool) :
    borrow s t false = decide (BQPCounting.suffixValue s < BQPCounting.suffixValue t) := by
  apply Bool.eq_iff_iff.mpr
  simpa using borrow_correct s t false

end BQPBinaryCompare
