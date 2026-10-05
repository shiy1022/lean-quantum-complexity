import «AMPUNI-subroutine-lift»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPUnaryCompare
open Turing Turing.TM2
abbrev K := Fin 3
abbrev Gam : K → Type := fun _ => Bool

/-- Cancel one mark from each index, accumulating their common prefix.
On exit the Boolean records whether the first index is larger. -/
def program (_ : Unit) : Stmt Gam Unit Bool :=
  .peek 0 (fun _ a => a.isSome) (.branch id
    (.peek 1 (fun _ a => a.isSome) (.branch id
      (.pop 0 (fun v _ => v) (.pop 1 (fun v _ => v)
        (.push 2 (fun _ => true) (.goto (fun _ => ())))))
      (.load (fun _ => true) .halt)))
    (.load (fun _ => false) .halt))

def tapes (a b c : List Bool) : ∀ k : K, List (Gam k) :=
  fun k => if k = 0 then a else if k = 1 then b else c

def cfg (v : Bool) (a b c : List Bool) : Cfg Gam Unit Bool := ⟨some (),v,tapes a b c⟩

@[simp] theorem tape0 (a b c : List Bool) : tapes a b c 0 = a := rfl
@[simp] theorem tape1 (a b c : List Bool) : tapes a b c 1 = b := rfl
@[simp] theorem tape2 (a b c : List Bool) : tapes a b c 2 = c := rfl

@[simp] theorem update0 (a b c t : List Bool) :
    Function.update (tapes a b c) 0 t = tapes t b c := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update1 (a b c t : List Bool) :
    Function.update (tapes a b c) 1 t = tapes a t c := by
  funext k; fin_cases k <;> simp [tapes, Function.update]
@[simp] theorem update2 (a b c t : List Bool) :
    Function.update (tapes a b c) 2 t = tapes a b t := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem both_cons (v x y : Bool) (a b c : List Bool) :
    ShiTMSubroutine.run program (some (cfg v (x::a) (y::b) c)) =
    some (cfg true a b (true::c)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem left_nil (v : Bool) (b c : List Bool) :
    ShiTMSubroutine.run program (some (cfg v [] b c)) =
    some (⟨none,false,tapes [] b c⟩ : Cfg Gam Unit Bool) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem right_nil (v x : Bool) (a c : List Bool) :
    ShiTMSubroutine.run program (some (cfg v (x::a) [] c)) =
    some (⟨none,true,tapes (x::a) [] c⟩ : Cfg Gam Unit Bool) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

private theorem replicate_append_cons (n : ℕ) (a : Bool) (bs : List Bool) :
    List.replicate n a ++ a :: bs = a :: (List.replicate n a ++ bs) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons a) ih

/-- Exact counter normalization: common prefix, absolute difference, orientation,
and linear clock are all proved from the two unary inputs. -/
theorem compare_run (i j : ℕ) (v : Bool) (c : List Bool) :
    (ShiTMSubroutine.run program)^[min i j+1]
      (some (cfg v (List.replicate i true) (List.replicate j true) c)) =
    some (⟨none,decide (j < i),tapes (List.replicate (i-j) true) (List.replicate (j-i) true)
      (List.replicate (min i j) true ++ c)⟩ : Cfg Gam Unit Bool) := by
  induction i generalizing j v c with
  | zero => simpa using left_nil v (List.replicate j true) c
  | succ i ih =>
      cases j with
      | zero => simpa [List.replicate_succ] using right_nil v true (List.replicate i true) c
      | succ j =>
          simp only [Nat.succ_min_succ, Nat.add_sub_add_right, Nat.add_lt_add_iff_right,
            List.replicate_succ, Function.iterate_succ_apply]
          rw [both_cons]
          simpa only [Function.iterate_succ_apply, List.replicate_succ, List.cons_append, replicate_append_cons] using ih j true (true::c)

end BQPUnaryCompare
