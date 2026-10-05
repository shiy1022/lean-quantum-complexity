import «BQP-cnot-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPCnot
open Turing Turing.TM2

instance : Fintype Label := ⟨{.compare, .choose, .less 0, .less 1, .less 2, .less 3,
    .greater 0, .greater 1, .greater 2, .greater 3}, by
  intro l
  cases l with
  | compare => simp
  | choose => simp
  | less l => fin_cases l <;> simp
  | greater l => fin_cases l <;> simp⟩

theorem choose_false (a b c d e out : List Bool) :
    ShiTMSubroutine.run program (some (cfg .choose false a b c d e out)) =
    some (cfg (.less 0) false a b c d e out) := rfl

theorem choose_true (a b c d e out : List Bool) :
    ShiTMSubroutine.run program (some (cfg .choose true a b c d e out)) =
    some (cfg (.greater 0) true a b c d e out) := rfl

private theorem chain {α : Type} (f : α → α) (x y z : α) (a b : ℕ)
    (h : f^[a] x = y) (h' : f^[b] y = z) : f^[a+b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, h, h']

/-- Both counters are computed by the machine from the two indices. -/
theorem from_indices_lt (i j : ℕ) (hlt : i < j) (v : Bool) (out : List Bool) :
    (ShiTMSubroutine.run program)^[i+2*j+6]
      (some (cfg .compare v (List.replicate i true) (List.replicate j true) [] [] [] out)) =
    some (⟨none,false,tapes [] [] [] [] []
      (BQPOpcodeEmission.encode (BQPNestedBlock.block i (j-i) [6] [7] []) ++ out)⟩ :
      Cfg Gam Label Bool) := by
  have hc := compare_run i j v out
  have hn : ¬ j < i := by omega
  simp only [Nat.min_eq_left (Nat.le_of_lt hlt), Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt),
    List.replicate_zero, decide_eq_false hn] at hc
  have hd := choose_false [] (List.replicate (j-i) true) (List.replicate i true) [] [] out
  have he := less_run (List.replicate i true) (List.replicate (j-i) true) out false
  simp only [List.length_replicate] at he
  have ht := chain _ _ _ _ (i+1) 1 hc hd
  have hall := chain _ _ _ _ _ _ ht he
  rw [show (i+1+1)+(2*i+2*(j-i)+4) = i+2*j+6 by omega] at hall
  exact hall

theorem from_indices_gt (i j : ℕ) (hgt : j < i) (v : Bool) (out : List Bool) :
    (ShiTMSubroutine.run program)^[j+2*i+6]
      (some (cfg .compare v (List.replicate i true) (List.replicate j true) [] [] [] out)) =
    some (⟨none,false,tapes [] [] [] [] []
      (BQPOpcodeEmission.encode (BQPNestedBlock.block j (i-j) [] [6] [7]) ++ out)⟩ :
      Cfg Gam Label Bool) := by
  have hc := compare_run i j v out
  simp only [Nat.min_eq_right (Nat.le_of_lt hgt), Nat.sub_eq_zero_of_le (Nat.le_of_lt hgt),
    List.replicate_zero, decide_eq_true hgt] at hc
  have hd := choose_true (List.replicate (i-j) true) [] (List.replicate j true) [] [] out
  have he := greater_run (List.replicate j true) (List.replicate (i-j) true) out true
  simp only [List.length_replicate] at he
  have ht := chain _ _ _ _ (j+1) 1 hc hd
  have hall := chain _ _ _ _ _ _ ht he
  rw [show (j+1+1)+(2*j+2*(i-j)+4) = j+2*i+6 by omega] at hall
  exact hall

end BQPCnot
