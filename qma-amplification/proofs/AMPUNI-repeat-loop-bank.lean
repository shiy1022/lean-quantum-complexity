import «AMPUNI-repeat-controller-restart»

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiTMRepeatController

/-- Auxiliary-stack layout at the start of a body call. -/
def bank (b : Bool) (n remaining : Nat) : Aux → List Bool
  | 0 => []
  | 1 => if b then [] else List.replicate n true
  | 2 => if b then List.replicate n true else []
  | 3 => List.replicate remaining true

theorem bank_scratch (b : Bool) (n q : Nat) :
    bank b n q scratch = [] := by
  cases b <;> rfl

theorem bank_active (b : Bool) (n q : Nat) :
    bank b n q (header b) = List.replicate n true := by
  cases b <;> rfl

theorem bank_other (b : Bool) (n q : Nat) :
    bank b n q (header (!b)) = [] := by
  cases b <;> rfl

theorem bank_counter (b : Bool) (n q : Nat) :
    bank b n q counter = List.replicate q true := by
  cases b <;> rfl

theorem bank_pop_counter (b : Bool) (n q : Nat) :
    Function.update (bank b n (q + 1)) counter
      (List.replicate q true) = bank b n q := by
  funext j
  fin_cases j <;> cases b <;>
    simp [bank, counter, Function.update, List.replicate_succ]

end ShiTMRepeatController
