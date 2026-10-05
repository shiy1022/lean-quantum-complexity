import «BQP-gate-runs»
import «BQP-unary-block-integration»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPProgram
open Turing Turing.TM2 ShiShallow

def instructionCost {n : ℕ} : Instr n → ℕ
  | .h i => 3*(i : ℕ)+4
  | .s i => 3*(i : ℕ)+5
  | .t i => 3*(i : ℕ)+6
  | .x i => 3*(i : ℕ)+7
  | .cnot i j _ => (i : ℕ)+j+min (i : ℕ) j+2*max (i : ℕ) j+13

def instructionBody {n : ℕ} (adj : Bool) (g : Instr n) : List ℕ :=
  if adj then adjointBlock g else gateBlock g

theorem cnot_rendered_eq {n : ℕ} (i j : Fin n) (hne : i ≠ j) :
    BQPCnot.rendered i j = gateBlock (.cnot i j hne) := by
  simp only [BQPCnot.rendered, gateBlock, BQPNestedBlock.block, wrap]
  split <;> simp_all [List.append_assoc, -List.replicate_append_replicate]

/-- Each original circuit instruction is read and rendered by one fixed finite
machine. Both the forward and adjoint variants preserve all remaining input. -/
theorem instruction_run {n : ℕ} (C : Checker) (adj : Bool) (g : Instr n)
    (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run (BQPGateDispatch.program adj))^[instructionCost g]
      (some (BQPGateDispatch.cfg (.tag 0) v (ShiBQP.encInstr g ++ s) out)) =
    some (⟨none,false,BQPGateDispatch.inputStacks s
      (C.encode (instructionBody adj g) ++ out)⟩ :
      Cfg BQPGateDispatch.Gam BQPGateDispatch.Label Bool) := by
  cases g with
  | h i =>
      have hr := BQPGateDispatch.tagged_one_run adj (0 : Fin 4) i v s out
      cases adj <;> simpa [instructionCost, instructionBody, gateBlock, adjointBlock, wrap,
        ShiBQP.encInstr, ShiBQP.encNat, checker_encode_eq, BQPGateDispatch.body,
        List.append_assoc] using hr
  | s i =>
      have hr := BQPGateDispatch.tagged_one_run adj (1 : Fin 4) i v s out
      rw [show (1 : Fin 4).val+3*(i : ℕ)+4 = 3*(i : ℕ)+5 by norm_num; omega] at hr
      cases adj <;> simpa [instructionCost, instructionBody, gateBlock, adjointBlock, wrap,
        ShiBQP.encInstr, ShiBQP.encNat, checker_encode_eq, BQPGateDispatch.body,
        List.append_assoc] using hr
  | t i =>
      have hr := BQPGateDispatch.tagged_one_run adj (2 : Fin 4) i v s out
      rw [show (2 : Fin 4).val+3*(i : ℕ)+4 = 3*(i : ℕ)+6 by norm_num; omega] at hr
      cases adj <;> simpa [instructionCost, instructionBody, gateBlock, adjointBlock, wrap,
        ShiBQP.encInstr, ShiBQP.encNat, checker_encode_eq, BQPGateDispatch.body,
        List.append_assoc] using hr
  | x i =>
      have hr := BQPGateDispatch.tagged_one_run adj (3 : Fin 4) i v s out
      rw [show (3 : Fin 4).val+3*(i : ℕ)+4 = 3*(i : ℕ)+7 by norm_num; omega] at hr
      cases adj <;> simpa [instructionCost, instructionBody, gateBlock, adjointBlock, wrap,
        ShiBQP.encInstr, ShiBQP.encNat, checker_encode_eq, BQPGateDispatch.body,
        List.append_assoc] using hr
  | cnot i j hij =>
      have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      have hr := BQPGateDispatch.tagged_two_run adj i j hne v s out
      rw [cnot_rendered_eq i j hij, ← checker_encode_eq C] at hr
      cases adj <;> simpa [instructionCost, instructionBody, adjointBlock,
        ShiBQP.encInstr, ShiBQP.encNat, List.append_assoc] using hr

theorem instructionCost_le {n : ℕ} (g : Instr n) :
    instructionCost g ≤ 3*(ShiBQP.encInstr g).length := by
  cases g <;> simp only [instructionCost, ShiBQP.encInstr, ShiBQP.encNat, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil] <;> omega

end BQPProgram
