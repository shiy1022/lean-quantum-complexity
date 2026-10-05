import «BQP-nested-block-runs»
import «BQP-unary-block-integration»

set_option autoImplicit false
namespace BQPProgram
open Turing Turing.TM2

/-- Forward CNOT block emission when its control index precedes its target.
The two unary counters are the wire index and the distance supplied by parsing. -/
theorem cnot_lt_emit {n : ℕ} (C : Checker) (i j : Fin n) (hij : i ≠ j)
    (hlt : (i : ℕ) < j) (out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run (BQPNestedBlock.program [6] [7] []))^[2*(j : ℕ)+4]
      (some (BQPNestedBlock.cfg 0 v (List.replicate i true)
        (List.replicate ((j : ℕ)-i) true) [] [] out)) =
    some (⟨none,false,BQPNestedBlock.tapes [] [] [] []
      (C.encode (gateBlock (.cnot i j hij)) ++ out)⟩ :
      Cfg BQPNestedBlock.Gam BQPNestedBlock.Label Bool) := by
  have h := BQPNestedBlock.block_run [6] [7] []
    (List.replicate i true) (List.replicate ((j : ℕ)-i) true) out v
  simp only [List.length_replicate] at h
  rw [show 2*(i : ℕ)+2*((j : ℕ)-i)+4 = 2*(j : ℕ)+4 by omega] at h
  simpa [checker_encode_eq, gateBlock, wrap, hlt, BQPNestedBlock.block,
    List.append_assoc, -List.replicate_append_replicate] using h

/-- Reverse-order CNOT uses the same four loops with different fixed bodies. -/
theorem cnot_gt_emit {n : ℕ} (C : Checker) (i j : Fin n) (hij : i ≠ j)
    (hgt : (j : ℕ) < i) (out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run (BQPNestedBlock.program [] [6] [7]))^[2*(i : ℕ)+4]
      (some (BQPNestedBlock.cfg 0 v (List.replicate j true)
        (List.replicate ((i : ℕ)-j) true) [] [] out)) =
    some (⟨none,false,BQPNestedBlock.tapes [] [] [] []
      (C.encode (gateBlock (.cnot i j hij)) ++ out)⟩ :
      Cfg BQPNestedBlock.Gam BQPNestedBlock.Label Bool) := by
  have h := BQPNestedBlock.block_run [] [6] [7]
    (List.replicate j true) (List.replicate ((i : ℕ)-j) true) out v
  simp only [List.length_replicate] at h
  rw [show 2*(j : ℕ)+2*((i : ℕ)-j)+4 = 2*(i : ℕ)+4 by omega] at h
  have hlt : ¬ (i : ℕ) < j := by omega
  simpa [checker_encode_eq, gateBlock, wrap, hlt, BQPNestedBlock.block,
    List.append_assoc, -List.replicate_append_replicate] using h

end BQPProgram
