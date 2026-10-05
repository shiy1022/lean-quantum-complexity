import «BQP-cnot-parser»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace BQPCnot

def rendered (i j : ℕ) : List ℕ :=
  if i < j then BQPNestedBlock.block i (j-i) [6] [7] []
  else BQPNestedBlock.block j (i-j) [] [6] [7]

/-- Exact normalization-and-rendering run, with its index-dependent linear clock. -/
theorem from_indices (i j : ℕ) (hne : i ≠ j) (v : Bool) (out : List Bool) :
    (ShiTMSubroutine.run program)^[min i j+2*max i j+6]
      (some (cfg .compare v (List.replicate i true) (List.replicate j true) [] [] [] out)) =
    some (⟨none,false,tapes [] [] [] [] [] (BQPOpcodeEmission.encode (rendered i j) ++ out)⟩ :
      Cfg Gam Label Bool) := by
  by_cases hlt : i < j
  · simpa only [rendered, if_pos hlt, Nat.min_eq_left (Nat.le_of_lt hlt),
      Nat.max_eq_right (Nat.le_of_lt hlt)] using from_indices_lt i j hlt v out
  · have hgt : j < i := by omega
    simpa only [rendered, if_neg hlt, Nat.min_eq_right (Nat.le_of_lt hgt),
      Nat.max_eq_left (Nat.le_of_lt hgt)] using from_indices_gt i j hgt v out

end BQPCnot
namespace BQPCnotParser

theorem compiler_run (i j : ℕ) (hne : i ≠ j) (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run program)^[min i j+2*max i j+6]
      (some (cfg (.compile .compare) v s (List.replicate i true) (List.replicate j true) [] [] [] out)) =
    some (⟨none,false,tapes s [] [] [] [] [] (BQPOpcodeEmission.encode (BQPCnot.rendered i j) ++ out)⟩ :
      Cfg Gam Label Bool) := by
  let c := BQPCnot.cfg .compare v (List.replicate i true) (List.replicate j true) [] [] [] out
  let d : Cfg BQPCnot.Gam BQPCnot.Label Bool :=
    ⟨none,false,BQPCnot.tapes [] [] [] [] [] (BQPOpcodeEmission.encode (BQPCnot.rendered i j) ++ out)⟩
  have hp : (ShiTMSubroutine.run BQPCnot.program)^[min i j+2*max i j+6] (some c) = some d :=
    BQPCnot.from_indices i j hne v out
  have he := (BQPStackEmbedding.run_iter compilerMap (tapes s [] [] [] [] [] [])
    BQPCnot.program (min i j+2*max i j+6) (some c)).trans
      (congrArg (Option.map (BQPStackEmbedding.cfg compilerMap (tapes s [] [] [] [] [] []))) hp)
  have hr := (ShiTMSubroutine.run_iter_lift
    (BQPStackEmbedding.machine compilerMap BQPCnot.program) program
    Label.compile (fun _ => rfl) (min i j+2*max i j+6)
    (some (BQPStackEmbedding.cfg compilerMap (tapes s [] [] [] [] [] []) c))).trans
      (congrArg (Option.map (ShiTMSubroutine.cfg Label.compile)) he)
  simpa only [Option.map_some, BQPStackEmbedding.cfg, ShiTMSubroutine.cfg, c, d,
    BQPCnot.cfg, compiler_stacks, Option.map_none, cfg] using hr

/-- A concrete compiler component for the two encoded CNOT operands. It
preserves the suffix and prior output and needs no supplied parsing result. -/
theorem parse_emit_run (i j : ℕ) (hne : i ≠ j) (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run program)^[i+j+min i j+2*max i j+8]
      (some (cfg .left v (List.replicate i true ++ false::(List.replicate j true ++ false::s))
        [] [] [] [] [] out)) =
    some (⟨none,false,tapes s [] [] [] [] [] (BQPOpcodeEmission.encode (BQPCnot.rendered i j) ++ out)⟩ :
      Cfg Gam Label Bool) := by
  rw [show i+j+min i j+2*max i j+8 = (min i j+2*max i j+6)+(i+j+2) by omega,
    Function.iterate_add_apply, parse_pair]
  exact compiler_run i j hne false s out

theorem parse_emit_cost_le (i j : ℕ) :
    i+j+min i j+2*max i j+8 ≤ 3*(i+j)+8 := by omega

end BQPCnotParser
