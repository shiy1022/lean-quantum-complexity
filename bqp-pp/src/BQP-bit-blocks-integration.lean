import «BQP-bit-blocks»
import «BQP-unary-block-integration»

set_option autoImplicit false
namespace BQPProgram
open Turing Turing.TM2

theorem render_load (s : List Bool) : BQPBitBlocks.render [1] [5,1] s = load s := by
  induction s with
  | nil => rfl
  | cons b s ih => simp only [BQPBitBlocks.render, load, ih]

theorem render_endpoint (s : List Bool) : BQPBitBlocks.render [5,8,5,1] [8,1] s = endpoint s := by
  induction s with
  | nil => rfl
  | cons b s ih => simp only [BQPBitBlocks.render, endpoint, ih]

theorem render_return (s : List Bool) : BQPBitBlocks.render [0] [0] s = List.replicate s.length 0 := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [BQPBitBlocks.render, ih, List.replicate_succ]

/-- Load the basis-state bits by a concrete linear-time opcode emitter. -/
theorem load_run (C : Checker) (s out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run (BQPBitBlocks.program [1] [5,1]))^[s.length+1]
      (some (BQPBitBlocks.cfg v s out)) =
    some (⟨none,false,BQPBitBlocks.tapes [] (C.encode (load s) ++ out)⟩ : Cfg BQPBitBlocks.Gam Unit Bool) := by
  simpa only [render_load, checker_encode_eq] using BQPBitBlocks.render_run [1] [5,1] s out v

/-- Emit the exact endpoint-cleanup code used by compile. -/
theorem endpoint_run (C : Checker) (s out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run (BQPBitBlocks.program [5,8,5,1] [8,1]))^[s.length+1]
      (some (BQPBitBlocks.cfg v s out)) =
    some (⟨none,false,BQPBitBlocks.tapes [] (C.encode (endpoint s) ++ out)⟩ : Cfg BQPBitBlocks.Gam Unit Bool) := by
  simpa only [render_endpoint, checker_encode_eq] using BQPBitBlocks.render_run [5,8,5,1] [8,1] s out v

/-- Emit one return opcode per wire marker. -/
theorem return_run (C : Checker) (s out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run (BQPBitBlocks.program [0] [0]))^[s.length+1]
      (some (BQPBitBlocks.cfg v s out)) =
    some (⟨none,false,BQPBitBlocks.tapes [] (C.encode (List.replicate s.length 0) ++ out)⟩ : Cfg BQPBitBlocks.Gam Unit Bool) := by
  simpa only [render_return, checker_encode_eq] using BQPBitBlocks.render_run [0] [0] s out v

end BQPProgram
