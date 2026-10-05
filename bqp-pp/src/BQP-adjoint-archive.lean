import «BQP-unary-block-integration»
import «BQP-bit-transfer»

set_option autoImplicit false
namespace BQPProgram
open ShiShallow

/-- Accumulate the reverse of each emitted block on a bit archive. -/
def archive (blocks : List (List Bool)) (acc : List Bool) : List Bool :=
  blocks.foldl (fun acc block => block.reverse ++ acc) acc

theorem archive_eq (blocks : List (List Bool)) (acc : List Bool) :
    archive blocks acc = blocks.flatten.reverse ++ acc := by
  induction blocks generalizing acc with
  | nil => rfl
  | cons b blocks ih =>
      change archive blocks (b.reverse ++ acc) = _
      rw [ih]
      simp only [List.flatten_cons, List.reverse_append, List.append_assoc]

theorem encode_flatten (C : Checker) (blocks : List (List ℕ)) :
    C.encode blocks.flatten = (blocks.reverse.map C.encode).flatten := by
  have he : C.encode = BQPOpcodeEmission.encode := funext (checker_encode_eq C)
  simp only [he]
  induction blocks with
  | nil => rfl
  | cons b blocks ih =>
      simp only [List.flatten_cons, BQPOpcodeEmission.encode_append, ih,
        List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- The adjoint's desired bitstring is a concatenation in original gate order.
Consequently the compiler need not parse the circuit description backwards. -/
theorem adjoint_encode_forward_order (C : Checker) {n : ℕ} (gs : List (Instr n)) :
    C.encode (adjointBody gs) = (gs.map (fun g => C.encode (adjointBlock g))).flatten := by
  rw [adjointBody, encode_flatten]
  simp only [List.map_reverse, List.reverse_reverse, List.map_map, Function.comp_def]

/-- Building an archive in a forward pass, then draining it once, produces
exactly the existing adjoint encoding, prepended to any prior output. -/
theorem adjoint_archive_drain (C : Checker) {n : ℕ} (gs : List (Instr n)) (out : List Bool) :
    (archive (gs.map (fun g => C.encode (adjointBlock g))) []).reverse ++ out =
      C.encode (adjointBody gs) ++ out := by
  rw [archive_eq, List.append_nil, List.reverse_reverse, adjoint_encode_forward_order]

/-- The final archive drain is an actual stack-machine run with an exact clock.
A surrounding circuit loop must still build the archive via the checked gate runs. -/
theorem adjoint_archive_run (C : Checker) {n : ℕ} (gs : List (Instr n))
    (out : List Bool) (v : Option Bool) :
    (ShiTMSubroutine.run BQPBitTransfer.program)^[
        (archive (gs.map (fun g => C.encode (adjointBlock g))) []).length+1]
      (some (BQPBitTransfer.cfg v (archive (gs.map (fun g => C.encode (adjointBlock g))) []) out)) =
    some (⟨none,none,BQPBitTransfer.tapes [] (C.encode (adjointBody gs) ++ out)⟩ :
      Turing.TM2.Cfg BQPBitTransfer.Gam Unit (Option Bool)) := by
  simpa only [adjoint_archive_drain] using
    BQPBitTransfer.transfer_run (archive (gs.map (fun g => C.encode (adjointBlock g))) []) out v

end BQPProgram
