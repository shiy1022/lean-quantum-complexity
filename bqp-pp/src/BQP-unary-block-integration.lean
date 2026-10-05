import «BQP-unary-block-runs»
import «BQP-program-data»

set_option autoImplicit false
namespace BQPProgram
open Turing Turing.TM2

theorem checker_encode_eq (C : Checker) (p : List ℕ) : C.encode p = BQPOpcodeEmission.encode p := by
  induction p with
  | nil => exact C.encode_nil
  | cons c p ih => rw [C.encode_cons, ih]; rfl

/-- Concrete finite-machine execution for every fixed-body indexed gate block.
Only the unary wire index is input data; the body is fixed finite control. -/
def wrap_outputs (C : Checker) (body : List ℕ) (xs : List Bool) :
    TM2OutputsInTime (BQPUnaryBlock.machine body) xs
      (some (C.encode (wrap xs.length body))) (2*xs.length+2) := by
  rw [checker_encode_eq]
  exact BQPUnaryBlock.outputs body xs

/-- Single-wire and fixed adjoint bodies therefore admit actual linear-time
emitters; this is a compiler component, not yet the complete family compiler. -/
theorem wrap_polyTime (C : Checker) (body : List ℕ) :
    PvsNP.PolyTimeComputable (fun xs => C.encode (wrap xs.length body)) := by
  refine ⟨{ tm := BQPUnaryBlock.machine body
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
            outputsFun := ?_ }⟩
  intro xs
  simpa only [id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl, List.map_id,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using
    wrap_outputs C body xs

end BQPProgram
