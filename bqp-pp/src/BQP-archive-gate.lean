import «BQP-archive-machine»
import «BQP-gate-machine-integration»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPArchiveGate
open Turing Turing.TM2 ShiShallow
abbrev K := BQPCounted.Key BQPGateDispatch.K
abbrev Label := BQPArchive.Label BQPGateDispatch.Label
abbrev Gam : K → Type := fun _ => Bool

def program : Label → Stmt Gam Label Bool := BQPArchive.program (6 : BQPGateDispatch.K) (BQPGateDispatch.program true)
def layout (s a : List Bool) : K → List Bool := BQPCounted.extend (BQPGateDispatch.inputStacks s []) a

def emitted (C : BQPProgram.Checker) {n : ℕ} (g : Instr n) : List Bool :=
  (C.encode (BQPProgram.adjointBlock g)).reverse

def cost (C : BQPProgram.Checker) {n : ℕ} (g : Instr n) : ℕ :=
  BQPProgram.instructionCost g + (emitted C g).length + 1

@[simp] theorem update_output (s out r : List Bool) :
    Function.update (BQPGateDispatch.inputStacks s out) 6 r = BQPGateDispatch.inputStacks s r := by
  funext k; fin_cases k <;> simp [BQPGateDispatch.inputStacks, BQPCnotParser.tapes, Function.update]

@[simp] theorem update_input (s a t : List Bool) :
    Function.update (layout s a) (.inl 0) t = layout t a := by
  simp only [layout, BQPCounted.update_body, BQPGateDispatch.update_input]

/-- Decode one original instruction, render its adjoint block, and archive it.
The body correctness premise of the generic archive is discharged here. -/
theorem gate_run (C : BQPProgram.Checker) {n : ℕ} (g : Instr n)
    (v : Bool) (s a : List Bool) :
    (ShiTMSubroutine.run program)^[cost C g]
      (some (⟨some (some (.tag 0)),v,layout (ShiBQP.encInstr g ++ s) a⟩ : Cfg Gam Label Bool)) =
    some (⟨none,false,layout s (emitted C g ++ a)⟩ : Cfg Gam Label Bool) := by
  have hg := BQPProgram.instruction_run C true g v s []
  simp only [BQPProgram.instructionBody, if_true, List.append_nil] at hg
  have hr := BQPArchive.body_archive_run (6 : BQPGateDispatch.K) (BQPGateDispatch.program true)
    (.tag 0) (BQPProgram.instructionCost g) v false
    (BQPGateDispatch.inputStacks (ShiBQP.encInstr g ++ s) [])
    (BQPGateDispatch.inputStacks s []) a (C.encode (BQPProgram.adjointBlock g))
    (by simpa only [update_output, BQPGateDispatch.cfg] using hg)
  simpa only [program, cost, emitted, List.length_reverse, BQPArchive.cfg, layout, update_output] using hr

theorem emitted_length_le (C : BQPProgram.Checker) {n : ℕ} (g : Instr n) :
    (emitted C g).length ≤ 28*(ShiBQP.encInstr g).length := by
  rw [emitted, List.length_reverse, C.encode_length]
  cases g <;> simp only [BQPProgram.adjointBlock, BQPProgram.gateBlock, BQPProgram.wrap,
    ShiBQP.encInstr, ShiBQP.encNat, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  all_goals first | omega | (split <;> simp only [List.length_append, List.length_replicate,
    List.length_cons, List.length_nil] <;> omega)

theorem cost_le (C : BQPProgram.Checker) {n : ℕ} (g : Instr n) :
    cost C g ≤ 32*(ShiBQP.encInstr g).length := by
  have hc := BQPProgram.instructionCost_le g
  have he := emitted_length_le C g
  have hp : 0 < (ShiBQP.encInstr g).length := by
    cases g <;> simp [ShiBQP.encInstr, ShiBQP.encNat]
  dsimp only [cost]
  omega

end BQPArchiveGate
