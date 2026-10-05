import «BQP-counted-runs»
import «BQP-gate-machine-integration»
import «BQP-adjoint-archive»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPLayer
open Turing Turing.TM2 ShiShallow
abbrev K := BQPCounted.Key BQPGateDispatch.K
abbrev Label := BQPCounted.Label BQPGateDispatch.Label
abbrev Gam : K → Type := fun _ => Bool

def program (adj : Bool) : Label → Stmt Gam Label Bool :=
  BQPCounted.program (0 : BQPGateDispatch.K) (BQPGateDispatch.program adj) (.tag 0)

def layout (s out : List Bool) : K → List Bool := BQPCounted.extend (BQPGateDispatch.inputStacks s out) []

def cost {n : ℕ} (gs : List (Instr n)) : ℕ := (gs.map BQPProgram.instructionCost).sum+2*gs.length+2

def emitted {n : ℕ} (adj : Bool) (gs : List (Instr n)) : List ℕ :=
  (gs.map (BQPProgram.instructionBody adj)).flatten

/-- A complete layer is read from its original length-prefixed encoding and
rendered by a concrete counter-driven machine. -/
theorem layer_run {n : ℕ} (C : BQPProgram.Checker) (adj : Bool) (gs : List (Instr n))
    (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run (program adj))^[cost gs]
      (some (⟨some none,v,layout (ShiBQP.encLayer gs ++ s) out⟩ : Cfg Gam Label Bool)) =
    some (⟨none,false,layout s (C.encode (emitted adj gs) ++ out)⟩ : Cfg Gam Label Bool) := by
  have hr := BQPCounted.counted_run (0 : BQPGateDispatch.K) (BQPGateDispatch.program adj) (.tag 0)
    BQPGateDispatch.inputStacks BQPGateDispatch.update_input
    ShiBQP.encInstr (fun g => C.encode (BQPProgram.instructionBody adj g)) BQPProgram.instructionCost
    (fun g s out => BQPProgram.instruction_run C adj g true s out) gs v s out
  have hout : C.encode (emitted adj gs) =
      (gs.reverse.map (fun g => C.encode (BQPProgram.instructionBody adj g))).flatten := by
    rw [emitted, BQPProgram.encode_flatten]
    simp only [List.map_reverse, List.reverse_reverse, List.map_map, Function.comp_def]
  rw [hout]
  simpa only [program, layout, cost, BQPCounted.cfg, ShiBQP.encLayer, ShiBQP.encStr,
    ShiBQP.encNat, List.length_map, List.append_assoc, List.cons_append, List.nil_append] using hr

@[simp] theorem update_input (s out t : List Bool) :
    Function.update (layout s out) (.inl 0) t = layout t out := by
  simp only [layout, BQPCounted.update_body, BQPGateDispatch.update_input]

theorem body_cost_le {n : ℕ} (gs : List (Instr n)) :
    (gs.map BQPProgram.instructionCost).sum ≤ 3*(gs.map ShiBQP.encInstr).flatten.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      have hg := BQPProgram.instructionCost_le g
      simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append]
      omega

theorem cost_le {n : ℕ} (gs : List (Instr n)) : cost gs ≤ 3*(ShiBQP.encLayer gs).length := by
  have h := body_cost_le gs
  simp only [cost, ShiBQP.encLayer, ShiBQP.encStr, ShiBQP.encNat,
    List.length_append, List.length_map, List.length_replicate, List.length_cons, List.length_nil]
  omega

end BQPLayer
