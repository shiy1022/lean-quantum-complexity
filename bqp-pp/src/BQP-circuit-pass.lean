import «BQP-layer-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPCircuitPass
open Turing Turing.TM2 ShiShallow
abbrev K := BQPCounted.Key BQPLayer.K
abbrev Label := BQPCounted.Label BQPLayer.Label
abbrev Gam : K → Type := fun _ => Bool

def program (adj : Bool) : Label → Stmt Gam Label Bool :=
  BQPCounted.program (.inl 0 : BQPLayer.K) (BQPLayer.program adj) none

def layout (s out : List Bool) : K → List Bool := BQPCounted.extend (BQPLayer.layout s out) []

def cost {n : ℕ} (c : Layered n) : ℕ := (c.map BQPLayer.cost).sum+2*c.length+2

def emitted {n : ℕ} (adj : Bool) (c : Layered n) : List ℕ :=
  (c.map (BQPLayer.emitted adj)).flatten

/-- A concrete complete pass over the original nested circuit encoding.
For adj=true this substitutes adjoint gate bodies in source order; reversing
the gate order still requires the separate archive construction. -/
theorem circuit_run {n : ℕ} (C : BQPProgram.Checker) (adj : Bool) (c : Layered n)
    (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run (program adj))^[cost c]
      (some (⟨some none,v,layout (ShiBQP.encCirc c ++ s) out⟩ : Cfg Gam Label Bool)) =
    some (⟨none,false,layout s (C.encode (emitted adj c) ++ out)⟩ : Cfg Gam Label Bool) := by
  have hr := BQPCounted.counted_run (.inl 0 : BQPLayer.K) (BQPLayer.program adj) none
    BQPLayer.layout BQPLayer.update_input ShiBQP.encLayer
    (fun gs => C.encode (BQPLayer.emitted adj gs)) BQPLayer.cost
    (fun gs s out => BQPLayer.layer_run C adj gs true s out) c v s out
  have hout : C.encode (emitted adj c) =
      (c.reverse.map (fun gs => C.encode (BQPLayer.emitted adj gs))).flatten := by
    rw [emitted, BQPProgram.encode_flatten]
    simp only [List.map_reverse, List.reverse_reverse, List.map_map, Function.comp_def]
  rw [hout]
  simpa only [program, layout, cost, BQPCounted.cfg, ShiBQP.encCirc, ShiBQP.encStr,
    ShiBQP.encNat, List.length_map, List.append_assoc, List.cons_append, List.nil_append] using hr

theorem body_cost_le {n : ℕ} (c : Layered n) :
    (c.map BQPLayer.cost).sum ≤ 3*(c.map ShiBQP.encLayer).flatten.length := by
  induction c with
  | nil => simp
  | cons l c ih =>
      have hl := BQPLayer.cost_le l
      simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append]
      omega

theorem cost_le {n : ℕ} (c : Layered n) : cost c ≤ 3*(ShiBQP.encCirc c).length := by
  have h := body_cost_le c
  simp only [cost, ShiBQP.encCirc, ShiBQP.encStr, ShiBQP.encNat,
    List.length_append, List.length_map, List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- The forward pass agrees with the original compiler's forwardBody. -/
theorem emitted_forward {n : ℕ} (c : Layered n) : emitted false c = BQPProgram.forwardBody c.flatten := by
  have he : ∀ gs : List (Instr n), BQPLayer.emitted false gs = BQPProgram.forwardBody gs := by
    intro gs
    rfl
  induction c with
  | nil => rfl
  | cons l c ih =>
      change BQPLayer.emitted false l ++ emitted false c = BQPProgram.forwardBody (l ++ c.flatten)
      rw [he, ih]
      simp only [BQPProgram.forwardBody, List.map_append, List.flatten_append]

end BQPCircuitPass
