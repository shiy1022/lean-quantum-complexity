import «BQP-archive-gate»
import «BQP-counted-runs»
import «BQP-adjoint-archive»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPArchivePass
open Turing Turing.TM2 ShiShallow
abbrev LayerK := BQPCounted.Key BQPArchiveGate.K
abbrev LayerLabel := BQPCounted.Label BQPArchiveGate.Label
abbrev LayerGam : LayerK → Type := fun _ => Bool

def layerProgram : LayerLabel → Stmt LayerGam LayerLabel Bool :=
  BQPCounted.program (.inl 0 : BQPArchiveGate.K) BQPArchiveGate.program (some (.tag 0))
def layerLayout (s a : List Bool) : LayerK → List Bool := BQPCounted.extend (BQPArchiveGate.layout s a) []
def layerCost (C : BQPProgram.Checker) {n : ℕ} (gs : List (Instr n)) : ℕ :=
  (gs.map (BQPArchiveGate.cost C)).sum+2*gs.length+2
def layerEmitted (C : BQPProgram.Checker) {n : ℕ} (gs : List (Instr n)) : List Bool :=
  (gs.reverse.map (BQPArchiveGate.emitted C)).flatten

theorem layer_run (C : BQPProgram.Checker) {n : ℕ} (gs : List (Instr n))
    (v : Bool) (s a : List Bool) :
    (ShiTMSubroutine.run layerProgram)^[layerCost C gs]
      (some (⟨some none,v,layerLayout (ShiBQP.encLayer gs ++ s) a⟩ : Cfg LayerGam LayerLabel Bool)) =
    some (⟨none,false,layerLayout s (layerEmitted C gs ++ a)⟩ : Cfg LayerGam LayerLabel Bool) := by
  have hr := BQPCounted.counted_run (.inl 0 : BQPArchiveGate.K) BQPArchiveGate.program (some (.tag 0))
    BQPArchiveGate.layout BQPArchiveGate.update_input ShiBQP.encInstr (BQPArchiveGate.emitted C)
    (BQPArchiveGate.cost C) (fun g s a => BQPArchiveGate.gate_run C g true s a) gs v s a
  simpa only [layerProgram, layerLayout, layerCost, layerEmitted, BQPCounted.cfg,
    ShiBQP.encLayer, ShiBQP.encStr, ShiBQP.encNat, List.length_map,
    List.append_assoc, List.cons_append, List.nil_append] using hr

@[simp] theorem layer_update_input (s a t : List Bool) :
    Function.update (layerLayout s a) (.inl (.inl 0)) t = layerLayout t a := by
  simp only [layerLayout, BQPCounted.update_body, BQPArchiveGate.update_input]

@[simp] theorem gate_update_archive (s a t : List Bool) :
    Function.update (BQPArchiveGate.layout s a) (.inr ()) t = BQPArchiveGate.layout s t := by
  simp only [BQPArchiveGate.layout, BQPCounted.update_count]

@[simp] theorem layer_update_archive (s a t : List Bool) :
    Function.update (layerLayout s a) (.inl (.inr ())) t = layerLayout s t := by
  simp only [layerLayout, BQPCounted.update_body, gate_update_archive]

abbrev K := BQPCounted.Key LayerK
abbrev Label := BQPCounted.Label LayerLabel
abbrev Gam : K → Type := fun _ => Bool

def program : Label → Stmt Gam Label Bool :=
  BQPCounted.program (.inl (.inl 0) : LayerK) layerProgram none
def layout (s a : List Bool) : K → List Bool := BQPCounted.extend (layerLayout s a) []
def cost (C : BQPProgram.Checker) {n : ℕ} (c : Layered n) : ℕ :=
  (c.map (layerCost C)).sum+2*c.length+2
def emitted (C : BQPProgram.Checker) {n : ℕ} (c : Layered n) : List Bool :=
  (c.reverse.map (layerEmitted C)).flatten

theorem circuit_run (C : BQPProgram.Checker) {n : ℕ} (c : Layered n)
    (v : Bool) (s a : List Bool) :
    (ShiTMSubroutine.run program)^[cost C c]
      (some (⟨some none,v,layout (ShiBQP.encCirc c ++ s) a⟩ : Cfg Gam Label Bool)) =
    some (⟨none,false,layout s (emitted C c ++ a)⟩ : Cfg Gam Label Bool) := by
  have hr := BQPCounted.counted_run (.inl (.inl 0) : LayerK) layerProgram none
    layerLayout layer_update_input ShiBQP.encLayer (layerEmitted C) (layerCost C)
    (fun gs s a => layer_run C gs true s a) c v s a
  simpa only [program, layout, cost, emitted, BQPCounted.cfg,
    ShiBQP.encCirc, ShiBQP.encStr, ShiBQP.encNat, List.length_map,
    List.append_assoc, List.cons_append, List.nil_append] using hr

@[simp] theorem update_archive (s a t : List Bool) :
    Function.update (layout s a) (.inl (.inl (.inr ()))) t = layout s t := by
  simp only [layout, BQPCounted.update_body, layer_update_archive]

theorem layerEmitted_eq (C : BQPProgram.Checker) {n : ℕ} (gs : List (Instr n)) :
    layerEmitted C gs = (gs.map (fun g => C.encode (BQPProgram.adjointBlock g))).flatten.reverse := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simpa only [layerEmitted, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.reverse_append, BQPArchiveGate.emitted] using
        congrArg (fun b => b ++ (C.encode (BQPProgram.adjointBlock g)).reverse) ih

theorem emitted_eq (C : BQPProgram.Checker) {n : ℕ} (c : Layered n) :
    emitted C c = (C.encode (BQPProgram.adjointBody c.flatten)).reverse := by
  rw [BQPProgram.adjoint_encode_forward_order]
  induction c with
  | nil => rfl
  | cons l c ih =>
      simpa only [emitted, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.reverse_append, layerEmitted_eq] using
        congrArg (fun b => b ++ (l.map (fun g => C.encode (BQPProgram.adjointBlock g))).flatten.reverse) ih

/-- All gate archives in a layer fit a linear bound in its actual encoding. -/
theorem layer_cost_le (C : BQPProgram.Checker) {n : ℕ} (gs : List (Instr n)) :
    layerCost C gs ≤ 32*(ShiBQP.encLayer gs).length := by
  have hb : (gs.map (BQPArchiveGate.cost C)).sum ≤ 32*(gs.map ShiBQP.encInstr).flatten.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
        have hg := BQPArchiveGate.cost_le C g
        simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append]
        omega
  simp only [layerCost, ShiBQP.encLayer, ShiBQP.encStr, ShiBQP.encNat,
    List.length_append, List.length_map, List.length_replicate, List.length_cons, List.length_nil]
  omega

theorem cost_le (C : BQPProgram.Checker) {n : ℕ} (c : Layered n) :
    cost C c ≤ 32*(ShiBQP.encCirc c).length := by
  have hb : (c.map (layerCost C)).sum ≤ 32*(c.map ShiBQP.encLayer).flatten.length := by
    induction c with
    | nil => simp
    | cons l c ih =>
        have hl := layer_cost_le C l
        simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append]
        omega
  simp only [cost, ShiBQP.encCirc, ShiBQP.encStr, ShiBQP.encNat,
    List.length_append, List.length_map, List.length_replicate, List.length_cons, List.length_nil]
  omega

end BQPArchivePass
