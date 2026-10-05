import «BQP-circuit-pass»
import «BQP-adjoint-pass»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPCircuitPass
open Turing Turing.TM2 ShiShallow

abbrev machine : FinTM2 where
  K := K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := .inl (.inl 0)
  k₁ := .inl (.inl 6)
  Γ := Gam
  Λ := Label
  main := none
  ΛFin := inferInstance
  σ := Bool
  initialState := false
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := program false

theorem initial_eq (s : List Bool) :
    initList machine s = (⟨some none,false,layout s []⟩ : Cfg Gam Label Bool) := by
  apply congrArg (fun S => (⟨some none,false,S⟩ : Cfg Gam Label Bool))
  funext k
  change K at k
  fin_cases k <;> simp [initList, machine, layout, BQPLayer.layout, BQPCounted.extend,
    BQPGateDispatch.inputStacks, BQPCnotParser.tapes] <;> rfl

theorem final_eq (out : List Bool) :
    (⟨none,false,layout [] out⟩ : Cfg Gam Label Bool) = haltList machine out := by
  apply congrArg (fun S => (⟨none,false,S⟩ : Cfg Gam Label Bool))
  funext k
  change K at k
  fin_cases k <;> simp [haltList, machine, layout, BQPLayer.layout, BQPCounted.extend,
    BQPGateDispatch.inputStacks, BQPCnotParser.tapes] <;> rfl

set_option backward.isDefEq.respectTransparency false in
def outputs (C : BQPProgram.Checker) {n : ℕ} (c : Layered n) :
    TM2OutputsInTime machine (ShiBQP.encCirc c)
      (some (C.encode (BQPProgram.forwardBody c.flatten))) (cost c) := by
  refine { steps := cost c, steps_le_m := le_refl _, evals_in_steps := ?_ }
  change (ShiTMSubroutine.run (program false))^[cost c]
    (some (initList machine (ShiBQP.encCirc c))) =
      some (haltList machine (C.encode (BQPProgram.forwardBody c.flatten)))
  rw [initial_eq, ← final_eq]
  simpa only [List.append_nil, emitted_forward] using circuit_run C false c false [] []

/-- The original circuit encoding admits a concrete polynomial-time forward
compiler pass. This does not yet assemble the complete doubled program. -/
theorem forward_polyTime (C : BQPProgram.Checker) (n : ℕ) :
    Nonempty (TM2ComputableInPolyTime (@ShiBQP.encCirc n) id
      (fun c => C.encode (BQPProgram.forwardBody c.flatten))) := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.C 3 * Polynomial.X
            outputsFun := ?_ }⟩
  intro c
  have h := outputs C c
  have ho : TM2OutputsInTime machine (ShiBQP.encCirc c)
      (some (C.encode (BQPProgram.forwardBody c.flatten))) (3*(ShiBQP.encCirc c).length) :=
    { h with steps_le_m := h.steps_le_m.trans (cost_le c) }
  simpa only [id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl, List.map_id,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using ho
end BQPCircuitPass

namespace BQPAdjointPass
open Turing Turing.TM2 ShiShallow
abbrev machine : FinTM2 where
  K := K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := .inl (.inl (.inl (.inl 0)))
  k₁ := .inr ()
  Γ := Gam
  Λ := Label
  main := some none
  ΛFin := inferInstance
  σ := Bool
  initialState := false
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := program

theorem initial_eq (s : List Bool) :
    initList machine s = (⟨some (some none),false,layout s []⟩ : Cfg Gam Label Bool) := by
  apply congrArg (fun S => (⟨some (some none),false,S⟩ : Cfg Gam Label Bool))
  funext k
  change K at k
  fin_cases k <;> simp [initList, machine, layout, BQPArchivePass.layout,
    BQPArchivePass.layerLayout, BQPArchiveGate.layout, BQPCounted.extend,
    BQPGateDispatch.inputStacks, BQPCnotParser.tapes] <;> rfl

theorem final_eq (out : List Bool) :
    (⟨none,false,layout [] out⟩ : Cfg Gam Label Bool) = haltList machine out := by
  apply congrArg (fun S => (⟨none,false,S⟩ : Cfg Gam Label Bool))
  funext k
  change K at k
  fin_cases k <;> simp [haltList, machine, layout, BQPArchivePass.layout,
    BQPArchivePass.layerLayout, BQPArchiveGate.layout, BQPCounted.extend,
    BQPGateDispatch.inputStacks, BQPCnotParser.tapes] <;> rfl

set_option backward.isDefEq.respectTransparency false in
def outputs (C : BQPProgram.Checker) {n : ℕ} (c : Layered n) :
    TM2OutputsInTime machine (ShiBQP.encCirc c)
      (some (C.encode (BQPProgram.adjointBody c.flatten))) (cost C c) := by
  refine { steps := cost C c, steps_le_m := le_refl _, evals_in_steps := ?_ }
  change (ShiTMSubroutine.run program)^[cost C c]
    (some (initList machine (ShiBQP.encCirc c))) =
      some (haltList machine (C.encode (BQPProgram.adjointBody c.flatten)))
  rw [initial_eq, ← final_eq]
  simpa only [List.append_nil] using adjoint_run C c false [] []

/-- A concrete polynomial-time adjoint compiler pass, including gate-order
reversal, derived from finite-machine runs on the original circuit encoding. -/
theorem adjoint_polyTime (C : BQPProgram.Checker) (n : ℕ) :
    Nonempty (TM2ComputableInPolyTime (@ShiBQP.encCirc n) id
      (fun c => C.encode (BQPProgram.adjointBody c.flatten))) := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.C 64 * Polynomial.X + Polynomial.C 1
            outputsFun := ?_ }⟩
  intro c
  have h := outputs C c
  have ho : TM2OutputsInTime machine (ShiBQP.encCirc c)
      (some (C.encode (BQPProgram.adjointBody c.flatten))) (64*(ShiBQP.encCirc c).length+1) :=
    { h with steps_le_m := h.steps_le_m.trans (cost_le C c) }
  simpa only [id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl, List.map_id,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using ho
end BQPAdjointPass
