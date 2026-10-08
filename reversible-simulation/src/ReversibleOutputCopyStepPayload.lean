import ReversibleOutputCopyStepCounters

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem outputCopyRetreatTemplate_bytes (cs : OutputCopyRegister → Nat) :
    outputCopyRetreatTemplate.bytes cs=[] := by
  simp only [outputCopyRetreatTemplate,sequenceProgramTemplate,decrementProgramTemplate,
    counterPairRetreatTemplate_bytes,counterAffineCopyProgramTemplate]
  rfl

/-- The silent pointer movement leaves exactly the copy layer emitted before it. -/
theorem outputCopyStepTemplate_bytes (cs : OutputCopyRegister → Nat) :
    outputCopyStepTemplate.bytes cs=(countedCopyProgramTemplate (0 : OutputCopyRegister) 1 2 3 4).bytes cs := by
  change outputCopyRetreatTemplate.bytes _++_=_
  rw [outputCopyRetreatTemplate_bytes,List.nil_append]

theorem outputCopyStepTemplate_quantum_bytes {wires : Nat} (cs : OutputCopyRegister → Nat)
    (i j : Fin wires) (hij : i ≠ j) (hi : cs 0=i.val) (hj : cs 1=j.val) :
    outputCopyStepTemplate.bytes cs=ShiBQP.encLayer [.cnot i j hij] := by
  rw [outputCopyStepTemplate_bytes]
  exact countedCopyProgramTemplate_bytes _ _ _ _ _ cs i j hij hi hj

/-- Actual cost includes CNOT printing, the counted unary stride subtraction, and target decrement. -/
theorem outputCopyStepTemplate_steps (cs : OutputCopyRegister → Nat) :
    outputCopyStepTemplate.steps cs=10*cs 0+10*cs 1+2*cs 7+11*cs 5+21 := by
  change (countedCopyProgramTemplate (0 : OutputCopyRegister) 1 2 3 4).steps cs+
    outputCopyRetreatTemplate.steps ((countedCopyProgramTemplate (0 : OutputCopyRegister) 1 2 3 4).counters cs)=_
  rw [countedCopyProgramTemplate_steps]
  simp only [outputCopyRetreatTemplate,sequenceProgramTemplate,counterPairRetreatTemplate_steps,
    decrementProgramTemplate,counterAffineCopyProgramTemplate,countedCopyProgramTemplate]
  simp
  omega

theorem outputCopyStepTemplate_polynomial (bound : Polynomial Nat) :
    outputCopyStepTemplate.PolynomiallyTimed bound := by
  refine ⟨Polynomial.C 33*bound+Polynomial.C 21,?_⟩
  intro n cs hb _
  rw [outputCopyStepTemplate_steps]
  have h0 := hb 0
  have h1 := hb 1
  have h5 := hb 5
  have h7 := hb 7
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  omega

end ShiReversibleGenerator
