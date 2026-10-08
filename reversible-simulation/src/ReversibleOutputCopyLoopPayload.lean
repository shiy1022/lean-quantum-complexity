import ReversibleOutputCopyLoop

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Established one-CNOT layer serialization, without a physical wire cast. -/
def outputCopyLayerBytes (source target : Nat) : List Bool :=
  ShiBQP.encNat 1++ShiBQP.encNat 4++ShiBQP.encNat source++ShiBQP.encNat target

/-- Output is prepended, so chronological copy bytes are assembled from the retreating pointer run. -/
def outputCopyLoopBytes (stride : Nat) : Nat → Nat → Nat → List Bool
  | 0, _, _ => []
  | k+1, source, target => outputCopyLoopBytes stride k (source-stride) (target-1)++outputCopyLayerBytes source target

theorem outputCopyStepTemplate_raw_bytes (cs : OutputCopyRegister → Nat) :
    outputCopyStepTemplate.bytes cs=outputCopyLayerBytes (cs 0) (cs 1) := by
  rw [outputCopyStepTemplate_bytes]
  simp [countedCopyProgramTemplate,cxAtoms,emissionBytes,EmissionAtom.bytes,outputCopyLayerBytes,List.append_assoc]

theorem outputCopyLoopTemplate_payload (cs : OutputCopyRegister → Nat) :
    outputCopyLoopTemplate.bytes cs=outputCopyLoopBytes (cs 5) (cs 6) (cs 0) (cs 1) := by
  suffices h : ∀ k (t : OutputCopyRegister → Nat),
      descendingTemplateBytes outputCopyStepTemplate 6 k t=outputCopyLoopBytes (t 5) k (t 0) (t 1) by
    exact h _ _
  intro k
  induction k with
  | zero => intro t; rfl
  | succ k ih =>
      intro t
      rw [descendingTemplateBytes,ih,outputCopyStepTemplate_raw_bytes,outputCopyStepTemplate_counters]
      simp [outputCopyLoopBytes]

end ShiReversibleGenerator
