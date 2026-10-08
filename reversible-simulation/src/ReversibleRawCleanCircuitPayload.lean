import ReversibleMachineBodyRawCount

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversible ShiReversibleFormula ShiReversibleGateBridge

/-- The established physical quantum circuit's exact encoding is raw compute-copy-uncompute, including the output-register flattening. -/
theorem SingleAssignmentCircuit.quantum_payload_raw {n k m : Nat} (c : SingleAssignmentCircuit n k m)
    (nodes : List RawAssignment) (ht : ∀ a ∈ nodes,a.target<n+k)
    (hp : ∀ a ∈ nodes,a.Topological) (hd : ∀ a ∈ nodes,a.DistinctControls)
    (hnodes : c.nodes=boundProgram (n+k) nodes ht hp) :
    ((substitute (c.reversible.map flatInstruction)).map ShiBQP.encLayer).flatten=
      rawNodesPayload false nodes++
        ((substitute ((copyOut c.read).map flatInstruction)).map ShiBQP.encLayer).flatten++
        rawNodesPayload true nodes := by
  unfold ShiReversible.SingleAssignmentCircuit.reversible cleanCircuit
  simp only [List.map_append,List.map_map]
  change ((substitute (((compileAssignments c.nodes).map workGate)++
    (copyOut c.read).map flatInstruction++(compileAssignments c.nodes).reverse.map workGate)).map ShiBQP.encLayer).flatten=_
  rw [substitute_append_payload,substitute_append_payload,hnodes]
  have hf := rawProgramPayload_work_substitute (m := m) nodes ht hp hd false
  have hb := rawProgramPayload_work_substitute (m := m) nodes ht hp hd true
  simpa only [rawNodesPayload,Bool.false_eq_true,if_false,if_true] using
    congrArg₂ (fun a b => a++((substitute ((copyOut c.read).map flatInstruction)).map ShiBQP.encLayer).flatten++b)
      hf.symm hb.symm

end ShiReversibleGenerator
