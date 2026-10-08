import ReversibleRawCleanCircuitPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversible ShiReversibleFormula ShiReversibleGateBridge

/-- Exact elementary-layer count of the semantic clean circuit, including physical work-wire embedding and one CNOT per output. -/
theorem SingleAssignmentCircuit.quantum_layers_raw {n k m : Nat} (c : SingleAssignmentCircuit n k m)
    (nodes : List RawAssignment) (ht : ∀ a ∈ nodes,a.target<n+k)
    (hp : ∀ a ∈ nodes,a.Topological) (hd : ∀ a ∈ nodes,a.DistinctControls)
    (hnodes : c.nodes=boundProgram (n+k) nodes ht hp) :
    (substitute (c.reversible.map flatInstruction)).length=2*(nodes.map rawAssignmentLayerCount).sum+m := by
  have hf := rawProgram_substitute_length nodes
    (fun a ha => (ht a ha).trans_le (Nat.le_add_right (n+k) m)) hp hd
  rw [rawProgram_compile_workGate] at hf
  have hb : (substitute ((compileAssignments (boundProgram (n+k) nodes ht hp)).reverse.map
      (workGate (m := m)))).length=(nodes.map rawAssignmentLayerCount).sum := by
    rw [List.map_reverse,substitute_reverse_length]
    exact hf
  have hcopy : (substitute ((copyOut c.read).map flatInstruction)).length=m := by
    rw [substitute_flat_copyOut,List.length_map,List.length_finRange]
  have hs : ∀ (xs ys : List (Gate (n+k+m))),substitute (xs++ys)=substitute xs++substitute ys := by
    intro xs ys
    simp only [substitute,List.flatMap_append]
  unfold ShiReversible.SingleAssignmentCircuit.reversible cleanCircuit
  simp only [List.map_append,List.map_map]
  change (substitute (((compileAssignments c.nodes).map workGate)++
    (copyOut c.read).map flatInstruction++(compileAssignments c.nodes).reverse.map workGate)).length=_
  rw [hs,hs,List.length_append,List.length_append,hnodes,hf,hcopy,hb]
  omega

end ShiReversibleGenerator
