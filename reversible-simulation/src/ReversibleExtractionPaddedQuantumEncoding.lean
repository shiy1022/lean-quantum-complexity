import ReversibleExtractionQuantumEncoding
import ReversibleRawElementaryLayers

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula ShiReversible ShiReversibleGateBridge

noncomputable def extractionPaddedRawNodes (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j input stride base slotBound : Nat) : List RawAssignment :=
  (extractionFormula tm e capacity j).paddedCompile (fun i => input+stride*i.val) base slotBound

theorem extractionPaddedRawNodes_bounded (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j input stride base slotBound wires : Nat)
    (hsize : (extractionFormula tm e capacity j).size ≤ slotBound) (hout : base+slotBound+1 ≤ wires) :
    ∀ a ∈ extractionPaddedRawNodes tm e capacity j input stride base slotBound,a.target < wires := by
  intro a ha
  have ht : a.target ∈ List.range' base (slotBound+1) := by
    rw [←Formula.paddedCompile_targets (extractionFormula tm e capacity j) _ base slotBound hsize]
    exact List.mem_map.mpr ⟨a,ha,rfl⟩
  obtain ⟨i,hi,he⟩ := List.mem_range'.mp ht
  simp only [Nat.one_mul] at he
  omega

theorem extractionPaddedRawNodes_topological (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j input stride base slotBound : Nat)
    (hsize : (extractionFormula tm e capacity j).size ≤ slotBound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+stride*i.val < base) :
    ∀ a ∈ extractionPaddedRawNodes tm e capacity j input stride base slotBound,a.Topological :=
  (extractionFormula tm e capacity j).paddedCompile_topological _ base slotBound hsize hin

noncomputable def extractionPaddedQuantumLayers (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j input stride base slotBound wires : Nat)
    (hsize : (extractionFormula tm e capacity j).size ≤ slotBound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+stride*i.val < base)
    (hout : base+slotBound+1 ≤ wires) (backward : Bool) : ShiShallow.Layered wires :=
  let gates := compileAssignments (boundProgram wires (extractionPaddedRawNodes tm e capacity j input stride base slotBound)
    (extractionPaddedRawNodes_bounded tm e capacity j input stride base slotBound wires hsize hout)
    (extractionPaddedRawNodes_topological tm e capacity j input stride base slotBound hsize hin))
  substitute (if backward then gates.reverse else gates)

theorem extractionPaddedQuantumLayers_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j input stride base slotBound wires : Nat)
    (hsize : (extractionFormula tm e capacity j).size ≤ slotBound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+stride*i.val < base)
    (hout : base+slotBound+1 ≤ wires) (backward : Bool) :
    ((if backward then (extractionPaddedRawNodes tm e capacity j input stride base slotBound).reverse
      else extractionPaddedRawNodes tm e capacity j input stride base slotBound).map (rawAssignmentPayload backward)).flatten=
      ((extractionPaddedQuantumLayers tm e capacity j input stride base slotBound wires hsize hin hout backward).map ShiBQP.encLayer).flatten :=
  rawProgramPayload_substitute _ _
    (extractionPaddedRawNodes_bounded tm e capacity j input stride base slotBound wires hsize hout)
    (extractionPaddedRawNodes_topological tm e capacity j input stride base slotBound hsize hin)
    (paddedCompile_distinct_controls _ _ _ _) backward

theorem extractionPaddedQuantumLayers_length (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j input stride base slotBound wires : Nat)
    (hsize : (extractionFormula tm e capacity j).size ≤ slotBound)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+stride*i.val < base)
    (hout : base+slotBound+1 ≤ wires) (backward : Bool) :
    (extractionPaddedQuantumLayers tm e capacity j input stride base slotBound wires hsize hin hout backward).length=
      formulaElementaryLayers (extractionFormula tm e capacity j)+1 :=
  (rawProgram_substitute_length_both _
    (extractionPaddedRawNodes_bounded tm e capacity j input stride base slotBound wires hsize hout)
    (extractionPaddedRawNodes_topological tm e capacity j input stride base slotBound hsize hin)
    (paddedCompile_distinct_controls _ _ _ _) backward).trans (paddedCompile_layerCount _ _ _ _)

end ShiReversibleGenerator
