import ReversibleExtractionNaturalFormulaAgreement
import ReversibleNaturalTickCompilation
import ReversibleRawSubstitutionLayers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula ShiReversible ShiReversibleGateBridge

noncomputable def extractionRawNodes (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j input stride base : Nat) : List RawAssignment :=
  (extractionFormula tm e capacity j).rawCompile (fun i => input+stride*i.val) base

theorem extractionRawNodes_bounded (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j input stride base wires : Nat) (hout : base+(extractionFormula tm e capacity j).size ≤ wires) :
    ∀ a ∈ extractionRawNodes tm e capacity j input stride base,a.target < wires := by
  intro a ha
  exact ((extractionFormula tm e capacity j).rawCompile_target_interval _ base a ha).2.trans_le hout

theorem extractionRawNodes_topological (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j input stride base : Nat)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+stride*i.val < base) :
    ∀ a ∈ extractionRawNodes tm e capacity j input stride base,a.Topological :=
  (extractionFormula tm e capacity j).rawCompile_topological _ base hin

theorem extractionRawNodes_natural (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j input stride base : Nat) :
    (disjoin (extractionNaturalTermRange tm e capacity j 0 (capacity+1))).rawCompile
      (fun bit => input+stride*naturalConfigurationAddress tm capacity bit) base=
      extractionRawNodes tm e capacity j input stride base := by
  rw [extractionNaturalFormula_original,Formula.rename_rawCompile]
  simp only [naturalInputAddress_value,extractionRawNodes]

noncomputable def extractionQuantumLayers (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j input stride base wires : Nat)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+stride*i.val < base)
    (hout : base+(extractionFormula tm e capacity j).size ≤ wires) (backward : Bool) : ShiShallow.Layered wires :=
  let gates := compileAssignments (boundProgram wires (extractionRawNodes tm e capacity j input stride base)
    (extractionRawNodes_bounded tm e capacity j input stride base wires hout)
    (extractionRawNodes_topological tm e capacity j input stride base hin))
  substitute (if backward then gates.reverse else gates)

theorem extractionQuantumLayers_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j input stride base wires : Nat)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+stride*i.val < base)
    (hout : base+(extractionFormula tm e capacity j).size ≤ wires) (backward : Bool) :
    ((if backward then (extractionRawNodes tm e capacity j input stride base).reverse
      else extractionRawNodes tm e capacity j input stride base).map (rawAssignmentPayload backward)).flatten=
      ((extractionQuantumLayers tm e capacity j input stride base wires hin hout backward).map ShiBQP.encLayer).flatten :=
  rawProgramPayload_substitute _ _
    (extractionRawNodes_bounded tm e capacity j input stride base wires hout)
    (extractionRawNodes_topological tm e capacity j input stride base hin)
    (rawCompile_distinct_controls _ _ _) backward

theorem extractionQuantumLayers_length (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j input stride base wires : Nat)
    (hin : ∀ i : Fin (configurationWidth tm capacity),input+stride*i.val < base)
    (hout : base+(extractionFormula tm e capacity j).size ≤ wires) (backward : Bool) :
    (extractionQuantumLayers tm e capacity j input stride base wires hin hout backward).length=
      formulaElementaryLayers (extractionFormula tm e capacity j) :=
  (rawProgram_substitute_length_both _
    (extractionRawNodes_bounded tm e capacity j input stride base wires hout)
    (extractionRawNodes_topological tm e capacity j input stride base hin)
    (rawCompile_distinct_controls _ _ _) backward).trans (rawCompile_layerCount _ _ _)

end ShiReversibleGenerator
