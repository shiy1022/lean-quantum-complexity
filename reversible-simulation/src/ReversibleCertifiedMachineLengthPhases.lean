import ReversibleCertifiedLengthPhase
import ReversibleExtractionRawLengthPhase
import ReversibleOutputCopyRawLengthPhase
import ReversibleInitializerRawLengthPhase
import ReversibleTickRawLengthPhase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula
variable {R : Type} [DecidableEq R]

noncomputable def certifiedLengthPhaseOf (p : CounterProgramTemplate (RawLengthPhaseRegister R))
    (payload : Nat → List Bool) (layers : Nat → Nat) (he : p.Embeds) (hr : p.Runs)
    (hready : ∀ cs,cs (.inl 2)=0 → p.ready cs) (hb : ∀ cs,p.bytes cs=payload (cs (.inl 0)))
    (hc : ∀ cs,p.counters cs (.inl 1)=cs (.inl 1)+layers (cs (.inl 0)))
    (hn : ∀ cs,p.counters cs (.inl 0)=cs (.inl 0)) (hs : ∀ cs,p.counters cs (.inl 2)=cs (.inl 2))
    (hz : ∀ cs r,p.counters cs (.inr r)=0)
    (hresources : ∀ bound : Polynomial Nat,p.CounterBound bound ∧ p.PolynomiallyTimed bound) : CertifiedLengthPhase R where
  program := p
  payload := payload
  layers := layers
  embeds := he
  runs := hr
  ready := hready
  bytes := hb
  total := hc
  length := hn
  scratch := hs
  privateZero := fun cs _ r => hz cs r
  resources := hresources

theorem extractionCertifiedLengthPhase_exists (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (c d : Nat) :
    ∃ a : CertifiedLengthPhase ExtractionMasterRegister,
      a.payload=(fun n => extractionResourcePayload tm e backward n ((n+c)^d)) ∧
      a.layers=(fun n => ((extractionForest tm e (n+(n+c)^d*machinePushBound tm+1)).map
        (fun p => formulaElementaryLayers p+1)).sum) := by
  obtain ⟨p,he,hr,hready,hb,hc,hn,hs,hz,hresources⟩ := extractionRawLengthPhase_exists tm e backward c d
  exact ⟨certifiedLengthPhaseOf p _ _ he hr hready hb hc hn hs hz hresources,rfl,rfl⟩

theorem outputCopyCertifiedLengthPhase_exists (tm : Turing.FinTM2) (c d : Nat) :
    ∃ a : CertifiedLengthPhase OutputCopyMasterRegister,
      a.payload=(fun n => outputCopyResourcePayload tm n ((n+c)^d)) ∧
      a.layers=(fun n => 2*(n+(n+c)^d*machinePushBound tm+1)+1) := by
  obtain ⟨p,he,hr,hready,hb,hc,hn,hs,hz,hresources⟩ := outputCopyRawLengthPhase_exists tm c d
  exact ⟨certifiedLengthPhaseOf p _ _ he hr hready hb hc hn hs hz hresources,rfl,rfl⟩

theorem initializerCertifiedLengthPhase_exists (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (c d : Nat) :
    ∃ a : CertifiedLengthPhase InitializationRegister,
      a.payload=(fun n => initializerResourcePayload tm e backward c d n) ∧
      a.layers=(fun n => initializationForestLayerCount tm e
        ((initializationCapacityPolynomial tm ((Polynomial.X+Polynomial.C c)^d)).eval n) n) := by
  obtain ⟨p,he,hr,hready,hb,hc,hn,hs,hz,hresources⟩ := initializerRawLengthPhase_exists tm e backward c d
  exact ⟨certifiedLengthPhaseOf p _ _ he hr hready hb hc hn hs hz hresources,rfl,rfl⟩

theorem tickCertifiedLengthPhase_exists (tm : Turing.FinTM2) (backward : Bool) (c d : Nat) (hpos : 0 < c) :
    ∃ a : CertifiedLengthPhase (FixedLeafRegister (tickTraversalSupply tm)),
      a.payload=(fun n => tickResourcePayload tm backward ((Polynomial.X+Polynomial.C c)^d) n) ∧
      a.layers=(fun n => (n+c)^d*tickForestLayerCount tm (n+(n+c)^d*machinePushBound tm+1)) := by
  obtain ⟨p,he,hr,hready,hb,hc,hn,hs,hz,hresources⟩ := tickRawLengthPhase_exists tm backward c d hpos
  exact ⟨certifiedLengthPhaseOf p _ _ he hr hready hb hc hn hs hz hresources,rfl,rfl⟩

end ShiReversibleGenerator
