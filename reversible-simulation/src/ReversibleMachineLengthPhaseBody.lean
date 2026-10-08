import ReversibleCertifiedMachineLengthPhases
import ReversibleCertifiedLengthPhaseBody

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

abbrev MachineLengthPhasePrivate (tm : Turing.FinTM2) := InitializationRegister ⊕
  (FixedLeafRegister (tickTraversalSupply tm) ⊕ (ExtractionMasterRegister ⊕ OutputCopyMasterRegister))

noncomputable def machineLengthPhaseBodyPayload (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d n : Nat) : List Bool :=
  initializerResourcePayload tm e₀ false c d n++
  tickResourcePayload tm false ((Polynomial.X+Polynomial.C c)^d) n++
  extractionResourcePayload tm e₁ false n ((n+c)^d)++outputCopyResourcePayload tm n ((n+c)^d)++
  extractionResourcePayload tm e₁ true n ((n+c)^d)++
  tickResourcePayload tm true ((Polynomial.X+Polynomial.C c)^d) n++initializerResourcePayload tm e₀ true c d n

noncomputable def machineLengthPhaseBodyLayers (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d n : Nat) : Nat :=
  2*initializationForestLayerCount tm e₀
    ((initializationCapacityPolynomial tm ((Polynomial.X+Polynomial.C c)^d)).eval n) n+
  2*((n+c)^d*tickForestLayerCount tm (n+(n+c)^d*machinePushBound tm+1))+
  2*((extractionForest tm e₁ (n+(n+c)^d*machinePushBound tm+1)).map (fun p => formulaElementaryLayers p+1)).sum+
  (2*(n+(n+c)^d*machinePushBound tm+1)+1)

/-- One actual fixed finite seven-phase body has exact original bytes/counts, polynomial resources, and a clean private register file. -/
theorem machineLengthPhaseBody_exists (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d : Nat) (hpos : 0 < c) :
    ∃ p : CounterProgramTemplate (RawLengthPhaseRegister (MachineLengthPhasePrivate tm)),
      p.Embeds ∧ p.Runs ∧
      (∀ cs,cs (.inl 2)=0 → p.ready cs) ∧
      (∀ cs,p.bytes cs=machineLengthPhaseBodyPayload tm e₀ e₁ c d (cs (.inl 0))) ∧
      (∀ cs,p.counters cs (.inl 1)=cs (.inl 1)+machineLengthPhaseBodyLayers tm e₀ e₁ c d (cs (.inl 0))) ∧
      (∀ cs,p.counters cs (.inl 0)=cs (.inl 0)) ∧
      (∀ cs,p.counters cs (.inl 2)=cs (.inl 2)) ∧
      (∀ cs,(∀ r,cs (.inr r)=0) → ∀ r,p.counters cs (.inr r)=0) ∧
      (∀ bound : Polynomial Nat,p.CounterBound bound ∧ p.PolynomiallyTimed bound) := by
  classical
  obtain ⟨ifwd,hifp,hifl⟩ := initializerCertifiedLengthPhase_exists tm e₀ false c d
  obtain ⟨iinv,hiip,hiil⟩ := initializerCertifiedLengthPhase_exists tm e₀ true c d
  obtain ⟨hfwd,hhfp,hhfl⟩ := tickCertifiedLengthPhase_exists tm false c d hpos
  obtain ⟨hinv,hhip,hhil⟩ := tickCertifiedLengthPhase_exists tm true c d hpos
  obtain ⟨efwd,hefp,hefl⟩ := extractionCertifiedLengthPhase_exists tm e₁ false c d
  obtain ⟨einv,heip,heil⟩ := extractionCertifiedLengthPhase_exists tm e₁ true c d
  obtain ⟨copy,hcp,hcl⟩ := outputCopyCertifiedLengthPhase_exists tm c d
  let fi : InitializationRegister → MachineLengthPhasePrivate tm := Sum.inl
  let fh : FixedLeafRegister (tickTraversalSupply tm) → MachineLengthPhasePrivate tm := fun r => .inr (.inl r)
  let fe : ExtractionMasterRegister → MachineLengthPhasePrivate tm := fun r => .inr (.inr (.inl r))
  let fc : OutputCopyMasterRegister → MachineLengthPhasePrivate tm := fun r => .inr (.inr (.inr r))
  have hfi : Function.Injective fi := by intro a b h; exact Sum.inl.inj h
  have hfh : Function.Injective fh := by intro a b h; exact Sum.inl.inj (Sum.inr.inj h)
  have hfe : Function.Injective fe := by intro a b h; exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h))
  have hfc : Function.Injective fc := by intro a b h; exact Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h))
  let schedule : List (CertifiedLengthPhase (MachineLengthPhasePrivate tm)) :=
    [iinv.lift fi hfi,hinv.lift fh hfh,einv.lift fe hfe,copy.lift fc hfc,
      efwd.lift fe hfe,hfwd.lift fh hfh,ifwd.lift fi hfi]
  have hbytes : ∀ n,lengthPhaseBodyPayload schedule n=machineLengthPhaseBodyPayload tm e₀ e₁ c d n := by
    intro n
    simp [schedule,lengthPhaseBodyPayload,CertifiedLengthPhase.lift,hifp,hiip,hhfp,hhip,hefp,heip,hcp,
      machineLengthPhaseBodyPayload,List.append_assoc]
  have hlayers : ∀ n,lengthPhaseBodyLayers schedule n=machineLengthPhaseBodyLayers tm e₀ e₁ c d n := by
    intro n
    simp only [schedule,lengthPhaseBodyLayers,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      CertifiedLengthPhase.lift,hifl,hiil,hhfl,hhil,hefl,heil,hcl]
    try dsimp only
    unfold machineLengthPhaseBodyLayers
    ring
  refine ⟨lengthPhaseBodyTemplate schedule,lengthPhaseBodyTemplate_embeds _,lengthPhaseBodyTemplate_run _,
    lengthPhaseBodyTemplate_ready _,?_,?_,?_,?_,lengthPhaseBodyTemplate_private_zero _,lengthPhaseBodyTemplate_resources _⟩
  · intro cs
    exact (lengthPhaseBodyTemplate_bytes schedule cs).trans (hbytes _)
  · intro cs
    exact (lengthPhaseBodyTemplate_layers schedule cs).trans (congrArg (fun k => cs (.inl 1)+k) (hlayers _))
  · intro cs
    exact (lengthPhaseBodyTemplate_shared schedule cs).1
  · intro cs
    exact (lengthPhaseBodyTemplate_shared schedule cs).2

end ShiReversibleGenerator
