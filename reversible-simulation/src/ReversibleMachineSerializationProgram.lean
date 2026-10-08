import ReversibleMachineLengthPhaseBody
import ReversibleResourceHeaderProgram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace ShiReversibleGenerator
open ShiReversibleTM

noncomputable def machineLengthSerialization (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d n : Nat) : List Bool :=
  ShiBQP.encNat (paddedMachineWorkspace tm n ((n+c)^d)+(2*(n+(n+c)^d*machinePushBound tm+1)+1)-1)++
  ShiBQP.encNat (n+paddedMachineWorkspace tm n ((n+c)^d))++
  ShiBQP.encNat (machineLengthPhaseBodyLayers tm e₀ e₁ c d n)++
  machineLengthPhaseBodyPayload tm e₀ e₁ c d n

/-- The checked seven-phase body followed by the actual layout/depth header is one finite polynomial-resource program. -/
theorem machineSerializationProgramTemplate_exists (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d : Nat) (hc : 0<c) :
    ∃ p : CounterProgramTemplate (RawLengthPhaseRegister (MachineLengthPhasePrivate tm)),
      p.Embeds ∧ p.Runs ∧
      (∀ cs,cs (.inl 2)=0 → p.ready cs) ∧
      (∀ cs,cs (.inl 1)=0 → p.bytes cs=machineLengthSerialization tm e₀ e₁ c d (cs (.inl 0))) ∧
      (∀ bound : Polynomial Nat,p.CounterBound bound ∧ p.PolynomiallyTimed bound) := by
  classical
  obtain ⟨b,hbe,hbr,hbready,hbbytes,hbtotal,hbn,hbs,hbz,hbresources⟩ :=
    machineLengthPhaseBody_exists tm e₀ e₁ c d hc
  obtain ⟨h,hhe,hhr,hhready,hhbytes,hhshared,hhresources⟩ := resourceHeaderProgramTemplate_exists tm c d
  let f : WorkspaceRegister → MachineLengthPhasePrivate tm := fun r => .inl (.inl r)
  have hf : Function.Injective f := by intro a b h; exact Sum.inl.inj (Sum.inl.inj h)
  let header := sharedPhaseLift h f
  let p := sequenceProgramTemplate b header
  have he : header.Embeds := sharedPhaseLift_embeds _ _
  have hr : header.Runs := sharedPhaseLift_run _ _ hf hhe hhr
  refine ⟨p,sequenceProgramTemplate_embeds _ _ hbe he,sequenceProgramTemplate_run _ _ hbe hbr hr,?_,?_,?_⟩
  · intro cs hs
    refine ⟨hbready cs hs,?_⟩
    apply sharedPhaseLift_ready _ _ hhready
    rw [hbs,hs]
  · intro cs ht
    change header.bytes (b.counters cs)++b.bytes cs=_
    change h.bytes (fun r => b.counters cs (sharedPhaseRegisterMap f r))++b.bytes cs=_
    rw [hhbytes]
    simp only [sharedPhaseRegisterMap,hbn,hbtotal,hbbytes,ht,Nat.zero_add]
    simp only [machineLengthSerialization,List.append_assoc]
  · intro bound
    obtain ⟨after,ha⟩ := (hbresources bound).1
    have hhr' := sharedPhaseLift_resources h f hf after (hhresources after).1 (hhresources after).2
    obtain ⟨final,hf'⟩ := hhr'.1
    refine ⟨⟨final,?_⟩,sequenceProgramTemplate_polynomial _ _ bound after (hbresources bound).2
      (fun n cs hn _ => ha n cs hn) hhr'.2⟩
    intro n cs hn r
    exact hf' n (b.counters cs) (ha n cs hn) r

end ShiReversibleGenerator
