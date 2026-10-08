import ReversibleResourceHeaderEmission

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- An actual finite header generator computes its layout from raw length and uses the body's actual accumulated depth. -/
theorem resourceHeaderProgramTemplate_exists (tm : Turing.FinTM2) (c d : Nat) :
    ∃ p : CounterProgramTemplate ResourceHeaderRegister,
      p.Embeds ∧ p.Runs ∧
      (∀ cs,cs (.inl 2)=0 → p.ready cs) ∧
      (∀ cs,p.bytes cs=
        ShiBQP.encNat (paddedMachineWorkspace tm (cs (.inl 0)) ((cs (.inl 0)+c)^d)+
          (2*(cs (.inl 0)+((cs (.inl 0)+c)^d)*machinePushBound tm+1)+1)-1)++
        ShiBQP.encNat (cs (.inl 0)+paddedMachineWorkspace tm (cs (.inl 0)) ((cs (.inl 0)+c)^d))++
        ShiBQP.encNat (cs (.inl 1))) ∧
      (∀ cs j,p.counters cs (.inl j)=cs (.inl j)) ∧
      (∀ bound : Polynomial Nat,p.CounterBound bound ∧ p.PolynomiallyTimed bound) := by
  obtain ⟨q,he,hr,hready,hbytes,hprivate,hshared,hresources⟩ := resourceHeaderPreludeTemplate_exists tm c d
  let ps := [q,resourceHeaderAdministrationTemplate,resourceHeaderEmissionTemplate]
  let p := listProgramTemplate ps
  have he' : p.Embeds := by
    apply listProgramTemplate_embeds
    intro t ht
    simp only [ps,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact he
    · exact resourceHeaderAdministrationTemplate_embeds
    · exact resourceHeaderEmissionTemplate_embeds
  have hr' : p.Runs := by
    apply listProgramTemplate_run
    · intro t ht
      simp only [ps,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact he
      · exact resourceHeaderAdministrationTemplate_embeds
      · exact resourceHeaderEmissionTemplate_embeds
    · intro t ht
      simp only [ps,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact hr
      · exact resourceHeaderAdministrationTemplate_run
      · exact resourceHeaderEmissionTemplate_run
  refine ⟨p,he',hr',?_,?_,?_,?_⟩
  · intro cs hs
    have ha : resourceHeaderAdministrationTemplate.ready (q.counters cs) := by
      apply (resourceHeaderAdministrationTemplate_ready _).2
      rw [hprivate,workspaceResult_scratch]
    have hh := (resourceHeaderEmissionTemplate_afterAdministration tm (cs (.inl 0))
      ((cs (.inl 0)+c)^d) (q.counters cs) (hprivate cs)).1
    exact ⟨hready cs hs,ha,hh,True.intro⟩
  · intro cs
    have hh := (resourceHeaderEmissionTemplate_afterAdministration tm (cs (.inl 0))
      ((cs (.inl 0)+c)^d) (q.counters cs) (hprivate cs)).2
    simpa [p,ps,listProgramTemplate,sequenceProgramTemplate,identityProgramTemplate,hbytes,
      resourceHeaderAdministrationTemplate_bytes,hshared] using hh
  · intro cs j
    simp [p,ps,listProgramTemplate,sequenceProgramTemplate,identityProgramTemplate,
      resourceHeaderEmissionTemplate,familyHeaderProgramTemplate,
      resourceHeaderAdministrationTemplate_counters,Function.update_apply,hshared]
  · intro bound
    apply listProgramTemplate_polynomial_certificate
    · intro t ht b
      simp only [ps,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact (hresources b).2
      · exact (resourceHeaderAdministrationTemplate_resources b).2
      · exact (resourceHeaderEmissionTemplate_resources b).2
    · intro t ht b
      simp only [ps,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact (hresources b).1
      · exact (resourceHeaderAdministrationTemplate_resources b).1
      · exact (resourceHeaderEmissionTemplate_resources b).1

end ShiReversibleGenerator
