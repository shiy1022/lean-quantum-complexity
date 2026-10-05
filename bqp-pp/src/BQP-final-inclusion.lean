import «BQP-router-complete»

set_option autoImplicit false
namespace BQPFinal

/-- BQP is contained in PP, for the original circuit-family and counting-class
definitions. All compiler, arithmetic, splitting, and routing machines are proved. -/
theorem bqp_subset_pp : ShiBQP.BQP ⊆ ShiClassPP.PP := by
  intro L hL
  obtain ⟨F,k,huni,_hwf,_hpoly,hcount⟩ := BQPProgram.bqp_counting_reduction L hL
  exact ⟨BQPProgram.patchedRelation L F, k,
    BQPProgram.patchedRelation_polyTime L F (BQPProgram.longRelation_polyTime F huni), hcount⟩

end BQPFinal

/-- Public endpoint in the original BQP namespace. -/
theorem ShiBQP.bqp_subset_pp : ShiBQP.BQP ⊆ ShiClassPP.PP := BQPFinal.bqp_subset_pp
