import «AMPUNI-retained-nested-lift»

set_option autoImplicit false

namespace ShiTMOuterLift

instance : Fintype OuterControl :=
  Fintype.ofList
    [.circuitHeader, .layerDriver, .layerHeader, .gateDriver, .exit]
    (by intro x; cases x <;> simp)

end ShiTMOuterLift

namespace ShiTMRetainedTop

instance : Fintype Header :=
  Fintype.ofList
    [.inputLength, .witnessCount, .ancillaCount, .outputIndex]
    (by intro x; cases x <;> simp)

instance (k : TopK) : Fintype (TopGam k) := by
  cases k with
  | inl k =>
      cases k <;> infer_instance
  | inr k => infer_instance

def finite_top_machine : Fintype TopK × Fintype TopLabel ×
    (∀ k : TopK, Fintype (TopGam k)) := by
  exact ⟨inferInstance, inferInstance, fun k => inferInstance⟩

end ShiTMRetainedTop
