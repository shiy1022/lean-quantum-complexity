import ReversibleExtractionIndexSetup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionIndexSetupTemplate_budget (cs : ExtractionTermRegister → Nat) (B : Nat)
    (hb : ∀ q,cs q ≤ B) : ∀ q,extractionIndexSetupTemplate.counters cs q ≤ B := by
  intro q
  rw [extractionIndexSetupTemplate_counters]
  have h1 := hb 1
  have h8 := hb 8
  have h2 := hb 2
  have hq := hb q
  simp only [Function.update_apply]
  split_ifs <;> omega

end ShiReversibleGenerator
