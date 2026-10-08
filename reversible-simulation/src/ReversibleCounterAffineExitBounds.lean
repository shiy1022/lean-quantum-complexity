import ReversibleCounterAffineProgramTemplates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

theorem counterAffineUnitCopyProgramTemplate_budget (source target tmp : R) (negative : Nat)
    (cs : R → Nat) (B : Nat) (hb : ∀ q,cs q ≤ B) :
    ∀ q,(counterAffineCopyProgramTemplate source target tmp 0 1 negative).counters cs q ≤ B := by
  intro q
  by_cases hq : q=target
  · subst q
    simp only [counterAffineCopyProgramTemplate,Function.update_self,Nat.one_mul,Nat.add_zero]
    exact (Nat.sub_le _ _).trans (hb source)
  · simpa only [counterAffineCopyProgramTemplate,Function.update_of_ne hq] using hb q

theorem counterAffineUnitAccumulationProgramTemplate_budget (source target tmp : R)
    (cs : R → Nat) (B : Nat) (hb : ∀ q,cs q ≤ B) :
    ∀ q,(counterAffineAccumulationProgramTemplate ⟨source,target,0,1⟩ tmp).counters cs q ≤ 2*B := by
  intro q
  have hs := hb source
  have ht := hb target
  have hq := hb q
  simp only [counterAffineAccumulationProgramTemplate,AffineAtom.apply,Function.update_apply]
  split_ifs <;> omega

end ShiReversibleGenerator
