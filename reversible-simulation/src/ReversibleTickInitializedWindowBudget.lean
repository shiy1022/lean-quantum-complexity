import ReversibleTickInitializedWindowTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickInitializedWindowTemplate_counters (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickInitializedWindowTemplate tm).counters cs=
      Function.update (Function.update cs (.inl 0) (cs (tickTraversalSpare tm 6)+17))
        (tickTraversalSpare tm 2) (cs (tickTraversalSpare tm 6)+18*configurationWidth tm (cs (.inl 1))) := by
  rw [tickWidth_affine]
  have h : cs (tickTraversalSpare tm 6)+18*(tickWidthSlope tm*cs (.inl 1)+tickWidthOffset tm)=
      cs (tickTraversalSpare tm 6)+18*tickWidthOffset tm+(18*tickWidthSlope tm)*cs (.inl 1) := by ring
  rw [h]
  simp [tickInitializedWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,AffineAtom.apply,tickInitializedWindowAtom,tickTraversalSpare]
  congr 1
  ring

theorem tickInitializedWindowTemplate_static_budget (tm : Turing.FinTM2) (wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hb : CounterBudget cs (.inl 9) wireBound)
    (hin : cs (tickTraversalSpare tm 6)+17 ≤ wireBound)
    (hout : cs (tickTraversalSpare tm 6)+18*configurationWidth tm (cs (.inl 1)) ≤ wireBound) :
    CounterBudget ((tickInitializedWindowTemplate tm).counters cs) (.inl 9) wireBound := by
  rw [tickInitializedWindowTemplate_counters]
  exact (hb.update _ _ hin).update _ _ hout

theorem tickInitializedWindowTemplate_ready_preserved (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm) ((tickInitializedWindowTemplate tm).counters cs) := by
  rw [tickInitializedWindowTemplate_counters]
  simpa [fixedGuardedEmitterReady,tickTraversalSpare] using hr

end ShiReversibleGenerator
