import ReversibleTickMetadataHandoffClock
import ReversibleResourceCounterBounds

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The existing resource polynomial bounds every ambient counter, including the framed extra registers. -/
theorem tickResourcePrelude_uniform_bound (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hpull : ∀ r,cs (workspaceTickRegister tm r)=
      operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r)
    (houtside : ∀ q,(∀ r,workspaceTickRegister tm r ≠ q) → cs q=0) :
    ∀ q,cs q ≤ (resourceCounterBudgetPolynomial tm time).eval n := by
  classical
  intro q
  by_cases hq : ∃ r,workspaceTickRegister tm r=q
  · obtain ⟨r,rfl⟩ := hq
    rw [hpull]
    exact resourceCounterBudgetPolynomial_bound tm time n r
  · rw [houtside q (by intro r h; exact hq ⟨r,h⟩)]
    exact Nat.zero_le _

theorem tickResourceHandoff_uniform_bound (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hpull : ∀ r,cs (workspaceTickRegister tm r)=
      operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r)
    (houtside : ∀ q,(∀ r,workspaceTickRegister tm r ≠ q) → cs q=0) :
    ∀ q,(tickMetadataHandoffTemplate tm).counters cs q ≤ (resourceCounterBudgetPolynomial tm time).eval n :=
  tickMetadataHandoffTemplate_uniform_bound tm _ cs (tickResourcePrelude_uniform_bound tm time n cs hpull houtside)

/-- An actual finite handoff run and clock now follow from the real prelude's metadata and frame contract. -/
theorem tickResourceHandoff_polynomial_run (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      (∀ r,cs (workspaceTickRegister tm r)=operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r) →
      (∀ q,(∀ r,workspaceTickRegister tm r ≠ q) → cs q=0) →
      ∀ (L : Type) (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop : L) (ys : List Bool),
      let p := tickMetadataHandoffTemplate tm
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,ys⟩ ∧ p.steps cs ≤ clock.eval n := by
  obtain ⟨clock,hclock⟩ := tickMetadataHandoffTemplate_polynomial tm (resourceCounterBudgetPolynomial tm time)
  refine ⟨clock,?_⟩
  intro n cs hpull houtside L caller stop ys
  dsimp only
  have hb := tickResourcePrelude_uniform_bound tm time n cs hpull houtside
  have hs := (tickResourcePrelude_metadata tm n (time.eval n) cs hpull).2.2.2.2.1
  have hr := (tickMetadataHandoffTemplate_ready tm cs).2 hs
  have hrun := tickMetadataHandoffTemplate_run tm L caller stop cs ys hr
  rw [tickMetadataHandoffTemplate_bytes,List.nil_append] at hrun
  exact ⟨hrun,hclock n cs hb hr⟩

end ShiReversibleGenerator
