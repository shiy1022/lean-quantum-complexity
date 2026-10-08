import ReversibleOutputCopyResourceMetadata

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Real prelude counters establish every hypothesis of the finite copy emitter's circuit certificate. -/
theorem outputCopyResource_circuit_certificate (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : OutputCopyMasterRegister → Nat),
      ∀ (hpull : ∀ r,cs (.inl r)=operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r),
      (∀ q : OutputCopyRegister,cs (.inr q)=0) →
      ∀ (L : Type) (caller : L → CounterInstr OutputCopyMasterRegister L) (stop : L) (ys : List Bool),
      let p := outputCopyMasterTemplate
      let layout := outputCopyResource_root_layout tm n (time.eval n) cs hpull
      let gs := stridedOutputCopyLayers (cs (.inl 10)+cs (.inl 9)) (cs (.inl 11))
        (cs (.inl 4)) (cs (.inl 10)) (cs (.inl 9)) layout.1
        (by have h := layout.2.2; omega) (Nat.le_refl _)
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs (.inr 2)=cs (.inl 9) ∧
      p.counters cs (.inr 6)=0 ∧ ∀ q,p.counters cs (.inl q)=cs (.inl q) := by
  obtain ⟨clock,hclock⟩ := outputCopyMasterTemplate_circuit_certificate (resourceCounterBudgetPolynomial tm time)
  refine ⟨clock,?_⟩
  intro n cs hpull houtside L caller stop ys
  dsimp only
  have hb := outputCopyResourcePrelude_uniform_bound tm time n cs hpull houtside
  have hs := (outputCopyResource_metadata tm n (time.eval n) cs hpull).2.2.2.2
  obtain ⟨hstride,hend,hroot⟩ := outputCopyResource_root_layout tm n (time.eval n) cs hpull
  exact hclock n cs hb hs L caller stop ys _ _ hstride hend hroot (Nat.le_refl _)

end ShiReversibleGenerator
