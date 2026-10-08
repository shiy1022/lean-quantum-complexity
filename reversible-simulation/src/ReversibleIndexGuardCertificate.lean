import ReversibleIndexGuardClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R] [Fintype L]

/-- A fixed finite guard instruction graph has its actual run, clean work counters and polynomial clock. -/
theorem indexGuardCode_certificate (g : TickIndexGuard) (caller : L → CounterInstr R L)
    (capacity position left right tmp : R) (le gt : L)
    (hcl : capacity ≠ left) (hpl : position ≠ left) (hcr : capacity ≠ right) (hpr : position ≠ right)
    (hcx : capacity ≠ tmp) (hpx : position ≠ tmp) (hlx : left ≠ tmp) (hrx : right ≠ tmp)
    (hlr : left ≠ right) (capacityBound positionBound : Polynomial Nat) :
    ∃ _finite : Fintype (IndexGuardLabels g L), ∃ clock : Polynomial Nat,
      ∀ n (cs : R → Nat) (ys : List Bool),
        cs capacity ≤ capacityBound.eval n → cs position ≤ positionBound.eval n →
        cs left = 0 → cs right = 0 → cs tmp = 0 →
        ∃ steps, CounterRun (indexGuardCode g caller capacity position left right tmp le gt)
          ⟨some (.inl 0), cs, ys⟩ steps
          ⟨some (indexGuardExit g (if g.eval (cs capacity) (cs position) then le else gt)), cs, ys⟩ ∧
          steps ≤ clock.eval n := by
  obtain ⟨clock, hclock⟩ := indexGuardSteps_polynomial g capacity position left right hcl hpl hlr
    capacityBound positionBound
  refine ⟨inferInstance, clock, ?_⟩
  intro n cs ys hc hi hl hr hx
  exact ⟨indexGuardSteps g capacity position left right cs,
    indexGuardCode_run g caller capacity position left right tmp le gt
      hcl hpl hcr hpr hcx hpx hlx hrx hlr cs hl hr hx ys,
    hclock n cs hc hi hl hr⟩

end ShiReversibleGenerator
