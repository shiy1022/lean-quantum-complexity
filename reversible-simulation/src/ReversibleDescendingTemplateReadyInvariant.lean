import ReversibleDescendingTemplateData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

/-- A maintained traversal invariant proves every actual body is ready and preserves its loop counter. -/
theorem descendingTemplateReady_of_invariant (p : CounterProgramTemplate R) (remaining : R)
    (invariant : Nat → CounterCfg R L → Prop)
    (hready : ∀ k s, invariant (k+1) s → p.ready (Function.update s.counters remaining k))
    (hframe : ∀ k s, invariant (k+1) s → p.counters (Function.update s.counters remaining k) remaining = k)
    (hnext : ∀ k s, invariant (k+1) s → invariant k (templateDescendingBody p remaining k s))
    (k : Nat) (s : CounterCfg R L) (hs : invariant k s) :
    descendingTemplateReady p remaining k s.counters := by
  induction k generalizing s with
  | zero => trivial
  | succ k ih => exact ⟨hready k s hs,hframe k s hs,ih _ (hnext k s hs)⟩

end ShiReversibleGenerator
