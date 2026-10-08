import ReversiblePaddedFormulaPrinterRun

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

theorem counterUpdate_mono (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) (r : R)
    (a b : Nat) (hab : a ≤ b) :
    ∀ s, Function.update cs r a s ≤ Function.update ds r b s := by
  intro s
  by_cases hs : s = r <;> simp [hs, h s, hab]

theorem cleanupCounters_mono (rs : List R) (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) :
    ∀ s, cleanupCounters rs cs s ≤ cleanupCounters rs ds s := by
  induction rs generalizing cs ds with
  | nil => exact h
  | cons r rs ih => exact ih _ _ (counterUpdate_mono cs ds h r 0 0 (by rfl))

theorem cleanupSteps_mono (rs : List R) (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) :
    cleanupSteps rs cs ≤ cleanupSteps rs ds := by
  induction rs generalizing cs ds with
  | nil => rfl
  | cons r rs ih =>
      have ht := ih _ _ (counterUpdate_mono cs ds h r 0 0 (by rfl))
      simp only [cleanupSteps]
      have hr := h r
      omega

theorem GeneratorOperation.apply_mono (op : GeneratorOperation R)
    (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) : ∀ s, op.apply cs s ≤ op.apply ds s := by
  cases op with
  | affine a =>
      apply counterUpdate_mono cs ds h
      gcongr <;> exact h _
  | product p =>
      apply counterUpdate_mono cs ds h
      gcongr <;> exact h _

theorem GeneratorOperation.steps_mono (op : GeneratorOperation R)
    (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) : op.steps cs ≤ op.steps ds := by
  cases op <;> simp only [GeneratorOperation.steps, AffineAtom.steps] <;> gcongr <;> exact h _

theorem operationResult_mono (ops : List (GeneratorOperation R))
    (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) :
    ∀ s, operationResult ops cs s ≤ operationResult ops ds s := by
  induction ops generalizing cs ds with
  | nil => exact h
  | cons op ops ih => exact ih _ _ (op.apply_mono cs ds h)

theorem operationSteps_mono (ops : List (GeneratorOperation R))
    (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) : operationSteps ops cs ≤ operationSteps ops ds := by
  induction ops generalizing cs ds with
  | nil => rfl
  | cons op ops ih =>
      exact Nat.add_le_add (op.steps_mono cs ds h) (ih _ _ (op.apply_mono cs ds h))

theorem GeneratorAction.counters_mono (a : GeneratorAction R)
    (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) : ∀ s, a.counters cs s ≤ a.counters ds s := by
  cases a with
  | arithmetic op => exact op.apply_mono cs ds h
  | emit atom => exact h

theorem GeneratorAction.steps_mono (a : GeneratorAction R)
    (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) : a.steps cs ≤ a.steps ds := by
  cases a with
  | arithmetic op => exact op.steps_mono cs ds h
  | emit atom =>
      cases atom <;> simp only [GeneratorAction.steps, EmissionAtom.steps]
      · rfl
      · gcongr; exact h _

theorem actionSteps_mono (as : List (GeneratorAction R))
    (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) : actionSteps as cs ≤ actionSteps as ds := by
  induction as generalizing cs ds with
  | nil => rfl
  | cons a as ih =>
      exact Nat.add_le_add (a.steps_mono cs ds h) (ih _ _ (a.counters_mono cs ds h))

theorem FixedNodeTemplate.fields_mono (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) : ∀ s, t.fields r cs s ≤ t.fields r ds s :=
  operationResult_mono _ _ _ (cleanupCounters_mono _ cs ds h)

theorem FixedNodeTemplate.counters_mono (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) : ∀ s, t.counters r cs s ≤ t.counters r ds s := by
  apply counterUpdate_mono _ _ (t.fields_mono r cs ds h)
  exact Nat.add_le_add_right (t.fields_mono r cs ds h r.count) _

theorem FixedNodeTemplate.steps_mono (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) : t.steps r cs ≤ t.steps r ds :=
  Nat.add_le_add (Nat.add_le_add (cleanupSteps_mono _ cs ds h)
    (operationSteps_mono _ _ _ (cleanupCounters_mono _ cs ds h)))
    (actionSteps_mono _ _ _ (t.fields_mono r cs ds h))

theorem fixedNodeSteps_mono (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (cs ds : R → Nat) (h : ∀ s, cs s ≤ ds s) : fixedNodeSteps r ts cs ≤ fixedNodeSteps r ts ds := by
  induction ts generalizing cs ds with
  | nil => rfl
  | cons t ts ih =>
      exact Nat.add_le_add (t.steps_mono r cs ds h) (ih _ _ (t.counters_mono r cs ds h))

/-- Runtime loop values may vary arbitrarily below the supplied polynomial bounds. -/
theorem fixedNodeSteps_polynomial_bound (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (sizes : R → Polynomial Nat) (n : Nat) (cs : R → Nat)
    (h : ∀ s, cs s ≤ (sizes s).eval n) :
    fixedNodeSteps r ts cs ≤ (fixedNodeClock r ts sizes).eval n := by
  rw [fixedNodeClock_eval]
  exact fixedNodeSteps_mono r ts cs _ h

end ShiReversibleGenerator
