import ReversibleInitializerSequenceClock

set_option autoImplicit false
namespace ShiReversibleGenerator

theorem initializerSequenceCounters_append (left right : List InitializationComponent)
    (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    initializerSequenceCounters (left ++ right) n cs ys = initializerSequenceCounters right n
      (initializerSequenceCounters left n cs ys) (initializerSequenceOutput left n cs ys) := by
  induction left generalizing cs ys with
  | nil => rfl
  | cons c rest ih => simp only [List.cons_append, initializerSequenceCounters, initializerSequenceOutput, ih]

theorem initializerSequenceOutput_append (left right : List InitializationComponent)
    (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    initializerSequenceOutput (left ++ right) n cs ys = initializerSequenceOutput right n
      (initializerSequenceCounters left n cs ys) (initializerSequenceOutput left n cs ys) := by
  induction left generalizing cs ys with
  | nil => rfl
  | cons c rest ih => simp only [List.cons_append, initializerSequenceCounters, initializerSequenceOutput, ih]

theorem initializerSequenceSteps_append (left right : List InitializationComponent)
    (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    initializerSequenceSteps (left ++ right) n cs ys = initializerSequenceSteps left n cs ys +
      initializerSequenceSteps right n (initializerSequenceCounters left n cs ys) (initializerSequenceOutput left n cs ys) := by
  induction left generalizing cs ys with
  | nil => simp [initializerSequenceSteps, initializerSequenceCounters, initializerSequenceOutput]
  | cons c rest ih =>
      simp only [List.cons_append, initializerSequenceSteps, initializerSequenceCounters, initializerSequenceOutput, ih]
      omega

/-- A fixed sequence preserves the shared budget and has only capacity-times-constant layer growth. -/
theorem initializerSequence_budget_layers (components : List InitializationComponent)
    (capacity budget : Polynomial Nat) :
    (∀ c ∈ components, InitializationResources c capacity budget) →
    ∃ growth : Nat, ∀ n cs ys,
      cs (.inl 0) = n → cs (.inl 2) = capacity.eval n → cs (.inl 6) = 0 → cs (.inl 5) = 0 →
      CounterBudget cs (.inr 10) (budget.eval n) →
      CounterBudget (initializerSequenceCounters components n cs ys) (.inr 10) (budget.eval n) ∧
      initializerSequenceCounters components n cs ys (.inr 10) ≤ cs (.inr 10) + capacity.eval n * growth := by
  induction components with
  | nil =>
      intro resources
      refine ⟨0, ?_⟩
      intro n cs ys hn hcap hb ht hbudget
      exact ⟨hbudget, by simp [initializerSequenceCounters]⟩
  | cons c rest ih =>
      intro resources
      let rc := resources c (by simp)
      obtain ⟨growth, hg⟩ := ih (fun d hd => resources d (by simp [hd]))
      refine ⟨rc.growth + growth, ?_⟩
      intro n cs ys hn hcap hb ht hbudget
      have hfirst := rc.preserved n cs ys hn hcap hb ht hbudget
      obtain ⟨hrest, hl⟩ := hg n (c.counters n cs ys) (c.output n cs ys)
        (by simpa only [c.metadata] using hn)
        (by simpa only [c.metadata] using hcap)
        (by simpa only [c.metadata] using hb)
        (by simpa only [c.metadata] using ht) hfirst
      refine ⟨hrest, ?_⟩
      have hhead := rc.layers n cs ys
      rw [hcap] at hhead
      simp only [initializerSequenceCounters, Nat.mul_add]
      omega

/-- A separately supplied private-register invariant propagates through actual component results. -/
theorem initializerSequence_index_bound (components : List InitializationComponent) (n capacity : Nat)
    (hindex : ∀ c ∈ components, ∀ cs ys, cs (.inl 0) = n → cs (.inl 2) = capacity →
      cs (.inr 0) ≤ capacity → c.counters n cs ys (.inr 0) ≤ capacity)
    (cs : InitializationRegister → Nat) (ys : List Bool)
    (hn : cs (.inl 0) = n) (hcap : cs (.inl 2) = capacity) (hi : cs (.inr 0) ≤ capacity) :
    initializerSequenceCounters components n cs ys (.inr 0) ≤ capacity := by
  induction components generalizing cs ys with
  | nil => exact hi
  | cons c rest ih =>
      exact ih (fun d hd => hindex d (by simp [hd])) (c.counters n cs ys) (c.output n cs ys)
        (by simpa only [c.metadata] using hn)
        (by simpa only [c.metadata] using hcap)
        (hindex c (by simp) cs ys hn hcap hi)

end ShiReversibleGenerator
