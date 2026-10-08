import ReversibleConstantInitializationBody
import ReversibleInitializationBodyBounds

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- The same address-clock bound works for constants in metadata and other stacks. -/
theorem constantInitialization_polynomial_bound (value backward : Bool)
    (sizes : InitializationRegister → Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat),
      (∀ r, cs r ≤ (sizes r).eval n) →
      constantInitializationSteps value backward cs ≤ clock.eval n := by
  let preparedSizes := initializationPreparedPolynomials sizes
  let clock := fixedNodeClock initializationNodeRegisters
    (constantInitializationTemplates value backward) preparedSizes
  refine ⟨initializationAddressClock sizes + clock, ?_⟩
  intro n cs h
  have hprep : ∀ r, initializationAddressResult cs r ≤ (preparedSizes r).eval n := by
    intro r
    change initializationAddressResult cs r ≤ (initializationPreparedPolynomials sizes r).eval n
    rw [congrFun (initializationPreparedPolynomials_eval sizes n) r]
    exact operationResult_mono initializationAddressOperations _ _
      (cleanupCounters_mono initializationAddressCleanup cs _ h) r
  have ha := Nat.add_le_add (cleanupSteps_mono initializationAddressCleanup cs _ h)
    (operationSteps_mono initializationAddressOperations _ _
      (cleanupCounters_mono initializationAddressCleanup cs _ h))
  rw [Polynomial.eval_add, initializationAddressClock_eval]
  exact Nat.add_le_add ha (fixedNodeSteps_polynomial_bound initializationNodeRegisters
    (constantInitializationTemplates value backward) preparedSizes n (initializationAddressResult cs) hprep)

theorem constantInitialization_preserves_metadata (value backward : Bool)
    (cs : InitializationRegister → Nat) (r : WorkspaceRegister) :
    constantInitializationCounters value backward cs (.inl r) = cs (.inl r) := by
  rw [constantInitializationCounters, fixedNodeCounters_other]
  · simp [initializationAddress_result]
  all_goals simp [initializationNodeRegisters]

theorem constantInitialization_preserves_index (value backward : Bool)
    (cs : InitializationRegister → Nat) :
    constantInitializationCounters value backward cs (.inr 0) = cs (.inr 0) := by
  rw [constantInitializationCounters, fixedNodeCounters_other]
  · simp [initializationAddress_result]
  all_goals simp [initializationNodeRegisters]

theorem constantInitialization_preserves_remaining (value backward : Bool)
    (cs : InitializationRegister → Nat) :
    constantInitializationCounters value backward cs (.inr 11) = cs (.inr 11) := by
  rw [constantInitializationCounters, fixedNodeCounters_other]
  · simp [initializationAddress_result]
  all_goals simp [initializationNodeRegisters]

theorem constantInitializationCode_embed {L : Type} (value backward : Bool)
    (caller : L → CounterInstr InitializationRegister L) (stop l : L) :
    constantInitializationCode value backward caller stop (constantInitializationExit value backward l) =
      (caller l).relabel (constantInitializationExit value backward) := by
  simp only [constantInitializationCode, initializationAddressCode, constantInitializationExit,
    cleanupCode_embed, operationCode_embed, fixedNodeCode_exit]
  cases caller l <;> rfl

end ShiReversibleGenerator
