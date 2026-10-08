import ReversibleConfigurationHeaderBudget
import ReversibleInitializerSequenceResources
import ReversibleInitializerIndexFrames

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- The complete actual ranked initializer, including its header and connecting instructions, has a polynomial clock. -/
theorem rankedInitializer_polynomial_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (capacity initial layers : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n cs ys,
      cs (.inl 0) = n → cs (.inl 2) = capacity.eval n → cs (.inl 6) = 0 → cs (.inl 5) = 0 →
      cs (.inr 0) ≤ capacity.eval n →
      CounterBudget cs (.inr 10) ((machineInitializationBudget tm capacity initial).eval n) →
      cs (.inr 10) ≤ layers.eval n →
      initializerSequenceSteps (rankedInitializerComponents tm e backward) n cs ys ≤ clock.eval n := by
  classical
  let stackComponents := (initializationStackSchedule tm backward).map (packagedInitializationStack tm e backward)
  let header := packagedConfigurationHeader tm backward
  have resources : ∀ c ∈ stackComponents,
      InitializationResources c capacity (machineInitializationBudget tm capacity initial) := by
    intro c hc
    let h := List.mem_map.mp hc
    let k := Classical.choose h
    have he : packagedInitializationStack tm e backward k = c := (Classical.choose_spec h).2
    exact he ▸ packagedInitializationStack_resources tm e backward capacity initial k
  obtain ⟨growth, hg⟩ := initializerSequence_budget_layers stackComponents capacity
    (machineInitializationBudget tm capacity initial) resources
  have hindex : ∀ n cs ys, cs (.inl 0) = n → cs (.inl 2) = capacity.eval n →
      cs (.inr 0) ≤ capacity.eval n → initializerSequenceCounters stackComponents n cs ys (.inr 0) ≤ capacity.eval n := by
    intro n cs ys hn hcap hi
    apply initializerSequence_index_bound stackComponents n (capacity.eval n) _ cs ys hn hcap hi
    intro c hc cs' ys' hn' hcap' hi'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
    exact packagedInitializationStack_index_bound tm e backward (capacity.eval n) n k cs' ys' hcap'
  cases backward with
  | false =>
      obtain ⟨p, hp⟩ := rankedInitializerStacks_polynomial_bound tm e false capacity initial layers
      obtain ⟨q, hq⟩ := configurationHeader_polynomial_bound tm false capacity initial
        (layers + capacity * Polynomial.C growth)
      refine ⟨p + Polynomial.C 1 + q, ?_⟩
      intro n cs ys hn hcap hb ht hi hbudget hl
      let cs' := initializerSequenceCounters stackComponents n cs ys
      let ys' := initializerSequenceOutput stackComponents n cs ys
      obtain ⟨hbudget', hgrowth⟩ := hg n cs ys hn hcap hb ht hbudget
      have hl' : cs' (.inr 10) ≤ (layers + capacity * Polynomial.C growth).eval n := by
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
        exact hgrowth.trans (Nat.add_le_add_right hl _)
      have hfirst := hp n cs ys hn hcap hb ht hbudget hl
      have hlast := hq n cs' ys'
        (by simpa only [cs', initializerSequence_metadata] using hn)
        (hindex n cs ys hn hcap hi) hbudget' hl'
      change initializerSequenceSteps (stackComponents ++ [header]) n cs ys ≤ _
      rw [initializerSequenceSteps_append]
      simp only [initializerSequenceSteps, Polynomial.eval_add, Polynomial.eval_C]
      change initializerSequenceSteps stackComponents n cs ys + (header.steps n cs' ys' + 1 + 0) ≤ p.eval n + 1 + q.eval n
      change initializerSequenceSteps stackComponents n cs ys ≤ p.eval n at hfirst
      change header.steps n cs' ys' ≤ q.eval n at hlast
      omega
  | true =>
      obtain ⟨q, hq⟩ := configurationHeader_polynomial_bound tm true capacity initial layers
      obtain ⟨p, hp⟩ := rankedInitializerStacks_polynomial_bound tm e true capacity initial
        (layers + Polynomial.C ((initializationHeaderSchedule tm true).length * 630))
      refine ⟨q + Polynomial.C 1 + p, ?_⟩
      intro n cs ys hn hcap hb ht hi hbudget hl
      let cs' := header.counters n cs ys
      let ys' := header.output n cs ys
      have hbudget' := configurationHeader_budget tm true capacity initial n cs ys hn hi hbudget
      have hl' : cs' (.inr 10) ≤
          (layers + Polynomial.C ((initializationHeaderSchedule tm true).length * 630)).eval n := by
        have hh := configurationHeader_layer_bound tm true n cs ys
        simp only [Polynomial.eval_add, Polynomial.eval_C]
        exact hh.trans (Nat.add_le_add_right hl _)
      have hfirst := hq n cs ys hn hi hbudget hl
      have hrest := hp n cs' ys'
        (by simpa only [cs', header.metadata] using hn)
        (by simpa only [cs', header.metadata] using hcap)
        (by simpa only [cs', header.metadata] using hb)
        (by simpa only [cs', header.metadata] using ht) hbudget' hl'
      change initializerSequenceSteps (header :: stackComponents) n cs ys ≤ _
      simp only [initializerSequenceSteps, Polynomial.eval_add, Polynomial.eval_C]
      change header.steps n cs ys + 1 + initializerSequenceSteps stackComponents n cs' ys' ≤ q.eval n + 1 + p.eval n
      exact Nat.add_le_add (Nat.add_le_add_right hfirst 1) hrest

end ShiReversibleGenerator
