import ReversibleInitializerResourcePrelude

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

noncomputable def initializerResourceCode (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (c d : Nat) := by
  classical
  exact chainedCounterCode (initializerResourcePreludeCode tm c d) (rankedInitializerCode tm e backward)
    (tickResourcePreludeExit tm c d) (initializerSequenceEntry (rankedInitializerComponents tm e backward)) (.inl 0)

theorem initializerResourceCode_finite (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (c d : Nat) :
    Nonempty (Fintype (ResourcePreludeLabels tm c d Unit ⊕ initializerSequenceLabels (rankedInitializerComponents tm e backward))) := by
  classical
  exact ⟨inferInstance⟩

/-- The actual raw-length initializer prints its original padded quantum payload, with exact layers and polynomial instruction count. -/
theorem initializerResourceCode_polynomial_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (c d : Nat) :
    ∃ clock : Polynomial Nat,∀ n,
      let time : Polynomial Nat := (Polynomial.X+Polynomial.C c)^d
      let cs := initializationPreludeCounters tm time n
      let cap := (initializationCapacityPolynomial tm time).eval n
      let gs := initializationQuantumLayers tm e cap n backward
      let final := initializerSequenceCounters (rankedInitializerComponents tm e backward) n cs []
      ∃ count,CounterRun (initializerResourceCode tm e backward c d)
        ⟨some (.inl (.inl ())),initializerResourceInitial n,[]⟩ count
        ⟨some (.inr (initializerSequenceExit (rankedInitializerComponents tm e backward))),final,
          (gs.map ShiBQP.encLayer).flatten⟩ ∧ count ≤ clock.eval n ∧ final (.inr 10)=gs.length := by
  classical
  let time : Polynomial Nat := (Polynomial.X+Polynomial.C c)^d
  obtain ⟨cp,hp⟩ := initializerResourcePreludeCode_polynomial_run tm c d
  obtain ⟨cq,hq⟩ := rankedInitializer_circuit_certificate tm e time backward
  refine ⟨cp+Polynomial.C 1+cq,?_⟩
  intro n
  dsimp only
  have hfirst := hp n []
  have hsecond := hq n []
  dsimp only at hsecond
  simp only [List.append_nil] at hsecond
  let cs := initializationPreludeCounters tm time n
  let count := initializerSequenceSteps (rankedInitializerComponents tm e backward) n cs []
  let final := initializerSequenceCounters (rankedInitializerComponents tm e backward) n cs []
  let payload := ((initializationQuantumLayers tm e ((initializationCapacityPolynomial tm time).eval n) n backward).map ShiBQP.encLayer).flatten
  have hrun := chainedCounterCode_run (initializerResourcePreludeCode tm c d) (rankedInitializerCode tm e backward)
    (tickResourcePreludeExit tm c d) (initializerSequenceEntry (rankedInitializerComponents tm e backward)) (.inl 0)
    (initializerResourcePreludeCode_exit_halt tm c d) _ cs [] _ (cp.eval n) count hfirst hsecond.1
  refine ⟨cp.eval n+1+count,?_,?_,hsecond.2.2⟩
  · simpa only [initializerResourceCode,CounterCfg.relabel,Option.map_some] using hrun
  · simpa only [Polynomial.eval_add,Polynomial.eval_C] using
      Nat.add_le_add_left hsecond.2.1 (cp.eval n+1)

end ShiReversibleGenerator
