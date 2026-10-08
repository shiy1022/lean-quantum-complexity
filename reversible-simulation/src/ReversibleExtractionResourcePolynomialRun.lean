import ReversibleExtractionResourceProgram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

noncomputable def extractionResourceState (tm : Turing.FinTM2) (n budget : Nat) : ExtractionMasterRegister → Nat :=
  fun q => match q with
    | .inl r => operationResult (workspaceOperations tm) (workspaceInitial tm n budget) r
    | .inr _ => 0

noncomputable def extractionResourcePayload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (n budget : Nat) : List Bool :=
  (extractionResourceTemplate tm e backward).bytes (extractionResourceState tm n budget)

/-- One finite program prints the original complete extraction forest from raw length with a polynomial actual clock. -/
theorem extractionResourceCode_polynomial_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (c d : Nat) :
    ∃ budget clock : Polynomial Nat,∀ n (ys : List Bool),
      let cs := extractionResourceState tm n ((n+c)^d)
      let p := extractionResourceTemplate tm e backward
      ∃ count,CounterRun (extractionResourceCode tm e backward c d)
        ⟨some (.inl (.inl ())),extractionResourceInitial n,ys⟩ count
        ⟨some (.inr (p.exit ())),p.counters cs,extractionResourcePayload tm e backward n ((n+c)^d)++ys⟩ ∧
        count ≤ clock.eval n ∧
        p.counters cs (.inr 16)=((extractionForest tm e (n+(n+c)^d*machinePushBound tm+1)).map
          (fun p => formulaElementaryLayers p+1)).sum ∧ ∀ q,p.counters cs q ≤ budget.eval n := by
  let time : Polynomial Nat := (Polynomial.X+Polynomial.C c)^d
  obtain ⟨cp,hp⟩ := extractionResourcePreludeCode_polynomial tm c d
  obtain ⟨⟨budget,hexit⟩,⟨cq,hq⟩⟩ := extractionResourceTemplate_resources tm e backward (resourceCounterBudgetPolynomial tm time)
  refine ⟨budget,cp+Polynomial.C 1+cq,?_⟩
  intro n ys
  dsimp only
  let cs := extractionResourceState tm n ((n+c)^d)
  obtain ⟨final,hfirst,hpull,houtside⟩ := hp Unit (fun _ => .halt) () n ys
  have hc : final.counters=cs := by
    funext q
    cases q with
    | inl r => exact congrArg (fun s => s.counters r) hpull
    | inr r => exact houtside r
  have he : final=⟨some (tickResourcePreludeExit tm c d),cs,ys⟩ := by
    apply CounterCfg.ext
    · simpa only [CounterCfg.pullRegisters,tickResourcePreludeExit] using congrArg (fun s => s.pc) hpull
    · exact hc
    · simpa only [CounterCfg.pullRegisters] using congrArg (fun s => s.output) hpull
  have hm : ∀ r,cs (.inl r)=operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r := by
    intro r
    simp only [cs,extractionResourceState,time,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  have hb := extractionResourcePrelude_uniform_bound tm time n cs hm (fun _ => rfl)
  have hr := extractionResourceTemplate_ready tm e backward cs
  have hsecond := extractionResourceTemplate_run tm e backward Unit (fun _ => .halt) () cs ys hr
  rw [he] at hfirst
  refine ⟨cp.eval n+1+(extractionResourceTemplate tm e backward).steps cs,?_,?_,?_,hexit n cs hb⟩
  · exact extractionResourceCode_joined_run tm e backward c d n ys _ cs (cp.eval n) hfirst hsecond
  · have ht := hq n cs hb hr
    simpa only [Polynomial.eval_add,Polynomial.eval_C] using Nat.add_le_add_left ht (cp.eval n+1)
  · exact (extractionResourceTemplate_payload_count tm e backward n ((n+c)^d) cs (fun _ => rfl)).2

end ShiReversibleGenerator
