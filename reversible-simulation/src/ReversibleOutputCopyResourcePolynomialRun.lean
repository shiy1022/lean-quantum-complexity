import ReversibleOutputCopyResourceProgram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def outputCopyResourceState (tm : Turing.FinTM2) (n budget : Nat) : OutputCopyMasterRegister → Nat :=
  fun q => match q with
    | .inl r => operationResult (workspaceOperations tm) (workspaceInitial tm n budget) r
    | .inr _ => 0

noncomputable def outputCopyResourcePayload (tm : Turing.FinTM2) (n budget : Nat) : List Bool :=
  outputCopyMasterTemplate.bytes (outputCopyResourceState tm n budget)

/-- A single finite program emits the copy circuit from raw length with a polynomial actual clock. -/
theorem outputCopyResourceCode_polynomial_run (tm : Turing.FinTM2) (c d : Nat) :
    ∃ clock : Polynomial Nat, ∀ n (ys : List Bool),
      let cs := outputCopyResourceState tm n ((n+c)^d)
      ∃ count,
        CounterRun (outputCopyResourceCode tm c d)
          ⟨some (.inl (.inl ())),outputCopyResourceInitial n,ys⟩ count
          ⟨some (.inr (outputCopyMasterTemplate.exit ())),outputCopyMasterTemplate.counters cs,
            outputCopyResourcePayload tm n ((n+c)^d)++ys⟩ ∧
        count ≤ clock.eval n ∧ outputCopyMasterTemplate.counters cs (.inr 2)=cs (.inl 9) ∧
        outputCopyMasterTemplate.counters cs (.inr 6)=0 := by
  let time : Polynomial Nat := (Polynomial.X+Polynomial.C c)^d
  obtain ⟨cp,hp⟩ := outputCopyResourcePreludeCode_polynomial tm c d
  obtain ⟨cq,hq⟩ := outputCopyMasterTemplate_polynomial (resourceCounterBudgetPolynomial tm time)
  refine ⟨cp+Polynomial.C 1+cq,?_⟩
  intro n ys
  dsimp only
  let cs := outputCopyResourceState tm n ((n+c)^d)
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
    simp only [cs,outputCopyResourceState,time,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  have hb := outputCopyResourcePrelude_uniform_bound tm time n cs hm (fun _ => rfl)
  have hs := (outputCopyResource_metadata tm n (time.eval n) cs hm).2.2.2.2
  have hr := (outputCopyMasterTemplate_ready cs).2 hs
  have hsecond := outputCopyMasterTemplate_run Unit (fun _ => .halt) () cs ys hr
  rw [he] at hfirst
  refine ⟨cp.eval n+1+outputCopyMasterTemplate.steps cs,?_,?_,?_⟩
  · exact outputCopyResourceCode_joined_run tm c d n ys _ cs (cp.eval n) hfirst hsecond
  · have ht := hq n cs hb hr
    simpa only [Polynomial.eval_add,Polynomial.eval_C] using Nat.add_le_add_left ht (cp.eval n+1)
  · exact outputCopyMasterTemplate_counts cs

/-- The payload in the raw-length program is exactly the quantum copy circuit at the actual layout. -/
theorem outputCopyResourcePayload_quantum (tm : Turing.FinTM2) (n budget : Nat) :
    let cs := outputCopyResourceState tm n budget
    let layout := outputCopyResource_root_layout tm n budget cs (fun _ => rfl)
    outputCopyResourcePayload tm n budget=
      ((stridedOutputCopyLayers (cs (.inl 10)+cs (.inl 9)) (cs (.inl 11)) (cs (.inl 4))
        (cs (.inl 10)) (cs (.inl 9)) layout.1
        (by have h := layout.2.2; omega) (Nat.le_refl _)).map ShiBQP.encLayer).flatten :=
  outputCopyResource_quantum_payload tm n budget (outputCopyResourceState tm n budget) (fun _ => rfl)

end ShiReversibleGenerator
