import ReversibleInitializerCircuitCertificate
import ReversibleTickResourcePreludeExit
import ReversibleCounterOutputSuffix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

noncomputable def initializerResourceInitial (n : Nat) : InitializationRegister → Nat :=
  Sum.elim (resourceBudgetState n 0) (fun _ => 0)

noncomputable def initializerResourcePreludeCode (tm : Turing.FinTM2) (c d : Nat) :=
  fun l => (resourcePreludeCode tm c d (fun _ : Unit => .halt) () l).mapRegisters
    (Sum.inl : WorkspaceRegister → InitializationRegister)

/-- The actual resource graph initializes the ranked initializer from raw length, with an exact polynomial instruction clock. -/
theorem initializerResourcePreludeCode_polynomial_run (tm : Turing.FinTM2) (c d : Nat) :
    ∃ clock : Polynomial Nat,∀ n (ys : List Bool),
      CounterRun (initializerResourcePreludeCode tm c d)
        ⟨some (.inl ()),initializerResourceInitial n,ys⟩ (clock.eval n)
        ⟨some (tickResourcePreludeExit tm c d),
          initializationPreludeCounters tm ((Polynomial.X+Polynomial.C c)^d) n,ys⟩ := by
  obtain ⟨clock,hclock⟩ := resourcePreludeCode_clock_polynomial tm c d
  refine ⟨clock,?_⟩
  intro n ys
  let original := resourcePreludeCode tm c d (fun _ : Unit => .halt) ()
  let ambient : CounterCfg InitializationRegister (ResourcePreludeLabels tm c d Unit) :=
    ⟨some (.inl ()),initializerResourceInitial n,ys⟩
  have hsmall := resourcePreludeCode_run tm c d (fun _ : Unit => .halt) () n ys
  rw [hclock n] at hsmall
  obtain ⟨final,hmap,hpull⟩ := CounterRun.mapRegisters
    (Sum.inl : WorkspaceRegister → InitializationRegister) (by intro a b h; exact Sum.inl.inj h)
    original hsmall ambient rfl
  have hzero : ∀ r : Fin 16,final.counters (.inr r)=0 := by
    intro r
    exact CounterRun.mapRegisters_outside _ original hmap (.inr r) (by intro q; simp)
  have he : final=⟨some (tickResourcePreludeExit tm c d),
      initializationPreludeCounters tm ((Polynomial.X+Polynomial.C c)^d) n,ys⟩ := by
    apply CounterCfg.ext
    · simpa only [CounterCfg.pullRegisters,tickResourcePreludeExit] using congrArg (fun s => s.pc) hpull
    · funext q
      cases q with
      | inl r =>
        have h := congrArg (fun s => s.counters r) hpull
        simpa only [CounterCfg.pullRegisters,initializationPreludeCounters,Sum.elim_inl,
          Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C] using h
      | inr r => exact hzero r
    · simpa only [CounterCfg.pullRegisters] using congrArg (fun s => s.output) hpull
  rw [he] at hmap
  exact hmap

theorem initializerResourcePreludeCode_exit_halt (tm : Turing.FinTM2) (c d : Nat) :
    initializerResourcePreludeCode tm c d (tickResourcePreludeExit tm c d)=.halt := by
  unfold initializerResourcePreludeCode tickResourcePreludeExit resourcePreludeCode
  rw [initializedBudgetCode_embed,operationCode_embed,operationCode_embed]
  rfl

end ShiReversibleGenerator
