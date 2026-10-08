import ReversibleTemplateRegisterInjectionData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R S : Type} [DecidableEq R] [DecidableEq S]

/-- The injected finite graph preserves actual instruction counts and frames every counter outside its block. -/
theorem injectProgramTemplate_run (p : CounterProgramTemplate R) (f : R → S) (hf : Function.Injective f)
    (branch : R) (he : p.Embeds) (hp : p.Runs) : (injectProgramTemplate p f branch).Runs := by
  classical
  intro L caller stop cs ys hr
  let original := p.code (fun _ : Unit => .halt) ()
  let mapped := fun l => (original l).mapRegisters f
  let ambient : CounterCfg S (p.Labels Unit) := ⟨some (p.entry ()),cs,ys⟩
  have hsmall := hp Unit (fun _ => .halt) () (fun r => cs (f r)) ys hr
  obtain ⟨final,hmap,hpull⟩ := CounterRun.mapRegisters f hf original hsmall ambient rfl
  have houtside : ∀ q,(∀ r,f r ≠ q) → final.counters q=cs q := by
    intro q hq
    exact CounterRun.mapRegisters_outside f original hmap q hq
  have hcounter : final.counters=injectedTemplateCounters f cs (p.counters (fun r => cs (f r))) :=
    injectedTemplateCounters_unique f cs final.counters _
      (fun r => congrArg (fun s => s.counters r) hpull) houtside
  have hfinal : final=⟨some (p.exit ()),injectedTemplateCounters f cs (p.counters (fun r => cs (f r))),
      p.bytes (fun r => cs (f r))++ys⟩ := by
    apply CounterCfg.ext
    · simpa only [CounterCfg.pullRegisters] using congrArg (fun s => s.pc) hpull
    · exact hcounter
    · simpa only [CounterCfg.pullRegisters] using congrArg (fun s => s.output) hpull
  rw [hfinal] at hmap
  have hhalt : mapped (p.exit ())=.halt := by
    dsimp only [mapped,original]
    rw [he Unit (fun _ => .halt) () ()]
    rfl
  have hwhole := chainedCounterCode_run mapped caller (p.exit ()) stop (f branch) hhalt ambient
    (injectedTemplateCounters f cs (p.counters (fun r => cs (f r)))) (p.bytes (fun r => cs (f r))++ys)
    (⟨some stop,injectedTemplateCounters f cs (p.counters (fun r => cs (f r))),
      p.bytes (fun r => cs (f r))++ys⟩ : CounterCfg S L)
    (p.steps (fun r => cs (f r))) 0 hmap (CounterRun.refl _)
  simpa only [injectProgramTemplate,CounterCfg.relabel,Option.map_some,Nat.add_zero,mapped,original,ambient] using hwhole

/-- The one connecting branch adds one to the real polynomial instruction clock. -/
theorem injectProgramTemplate_polynomial (p : CounterProgramTemplate R) (f : R → S) (branch : R)
    (bound : Polynomial Nat) (hp : p.PolynomiallyTimed bound) :
    (injectProgramTemplate p f branch).PolynomiallyTimed bound := by
  obtain ⟨clock,hclock⟩ := hp
  refine ⟨clock+Polynomial.C 1,?_⟩
  intro n cs hb hr
  simpa only [injectProgramTemplate,Polynomial.eval_add,Polynomial.eval_C] using
    Nat.add_le_add_right (hclock n (fun r => cs (f r)) (fun r => hb (f r)) hr) 1

end ShiReversibleGenerator
