import ReversibleCounterRegisterInjection
import ReversibleProgramTemplateSequence
import ReversibleCounterChain

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R S : Type}

/-- Replace only the injected register block, retaining every other ambient counter. -/
noncomputable def injectedTemplateCounters (f : R → S) (before : S → Nat) (after : R → Nat) : S → Nat := by
  classical
  exact fun q => if h : ∃ r,f r=q then after (Classical.choose h) else before q

theorem injectedTemplateCounters_pull (f : R → S) (hf : Function.Injective f)
    (before : S → Nat) (after : R → Nat) (r : R) :
    injectedTemplateCounters f before after (f r)=after r := by
  classical
  have h : ∃ a,f a=f r := ⟨r,rfl⟩
  simp only [injectedTemplateCounters,dif_pos h]
  rw [hf (Classical.choose_spec h)]

theorem injectedTemplateCounters_outside (f : R → S) (before : S → Nat) (after : R → Nat)
    (q : S) (hq : ∀ r,f r ≠ q) : injectedTemplateCounters f before after q=before q := by
  classical
  have h : ¬∃ r,f r=q := by rintro ⟨r,hr⟩; exact hq r hr
  simp only [injectedTemplateCounters,dif_neg h]

theorem injectedTemplateCounters_unique (f : R → S) (before final : S → Nat) (after : R → Nat)
    (hpull : ∀ r,final (f r)=after r) (houtside : ∀ q,(∀ r,f r ≠ q) → final q=before q) :
    final=injectedTemplateCounters f before after := by
  classical
  funext q
  by_cases h : ∃ r,f r=q
  · simp only [injectedTemplateCounters,dif_pos h]
    exact (congrArg final (Classical.choose_spec h).symm).trans (hpull _)
  · rw [injectedTemplateCounters_outside f before after q (by intro r hr; exact h ⟨r,hr⟩)]
    exact houtside q (by intro r hr; exact h ⟨r,hr⟩)

/-- A one-instruction continuation bridge lifts any fixed finite template into an ambient register file. -/
noncomputable def injectProgramTemplate [DecidableEq R] [DecidableEq S]
    (p : CounterProgramTemplate R) (f : R → S) (branch : R) : CounterProgramTemplate S := by
  classical
  exact {
    Labels := fun L => p.Labels Unit ⊕ L
    finite := fun L fl => by
      letI := fl
      letI := p.finite Unit inferInstance
      infer_instance
    code := fun caller stop => chainedCounterCode
      (fun l => (p.code (fun _ : Unit => .halt) () l).mapRegisters f) caller
      (p.exit ()) stop (f branch)
    entry := fun _ => .inl (p.entry ())
    exit := Sum.inr
    ready := fun cs => p.ready (fun r => cs (f r))
    steps := fun cs => p.steps (fun r => cs (f r))+1
    counters := fun cs => injectedTemplateCounters f cs (p.counters (fun r => cs (f r)))
    bytes := fun cs => p.bytes (fun r => cs (f r)) }

theorem injectProgramTemplate_embeds [DecidableEq R] [DecidableEq S]
    (p : CounterProgramTemplate R) (f : R → S) (branch : R) : (injectProgramTemplate p f branch).Embeds := by
  intro L caller stop l
  rfl

end ShiReversibleGenerator
