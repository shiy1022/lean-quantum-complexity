import ReversibleTemplateRegisterInjectionData

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R S : Type} [DecidableEq R] [DecidableEq S]

theorem injectedTemplateCounters_identity (f : R → S) (before : S → Nat) :
    injectedTemplateCounters f before (fun r => before (f r))=before := by
  exact (injectedTemplateCounters_unique f before before _ (fun _ => rfl) (fun _ _ => rfl)).symm

/-- Updating an actual injected counter corresponds exactly to updating its ambient register. -/
theorem injectedTemplateCounters_update (f : R → S) (hf : Function.Injective f)
    (before : S → Nat) (after : R → Nat) (r : R) (value : Nat) :
    injectedTemplateCounters f before (Function.update after r value)=
      Function.update (injectedTemplateCounters f before after) (f r) value := by
  apply Eq.symm
  apply injectedTemplateCounters_unique
  · intro s
    by_cases hs : s=r
    · subst s; simp
    · have hfs : f s ≠ f r := fun h => hs (hf h)
      simp only [Function.update_of_ne hs,Function.update_of_ne hfs]
      exact injectedTemplateCounters_pull f hf before after s
  · intro q hq
    rw [Function.update_of_ne (Ne.symm (hq r))]
    exact injectedTemplateCounters_outside f before after q hq

end ShiReversibleGenerator
