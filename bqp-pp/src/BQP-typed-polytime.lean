import «BQP-closed-references»

set_option autoImplicit false
namespace BQPTypedPolyTime
open Turing Polynomial
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin

/-- Typed polynomial-time composition, with the intermediate size bound derived
from the finite source machine rather than supplied as an extra hypothesis. -/
theorem comp {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ}
    (hf : Nonempty (TM2ComputableInPolyTime ea eb f))
    (hg : Nonempty (TM2ComputableInPolyTime eb ec g)) :
    Nonempty (TM2ComputableInPolyTime ea ec (g ∘ f)) := by
  obtain ⟨A⟩ := hf
  obtain ⟨B⟩ := hg
  obtain ⟨c,hc⟩ := BQPChecked.reference32 A.tm.m
  let q : Polynomial ℕ := X + C c * A.time
  have hq : ∀ a, (eb (f a)).length ≤ q.eval (ea a).length := by
    intro a
    have h := BQPChecked.reference38 c hc _ _ _ (A.outputsFun a)
    simpa only [List.length_map, q, eval_add, eval_mul, eval_X, eval_C] using h
  obtain ⟨M, _⟩ := BQPChecked.reference2.1 α β γ Bool Bool Bool ea eb ec f g q false A B hq
  exact ⟨M⟩

/-- Change the represented domain when its encoded strings are identical. -/
theorem precompose {α α' β : Type} {ea : α → List Bool} {ea' : α' → List Bool}
    {eb : β → List Bool} {f : α → β} (u : α' → α)
    (he : ∀ a, ea (u a) = ea' a)
    (hf : Nonempty (TM2ComputableInPolyTime ea eb f)) :
    Nonempty (TM2ComputableInPolyTime ea' eb (f ∘ u)) := by
  obtain ⟨A⟩ := hf
  exact ⟨{ A with outputsFun := fun a => by simpa only [Function.comp_apply, he] using A.outputsFun (u a) }⟩

end BQPTypedPolyTime
