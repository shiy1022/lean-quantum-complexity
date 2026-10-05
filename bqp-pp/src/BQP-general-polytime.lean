import «BQP-typed-polytime»

set_option autoImplicit false
namespace BQPGeneralPolyTime
open Turing Polynomial
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin

/-- Composition over arbitrary finite machine alphabets; output growth is proved. -/
theorem comp {α β γ A B C : Type} {ea : α → List A} {eb : β → List B}
    {ec : γ → List C} {f : α → β} {g : β → γ} (z : B)
    (hf : Nonempty (TM2ComputableInPolyTime ea eb f))
    (hg : Nonempty (TM2ComputableInPolyTime eb ec g)) :
    Nonempty (TM2ComputableInPolyTime ea ec (g ∘ f)) := by
  obtain ⟨M⟩ := hf
  obtain ⟨N⟩ := hg
  obtain ⟨c,hc⟩ := BQPChecked.reference32 M.tm.m
  let q : Polynomial ℕ := X + Polynomial.C c * M.time
  have hq : ∀ a, (eb (f a)).length ≤ q.eval (ea a).length := by
    intro a
    have h := BQPChecked.reference38 c hc _ _ _ (M.outputsFun a)
    simpa only [List.length_map, q, eval_add, eval_mul, eval_X, eval_C] using h
  obtain ⟨P,_⟩ := BQPChecked.reference2.1 α β γ A B C ea eb ec f g q z M N hq
  exact ⟨P⟩

end BQPGeneralPolyTime
