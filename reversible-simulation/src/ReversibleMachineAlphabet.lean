import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Tactic

set_option autoImplicit false

namespace ShiReversibleTM

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [Fintype σ]

/-- Only finitely many symbols can be pushed by a fixed finite statement tree. -/
noncomputable def pushSymbols : Turing.TM2.Stmt Γ Λ σ → Finset (Σ k, Γ k)
  | .push k f q => by
      classical
      exact (Finset.univ.image (fun v => ⟨k, f v⟩)) ∪ pushSymbols q
  | .peek _ _ q => pushSymbols q
  | .pop _ _ q => pushSymbols q
  | .load _ q => pushSymbols q
  | .branch _ q r => by classical exact pushSymbols q ∪ pushSymbols r
  | .goto _ => ∅
  | .halt => ∅

def StackAlphabet (A : Finset (Σ k, Γ k)) (S : ∀ k, List (Γ k)) : Prop :=
  ∀ k a, a ∈ S k → (⟨k, a⟩ : Σ k, Γ k) ∈ A

theorem stepAux_alphabet (q : Turing.TM2.Stmt Γ Λ σ) (A : Finset (Σ k, Γ k))
    (hq : pushSymbols q ⊆ A) (v : σ) (S : ∀ k, List (Γ k))
    (hs : StackAlphabet A S) : StackAlphabet A (Turing.TM2.stepAux q v S).stk := by
  classical
  induction q generalizing v S with
  | push k f q ih =>
    apply ih (fun z hz => hq (Finset.mem_union_right _ hz))
    intro i a ha
    by_cases hi : i = k
    · subst i
      simp only [Function.update_self, List.mem_cons] at ha
      rcases ha with ha | ha
      · subst a
        apply hq
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
      · exact hs k a ha
    · exact hs i a (by simpa [Function.update_of_ne hi] using ha)
  | peek k f q ih => exact ih hq _ _ hs
  | pop k f q ih =>
    apply ih hq
    intro i a ha
    by_cases hi : i = k
    · subst i
      simp only [Function.update_self] at ha
      exact hs k a (List.mem_of_mem_tail ha)
    · exact hs i a (by simpa [Function.update_of_ne hi] using ha)
  | load f q ih => exact ih hq _ _ hs
  | branch f q r ihq ihr =>
    cases hf : f v
    · simp only [Turing.TM2.stepAux, hf, Bool.cond_false]
      exact ihr (fun z hz => hq (Finset.mem_union_right _ hz)) v S hs
    · simp only [Turing.TM2.stepAux, hf, Bool.cond_true]
      exact ihq (fun z hz => hq (Finset.mem_union_left _ hz)) v S hs
  | goto f => exact hs
  | halt => exact hs

end ShiReversibleTM
