import «AMPUNI-repeat-transfer-core»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatTransfer

variable {K L W : Type} [DecidableEq K] {G : K → Type}

private theorem update_self (S : ∀ j, List (G j)) (j : K) :
    Function.update S j (S j) = S := by
  funext k
  by_cases hk : k = j
  · subst k; simp
  · simp [hk]

/-- Duplicate a Boolean-coded source onto two distinct stacks in one pass. -/
def duplicate (src dst₁ dst₂ : K)
    (decode : G src → Bool)
    (encode₁ : Bool → G dst₁) (encode₂ : Bool → G dst₂)
    (again next : L) :
    Stmt G L (Option Bool × W) :=
  .pop src (fun v x => (x.map decode, v.2))
    (.branch (fun v => v.1.isSome)
      (.push dst₁ (fun v => encode₁ (v.1.getD false))
        (.push dst₂ (fun v => encode₂ (v.1.getD false))
          (.goto (fun _ => again))))
      (.goto (fun _ => next)))

theorem duplicate_run (M : L → Stmt G L (Option Bool × W))
    (src dst₁ dst₂ : K)
    (decode : G src → Bool)
    (encode₁ : Bool → G dst₁) (encode₂ : Bool → G dst₂)
    (again next : L)
    (hm : M again = duplicate src dst₁ dst₂ decode encode₁ encode₂ again next)
    (h₁ : dst₁ ≠ src) (h₂ : dst₂ ≠ src) (h₁₂ : dst₁ ≠ dst₂)
    (xs : List (G src)) (S : ∀ j, List (G j))
    (v : Option Bool) (w : W) (hs : S src = xs) :
    (ShiTMSubroutine.run M)^[xs.length + 1]
      (some ⟨some again, (v, w), S⟩) =
        some ⟨some next, (none, w),
          Function.update
            (Function.update (Function.update S src []) dst₁
              ((xs.map decode).reverse.map encode₁ ++ S dst₁))
            dst₂ ((xs.map decode).reverse.map encode₂ ++ S dst₂)⟩ := by
  induction xs generalizing S v with
  | nil =>
      have hsrc : Function.update S src [] = S := by
        funext j
        by_cases hj : j = src
        · subst j; simp [hs]
        · simp [hj]
      have hstack :
          Function.update S src [] =
            Function.update
              (Function.update (Function.update S src []) dst₁ (S dst₁))
              dst₂ (S dst₂) := by
        simp only [hsrc, update_self]
      simpa [ShiTMSubroutine.run, step, hm, duplicate, stepAux, hs]
        using congrArg
          (fun T : ∀ j, List (G j) =>
            some (⟨some next, (none, w), T⟩ : Cfg G L (Option Bool × W)))
          hstack
  | cons b xs ih =>
      let S₁ :=
        Function.update
          (Function.update (Function.update S src xs) dst₁
            (encode₁ (decode b) :: S dst₁))
          dst₂ (encode₂ (decode b) :: S dst₂)
      have hs₁ : S₁ src = xs := by
        simp [S₁, h₁, h₂, Ne.symm h₁, Ne.symm h₂]
      have hstep :
          ShiTMSubroutine.run M
            (some ⟨some again, (v, w), S⟩) =
              some ⟨some again, (some (decode b), w), S₁⟩ := by
        simp [ShiTMSubroutine.run, step, hm, duplicate, stepAux,
          hs, S₁, h₁, h₂, h₁₂, Ne.symm h₁₂]
      have h := ih S₁ (some (decode b)) hs₁
      rw [List.length_cons, Function.iterate_succ_apply, hstep, h]
      congr 1
      congr 1
      funext j
      by_cases hj₀ : j = src
      · subst j
        simp [S₁, h₁, h₂, Ne.symm h₁, Ne.symm h₂]
      · by_cases hj₁ : j = dst₁
        · subst j
          simp [S₁, hj₀, h₁₂, Ne.symm h₁₂,
            List.reverse_cons, List.map_append, List.append_assoc]
        · by_cases hj₂ : j = dst₂
          · subst j
            simp [S₁, hj₀, hj₁,
              List.reverse_cons, List.map_append, List.append_assoc]
          · simp [S₁, hj₀, hj₁, hj₂]

end ShiTMRepeatTransfer
