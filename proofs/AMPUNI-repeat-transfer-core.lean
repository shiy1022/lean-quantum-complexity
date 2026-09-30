import «AMPUNI-subroutine-lift»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatTransfer

variable {K L W : Type} [DecidableEq K] {G : K → Type}

/-- Transfer one stack to another with a Boolean register, reversing the list. -/
def move (src dst : K) (decode : G src → Bool) (encode : Bool → G dst)
    (again next : L) :
    Stmt G L (Option Bool × W) :=
  .pop src (fun v x => (x.map decode, v.2))
    (.branch (fun v => v.1.isSome)
      (.push dst (fun v => encode (v.1.getD false))
        (.goto (fun _ => again)))
      (.goto (fun _ => next)))

private theorem update_swap (S : ∀ j, List (G j))
    (a b : K) (hab : a ≠ b)
    (xs : List (G a)) (ys : List (G b)) :
    Function.update (Function.update S a xs) b ys =
      Function.update (Function.update S b ys) a xs := by
  funext j
  by_cases hja : j = a
  · subst j
    simp [hab, Ne.symm hab]
  · by_cases hjb : j = b
    · subst j
      simp [hab, Ne.symm hab]
    · simp [hja, hjb]

theorem move_run (M : L → Stmt G L (Option Bool × W))
    (src dst : K) (decode : G src → Bool) (encode : Bool → G dst)
    (again next : L)
    (hm : M again = move src dst decode encode again next)
    (hne : dst ≠ src)
    (xs : List (G src)) (S : ∀ j, List (G j))
    (v : Option Bool) (w : W) (hs : S src = xs) :
    (ShiTMSubroutine.run M)^[xs.length + 1]
      (some ⟨some again, (v, w), S⟩) =
        some ⟨some next, (none, w),
          Function.update (Function.update S src []) dst
            ((xs.map decode).reverse.map encode ++ S dst)⟩ := by
  induction xs generalizing S v with
  | nil =>
      simp [ShiTMSubroutine.run, step, hm, move, stepAux, hs, hne]
  | cons b xs ih =>
      let S₁ := Function.update (Function.update S src xs) dst
        (encode (decode b) :: S dst)
      have hs₁ : S₁ src = xs := by simp [S₁, hne, Ne.symm hne]
      have hstep :
          ShiTMSubroutine.run M (some ⟨some again, (v, w), S⟩) =
            some ⟨some again, (some (decode b), w), S₁⟩ := by
        simp [ShiTMSubroutine.run, step, hm, move, stepAux, hs,
          S₁, hne]
      have h := ih S₁ (some (decode b)) hs₁
      rw [List.length_cons, Function.iterate_succ_apply, hstep, h]
      congr 1
      congr 1
      dsimp [S₁]
      rw [update_swap _ dst src hne]
      simp [List.reverse_cons, List.map_append, List.append_assoc,
        hne, Ne.symm hne]

end ShiTMRepeatTransfer
