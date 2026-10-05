import «AMPUNI-fuel-frame»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMFuelTransfer
variable {K W : Type} [DecidableEq K] {G : K → Type}
abbrev Gam := ShiTMFuelFrame.Gam (G := G)
abbrev State := Option Bool × W
inductive Label where
  | reverseInput | loadInput | loadFuel | done
  deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.reverseInput, .loadInput, .loadFuel, .done]
  (by intro l; cases l <;> simp)

def move (src : ShiTMFuel.Stack) (dst : ShiTMFuel.Stack ⊕ K)
    (put : Bool → Gam (G := G) dst) (again next : Label) :
    Stmt (Gam (G := G)) Label (State (W := W)) :=
  .pop (.inl src) (fun v x => (x, v.2))
    (.branch (fun v => v.1.isSome)
      (.push dst (fun v => put (v.1.getD false)) (.goto (fun _ => again)))
      (.goto (fun _ => next)))

def machine (input fuel : K) (putInput : Bool → G input) (putFuel : Bool → G fuel) :
    Label → Stmt (Gam (G := G)) Label (State (W := W))
  | .reverseInput => move .input (.inl .scratch) id .reverseInput .loadInput
  | .loadInput => move .scratch (.inr input) putInput .loadInput .loadFuel
  | .loadFuel => move .fuel (.inr fuel) putFuel .loadFuel .done
  | .done => .halt

private theorem update_swap (S : ∀ j, List (Gam (G := G) j))
    (a b : ShiTMFuel.Stack ⊕ K) (ha : a ≠ b)
    (xs : List (Gam (G := G) a)) (ys : List (Gam (G := G) b)) :
    Function.update (Function.update S a xs) b ys =
      Function.update (Function.update S b ys) a xs := by
  funext j
  by_cases hja : j = a
  · subst j; simp [ha, Ne.symm ha]
  · by_cases hjb : j = b
    · subst j; simp [ha, Ne.symm ha]
    · simp [hja, hjb]

/-- Move a Boolean stack to a distinct destination, reversing its order and
applying the destination encoding, while preserving all unrelated stacks. -/
theorem move_run (M : Label → Stmt (Gam (G := G)) Label (State (W := W)))
    (src : ShiTMFuel.Stack) (dst : ShiTMFuel.Stack ⊕ K)
    (put : Bool → Gam (G := G) dst) (again next : Label)
    (hm : M again = move src dst put again next) (hne : dst ≠ .inl src)
    (xs : List Bool) (S : ∀ j, List (Gam (G := G) j)) (v : Option Bool) (w : W)
    (hs : S (.inl src) = xs) :
    (ShiTMSubroutine.run M)^[xs.length+1] (some ⟨some again, (v,w), S⟩) =
      some ⟨some next, (none,w),
        Function.update (Function.update S (.inl src) []) dst
          (xs.reverse.map put ++ S dst)⟩ := by
  induction xs generalizing S v with
  | nil =>
      simp [ShiTMSubroutine.run, step, hm, move, stepAux, hs, hne]
  | cons b xs ih =>
      let S₁ := Function.update (Function.update S (.inl src) xs) dst (put b::S dst)
      have hs₁ : S₁ (.inl src) = xs := by simp [S₁, hne, Ne.symm hne]
      have hstep : ShiTMSubroutine.run M (some ⟨some again, (v,w), S⟩) =
          some ⟨some again, (some b,w), S₁⟩ := by
        simp [ShiTMSubroutine.run, step, hm, move, stepAux, hs, S₁, hne]
      have h := ih S₁ (some b) hs₁
      rw [List.length_cons, Function.iterate_succ_apply, hstep, h]
      congr 1
      congr 1
      dsimp [S₁]
      rw [update_swap _ dst (.inl src) hne]
      simp [List.reverse_cons, List.map_append, List.append_assoc, hne, Ne.symm hne]

end ShiTMFuelTransfer
