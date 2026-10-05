import «AMPUNI-fuel-transfer»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMFuelTransfer
variable {K W : Type} [DecidableEq K] {G : K → Type}

private theorem update_left (A : ∀ h, List (ShiTMFuel.Gam h)) (S : ∀ j, List (G j))
    (a : ShiTMFuel.Stack) (xs : List Bool) :
    Function.update (ShiTMStackFrame.extendStacks A S) (.inl a) xs =
      ShiTMStackFrame.extendStacks (Function.update A a xs) S := by
  funext j
  cases j with
  | inl j =>
      by_cases h : j = a
      · subst j; simp [ShiTMStackFrame.extendStacks]
      · simp [ShiTMStackFrame.extendStacks, h]
  | inr j => simp [ShiTMStackFrame.extendStacks]

private theorem update_right (A : ∀ h, List (ShiTMFuel.Gam h)) (S : ∀ j, List (G j))
    (j : K) (xs : List (G j)) :
    Function.update (ShiTMStackFrame.extendStacks A S) (.inr j) xs =
      ShiTMStackFrame.extendStacks A (Function.update S j xs) := by
  funext a
  cases a with
  | inl a => simp [ShiTMStackFrame.extendStacks]
  | inr a =>
      by_cases h : a = j
      · subst a; simp [ShiTMStackFrame.extendStacks]
      · simp [ShiTMStackFrame.extendStacks, h]

def transferred (input fuel : K) (putInput : Bool → G input) (putFuel : Bool → G fuel)
    (xs : List Bool) (budget : Nat) : ∀ j, List (G j) :=
  Function.update (Function.update (fun _ => []) input (xs.map putInput)) fuel
    ((List.replicate budget true).map putFuel)

/-- Move prepared input and fuel into the future machine. All initializer
stacks are empty at the active exit; the input's original order is retained. -/
theorem transfer_run (input fuel : K) (putInput : Bool → G input) (putFuel : Bool → G fuel)
    (hne : fuel ≠ input) (w : W) (xs : List Bool) (budget : Nat) :
    (ShiTMSubroutine.run (machine input fuel putInput putFuel))^[2*xs.length+budget+3]
      (some ⟨some .reverseInput, (none,w),
        ShiTMStackFrame.extendStacks
          (ShiTMFuel.storeFn xs [] [] (List.replicate budget true)) (fun _ => [])⟩) =
      some ⟨some .done, (none,w),
        ShiTMStackFrame.extendStacks (fun _ => [])
          (transferred input fuel putInput putFuel xs budget)⟩ := by
  let M := machine (W := W) input fuel putInput putFuel
  let S₀ := ShiTMStackFrame.extendStacks
    (ShiTMFuel.storeFn xs [] [] (List.replicate budget true)) (fun j : K => ([] : List (G j)))
  let S₁ := ShiTMStackFrame.extendStacks
    (ShiTMFuel.storeFn [] xs.reverse [] (List.replicate budget true)) (fun j : K => ([] : List (G j)))
  let T := Function.update (fun j : K => ([] : List (G j))) input (xs.map putInput)
  let S₂ := ShiTMStackFrame.extendStacks
    (ShiTMFuel.storeFn [] [] [] (List.replicate budget true)) T
  have h₀ := move_run M .input (.inl .scratch) id .reverseInput .loadInput rfl
    (by simp) xs S₀ none w rfl
  have h₀' : (ShiTMSubroutine.run M)^[xs.length+1]
      (some ⟨some .reverseInput, (none,w), S₀⟩) =
      some ⟨some .loadInput, (none,w), S₁⟩ := by
    simpa [S₀, S₁, update_left, ShiTMStackFrame.extendStacks] using h₀
  have h₁ := move_run M .scratch (.inr input) putInput .loadInput .loadFuel rfl
    (by simp) xs.reverse S₁ none w rfl
  have h₁' : (ShiTMSubroutine.run M)^[xs.length+1]
      (some ⟨some .loadInput, (none,w), S₁⟩) =
      some ⟨some .loadFuel, (none,w), S₂⟩ := by
    simpa [S₁, S₂, T, update_left, update_right, ShiTMStackFrame.extendStacks] using h₁
  have h₂ := move_run M .fuel (.inr fuel) putFuel .loadFuel .done rfl
    (by simp) (List.replicate budget true) S₂ none w rfl
  have h₂' : (ShiTMSubroutine.run M)^[budget+1]
      (some ⟨some .loadFuel, (none,w), S₂⟩) =
      some ⟨some .done, (none,w), ShiTMStackFrame.extendStacks (fun _ => [])
        (transferred input fuel putInput putFuel xs budget)⟩ := by
    have hz : ShiTMFuel.storeFn [] [] [] [] = fun _ => [] := by
      funext j; cases j <;> rfl
    simpa [S₂, T, transferred, update_left, update_right,
      ShiTMStackFrame.extendStacks, hne, hz] using h₂
  have h := ShiTMFuel.iterTwo (ShiTMSubroutine.run M) _ _ _ _ _
    (ShiTMFuel.iterTwo (ShiTMSubroutine.run M) _ _ _ _ _ h₀' h₁') h₂'
  have ht : (xs.length+1)+(xs.length+1)+(budget+1) = 2*xs.length+budget+3 := by omega
  simpa only [ht] using h

end ShiTMFuelTransfer
