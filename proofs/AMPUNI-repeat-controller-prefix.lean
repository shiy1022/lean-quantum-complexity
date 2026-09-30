import «AMPUNI-repeat-controller-transfer»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatController

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

private theorem headers_distinct (b : Bool) : header (!b) ≠ header b := by
  cases b <;> decide

/-- Restore the unary length prefix after a startup scan, and switch to the
other header bank before the first source-machine call. -/
theorem prefix_to_body
    (M : L → Stmt G L (Option Bool × W))
    (entry terminal : L) (input output : K)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (b : Bool) (n : Nat) (code : List (G input))
    (S : ∀ j, List (Gam G j)) (v : Option Bool) (w : W)
    (hi : S (.inl input) = code)
    (hh : S (.inr (header b)) = List.replicate n true)
    (hm : S (.inr (header (!b))) = []) :
    ∃ S' : ∀ j, List (Gam G j),
      (ShiTMSubroutine.run
        (machine M entry terminal input output decodeOutput encodeInput))^[n + 2]
        (some ⟨some (phase b .separator), (v, w), S⟩) =
          some ⟨some (body (!b) entry), (none, w), S'⟩ ∧
      S' (.inl input) =
        (List.replicate n true).map encodeInput ++ encodeInput false :: code ∧
      S' (.inr (header b)) = [] ∧
      S' (.inr (header (!b))) = List.replicate n true ∧
      S' (.inr scratch) = S (.inr scratch) ∧
      S' (.inr counter) = S (.inr counter) ∧
      (∀ j : K, j ≠ input → S' (.inl j) = S (.inl j)) := by
  let P := machine M entry terminal input output decodeOutput encodeInput
  let S₁ := Function.update S (.inl input) (encodeInput false :: code)
  have hr₁ : ShiTMSubroutine.run P
      (some ⟨some (phase b .separator), (v, w), S⟩) =
        some ⟨some (phase b .copyHeader), (v, w), S₁⟩ := by
    simp [ShiTMSubroutine.run, P, machine, phase, step, stepAux, S₁, hi]
  have hh₁ : S₁ (.inr (header b)) = List.replicate n true := by
    simp [S₁, hh]
  let S₂ := Function.update
      (Function.update (Function.update S₁ (.inr (header b)) [])
        (.inl input)
        ((List.replicate n true).map encodeInput ++ S₁ (.inl input)))
      (.inr (header (!b)))
        (List.replicate n true ++ S₁ (.inr (header (!b))))
  have hr₂ :
      (ShiTMSubroutine.run P)^[(List.replicate n true).length + 1]
        (some ⟨some (phase b .copyHeader), (v, w), S₁⟩) =
          some ⟨some (body (!b) entry), (none, w), S₂⟩ := by
    simpa only [List.map_id, List.reverse_replicate, P, S₂] using
      ShiTMRepeatTransfer.duplicate_run P
        (.inr (header b)) (.inl input) (.inr (header (!b)))
        id encodeInput id (phase b .copyHeader) (body (!b) entry)
        (by rfl) (by simp) (by simp [headers_distinct b]) (by simp)
        (List.replicate n true) S₁ v w hh₁
  have hinput : S₂ (.inl input) =
      (List.replicate n true).map encodeInput ++ encodeInput false :: code := by
    simp [S₂, S₁, hi]
  have hheader : S₂ (.inr (header b)) = [] := by
    simp [S₂, headers_distinct b, Ne.symm (headers_distinct b)]
  have hmirror : S₂ (.inr (header (!b))) = List.replicate n true := by
    simp [S₂, S₁, hm]
  have hscratch : S₂ (.inr scratch) = S (.inr scratch) := by
    cases b <;> simp [S₂, S₁, header, scratch]
  have hcounter : S₂ (.inr counter) = S (.inr counter) := by
    cases b <;> simp [S₂, S₁, header, counter]
  have hother (j : K) (hj : j ≠ input) :
      S₂ (.inl j) = S (.inl j) := by
    simp [S₂, S₁, hj]
  refine ⟨S₂, ?_, hinput, hheader, hmirror,
    hscratch, hcounter, hother⟩
  rw [show n + 2 = ((List.replicate n true).length + 1) + 1 by simp,
    Function.iterate_add_apply]
  change (ShiTMSubroutine.run P)^[(List.replicate n true).length + 1]
    (ShiTMSubroutine.run P
      (some ⟨some (phase b .separator), (v, w), S⟩)) =
    some ⟨some (body (!b) entry), (none, w), S₂⟩
  rw [hr₁, hr₂]

end ShiTMRepeatController
