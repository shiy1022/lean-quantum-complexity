import «AMPUNI-repeat-controller-body»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatController

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

private theorem headers_distinct (b : Bool) : header (!b) ≠ header b := by
  cases b <;> decide

private theorem header_ne_scratch (b : Bool) : header b ≠ scratch := by
  cases b <;> decide

/-- The four controller phases between successive body calls. -/
theorem transfer_to_next
    (M : L → Stmt G L (Option Bool × W))
    (entry terminal : L) (input output : K)
    (hio : input ≠ output)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (b : Bool) (n : Nat) (ys : List (G output))
    (S : ∀ j, List (Gam G j)) (v : Option Bool) (w : W)
    (ho : S (.inl output) = ys)
    (hs : S (.inr scratch) = [])
    (hi : S (.inl input) = [])
    (hh : S (.inr (header b)) = List.replicate n true)
    (hm : S (.inr (header (!b))) = []) :
    ∃ S' : ∀ j, List (Gam G j),
      (ShiTMSubroutine.run
        (machine M entry terminal input output decodeOutput encodeInput))^[
          2 * (ys.length + 1) + n + 2]
        (some ⟨some (phase b .toScratch), (v, w), S⟩) =
          some ⟨some (body (!b) entry), (none, w), S'⟩ ∧
      S' (.inl input) =
        (List.replicate n true ++ false :: ys.map decodeOutput).map encodeInput ∧
      S' (.inl output) = [] ∧
      S' (.inr (header b)) = [] ∧
      S' (.inr (header (!b))) = List.replicate n true ∧
      S' (.inr scratch) = [] ∧
      S' (.inr counter) = S (.inr counter) ∧
      (∀ j : K, j ≠ input → j ≠ output → S' (.inl j) = S (.inl j)) := by
  let P := machine M entry terminal input output decodeOutput encodeInput
  let bits := ys.map decodeOutput
  let S₁ := Function.update
    (Function.update S (.inl output) []) (.inr scratch) bits.reverse
  have hr₁ :
      (ShiTMSubroutine.run P)^[ys.length + 1]
        (some ⟨some (phase b .toScratch), (v, w), S⟩) =
          some ⟨some (phase b .toInput), (none, w), S₁⟩ := by
    simpa only [List.map_id, hs, List.append_nil, P, bits, S₁] using
      ShiTMRepeatTransfer.move_run P (.inl output) (.inr scratch)
        decodeOutput id (phase b .toScratch) (phase b .toInput)
        (by rfl) (by simp) ys S v w ho
  have hs₁ : S₁ (.inr scratch) = bits.reverse := by simp [S₁]
  have hi₁ : S₁ (.inl input) = [] := by
    simp [S₁, hio, Ne.symm hio, hi]
  let S₂ := Function.update
    (Function.update S₁ (.inr scratch) []) (.inl input)
      (bits.map encodeInput)
  have hr₂ :
      (ShiTMSubroutine.run P)^[bits.reverse.length + 1]
        (some ⟨some (phase b .toInput), (none, w), S₁⟩) =
          some ⟨some (phase b .separator), (none, w), S₂⟩ := by
    simpa only [List.map_id, List.reverse_reverse, hi₁,
      List.append_nil, P, S₂] using
      ShiTMRepeatTransfer.move_run P (.inr scratch) (.inl input)
        id encodeInput (phase b .toInput) (phase b .separator)
        (by rfl) (by simp) bits.reverse S₁ none w hs₁
  let S₃ := Function.update S₂ (.inl input)
    (encodeInput false :: S₂ (.inl input))
  have hr₃ : ShiTMSubroutine.run P
      (some ⟨some (phase b .separator), (none, w), S₂⟩) =
        some ⟨some (phase b .copyHeader), (none, w), S₃⟩ := by
    rfl
  have hh₃ : S₃ (.inr (header b)) = List.replicate n true := by
    simp [S₃, S₂, S₁, hh, header_ne_scratch b,
      Ne.symm (header_ne_scratch b)]
  let S₄ := Function.update
      (Function.update (Function.update S₃ (.inr (header b)) [])
        (.inl input)
        ((List.replicate n true).map encodeInput ++ S₃ (.inl input)))
      (.inr (header (!b)))
        (List.replicate n true ++ S₃ (.inr (header (!b))))
  have hr₄ :
      (ShiTMSubroutine.run P)^[(List.replicate n true).length + 1]
        (some ⟨some (phase b .copyHeader), (none, w), S₃⟩) =
          some ⟨some (body (!b) entry), (none, w), S₄⟩ := by
    simpa only [List.map_id, List.reverse_replicate, P, S₄] using
      ShiTMRepeatTransfer.duplicate_run P
        (.inr (header b)) (.inl input) (.inr (header (!b)))
        id encodeInput id (phase b .copyHeader) (body (!b) entry)
        (by rfl) (by simp) (by simp [headers_distinct b]) (by simp)
        (List.replicate n true) S₃ none w hh₃
  have hi₂ : S₂ (.inl input) = bits.map encodeInput := by simp [S₂]
  have ho₂ : S₂ (.inl output) = [] := by
    simp [S₂, S₁, hio, Ne.symm hio]
  have hm₃ : S₃ (.inr (header (!b))) = [] := by
    simp [S₃, S₂, S₁, hm, header_ne_scratch (!b),
      Ne.symm (header_ne_scratch (!b))]
  have hinput : S₄ (.inl input) =
      (List.replicate n true ++ false :: bits).map encodeInput := by
    simp [S₄, S₃, hi₂, List.map_append, List.map_cons,
      List.append_assoc]
  have houtput : S₄ (.inl output) = [] := by
    simp [S₄, S₃, ho₂, hio, Ne.symm hio]
  have hheader : S₄ (.inr (header b)) = [] := by
    simp [S₄, headers_distinct b, Ne.symm (headers_distinct b)]
  have hmirror : S₄ (.inr (header (!b))) = List.replicate n true := by
    simp [S₄, hm₃]
  have hscratch : S₄ (.inr scratch) = [] := by
    simp [S₄, S₃, S₂, S₁, hs, header_ne_scratch b,
      header_ne_scratch (!b), Ne.symm (header_ne_scratch b),
      Ne.symm (header_ne_scratch (!b))]
  have hcounter : S₄ (.inr counter) = S (.inr counter) := by
    cases b <;> simp [S₄, S₃, S₂, S₁, counter, scratch, header]
  have hframe (j : K) (hji : j ≠ input) (hjo : j ≠ output) :
      S₄ (.inl j) = S (.inl j) := by
    simp [S₄, S₃, S₂, S₁, hji, hjo, Ne.symm hji, Ne.symm hjo]
  refine ⟨S₄, ?_, hinput, houtput, hheader, hmirror,
    hscratch, hcounter, hframe⟩
  have h₁₂ :
      (ShiTMSubroutine.run P)^[ys.length + 1 + (bits.reverse.length + 1)]
        (some ⟨some (phase b .toScratch), (v, w), S⟩) =
          some ⟨some (phase b .separator), (none, w), S₂⟩ := by
    rw [show ys.length + 1 + (bits.reverse.length + 1) =
      (bits.reverse.length + 1) + (ys.length + 1) by omega,
      Function.iterate_add_apply, hr₁, hr₂]
  have h₁₂₃ :
      (ShiTMSubroutine.run P)^[ys.length + 1 +
          (bits.reverse.length + 1) + 1]
        (some ⟨some (phase b .toScratch), (v, w), S⟩) =
          some ⟨some (phase b .copyHeader), (none, w), S₃⟩ := by
    rw [show ys.length + 1 + (bits.reverse.length + 1) + 1 =
      1 + (ys.length + 1 + (bits.reverse.length + 1)) by omega,
      Function.iterate_add_apply, h₁₂]
    exact hr₃
  rw [show 2 * (ys.length + 1) + n + 2 =
      ((List.replicate n true).length + 1) +
        (ys.length + 1 + (bits.reverse.length + 1) + 1) by
          simp [bits]; omega,
    Function.iterate_add_apply, h₁₂₃, hr₄]

end ShiTMRepeatController
