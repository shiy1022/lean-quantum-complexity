import «AMPUNI-repeat-header-copy»
import «AMPUNI-repeat-controller»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatLoaderPrep

variable {K L W : Type} [DecidableEq K]
    {G : K → Type}

/-- Copy the scanned unary length header into scratch and the opposite
header bank. The original header becomes empty, ready to serve as the
loader's target stack, and the source-machine stacks are unchanged. -/
theorem duplicate_length_header
    (M : L → Stmt (ShiTMRepeatController.Gam G) L
      (Option Bool × W))
    (again next : L) (n : Nat)
    (S : ∀ j, List (ShiTMRepeatController.Gam G j))
    (v : Option Bool) (w : W)
    (hm : M again =
      ShiTMRepeatTransfer.duplicate
        (.inr (ShiTMRepeatController.header false))
        (.inr ShiTMRepeatController.scratch)
        (.inr (ShiTMRepeatController.header true))
        id id id again next)
    (hheader : S (.inr (ShiTMRepeatController.header false)) =
      List.replicate n true)
    (hscratch : S (.inr ShiTMRepeatController.scratch) = [])
    (hmirror : S (.inr (ShiTMRepeatController.header true)) = []) :
    ∃ S' : ∀ j, List (ShiTMRepeatController.Gam G j),
      (ShiTMSubroutine.run M)^[n + 1]
        (some ⟨some again, (v, w), S⟩) =
          some ⟨some next, (none, w), S'⟩ ∧
      S' (.inr (ShiTMRepeatController.header false)) = [] ∧
      S' (.inr ShiTMRepeatController.scratch) =
        List.replicate n true ∧
      S' (.inr (ShiTMRepeatController.header true)) =
        List.replicate n true ∧
      S' (.inr ShiTMRepeatController.counter) =
        S (.inr ShiTMRepeatController.counter) ∧
      (∀ j : K, S' (.inl j) = S (.inl j)) := by
  let S' := Function.update
    (Function.update
      (Function.update S
        (.inr (ShiTMRepeatController.header false)) [])
      (.inr ShiTMRepeatController.scratch)
        (List.replicate n true ++
          S (.inr ShiTMRepeatController.scratch)))
    (.inr (ShiTMRepeatController.header true))
      (List.replicate n true ++
        S (.inr (ShiTMRepeatController.header true)))
  have hr := ShiTMRepeatTransfer.duplicate_run M
    (.inr (ShiTMRepeatController.header false))
    (.inr ShiTMRepeatController.scratch)
    (.inr (ShiTMRepeatController.header true))
    id id id again next hm
    (by simp [ShiTMRepeatController.header,
        ShiTMRepeatController.scratch])
    (by simp [ShiTMRepeatController.header])
    (by simp [ShiTMRepeatController.header,
        ShiTMRepeatController.scratch])
    (List.replicate n true) S v w hheader
  refine ⟨S', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [S', List.map_id, List.reverse_replicate] using hr
  · simp [S', ShiTMRepeatController.header,
      ShiTMRepeatController.scratch]
  · have hs : S (.inr (0 : ShiTMRepeatController.Aux)) = [] := by
      simpa [ShiTMRepeatController.scratch] using hscratch
    simp [S', hs, ShiTMRepeatController.header,
      ShiTMRepeatController.scratch]
  · have hs : S (.inr (2 : ShiTMRepeatController.Aux)) = [] := by
      simpa [ShiTMRepeatController.header] using hmirror
    simp [S', hs, ShiTMRepeatController.header,
      ShiTMRepeatController.scratch]
  · simp [S', ShiTMRepeatController.header,
      ShiTMRepeatController.scratch,
      ShiTMRepeatController.counter]
  · intro j
    simp [S']

end ShiTMRepeatLoaderPrep
