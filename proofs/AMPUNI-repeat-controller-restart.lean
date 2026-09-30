import «AMPUNI-repeat-controller-transfer»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatController

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- If a source round leaves only its output stack occupied, the controller
handoff produces exactly a source input-stack configuration for the next
round. Auxiliary header and counter stacks are tracked separately. -/
theorem transfer_to_canonical_input
    (M : L → Stmt G L (Option Bool × W))
    (entry terminal : L) (input output : K)
    (hio : input ≠ output)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (b : Bool) (n : Nat) (ys : List (G output))
    (S : ∀ j, List (Gam G j)) (v : Option Bool) (w : W)
    (ho : S (.inl output) = ys)
    (hbase : ∀ j : K, j ≠ output → S (.inl j) = [])
    (hs : S (.inr scratch) = [])
    (hh : S (.inr (header b)) = List.replicate n true)
    (hm : S (.inr (header (!b))) = []) :
    ∃ S' : ∀ j, List (Gam G j),
      (ShiTMSubroutine.run
        (machine M entry terminal input output decodeOutput encodeInput))^[
          2 * (ys.length + 1) + n + 2]
        (some ⟨some (phase b .toScratch), (v, w), S⟩) =
          some ⟨some (body (!b) entry), (none, w), S'⟩ ∧
      (∀ j : K,
        S' (.inl j) =
          Function.update (fun _ : K => []) input
            ((List.replicate n true ++ false :: ys.map decodeOutput).map
              encodeInput) j) ∧
      S' (.inr scratch) = [] ∧
      S' (.inr counter) = S (.inr counter) ∧
      S' (.inr (header b)) = [] ∧
      S' (.inr (header (!b))) = List.replicate n true := by
  have hi : S (.inl input) = [] := hbase input hio
  obtain ⟨S', hr, hinput, houtput, hheader, hmirror,
    hscratch, hcounter, hframe⟩ :=
      transfer_to_next M entry terminal input output hio
        decodeOutput encodeInput b n ys S v w ho hs hi hh hm
  refine ⟨S', hr, ?_, hscratch, hcounter, hheader, hmirror⟩
  intro j
  by_cases hji : j = input
  · subst j
    simpa using hinput
  · by_cases hjo : j = output
    · subst j
      simpa [hji] using houtput
    · rw [hframe j hji hjo, hbase j hjo]
      simp [hji]

end ShiTMRepeatController
