import «AMPUNI-repeat-loop-bank»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatController

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- One counter token pays for exactly one more body call. The controller
returns to a canonical source input-stack layout with the other header bank
active and one fewer token. -/
theorem terminal_to_next
    (M : L → Stmt G L (Option Bool × W))
    (entry terminal : L) (input output : K)
    (hio : input ≠ output)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (b : Bool) (n q : Nat) (ys : List (G output))
    (S : ∀ j, List (Gam G j)) (v : Option Bool) (w : W)
    (ho : S (.inl output) = ys)
    (hbase : ∀ j : K, j ≠ output → S (.inl j) = [])
    (haux : ∀ h : Aux, S (.inr h) = bank b n (q + 1) h) :
    ∃ S' : ∀ j, List (Gam G j),
      (ShiTMSubroutine.run
        (machine M entry terminal input output decodeOutput encodeInput))^[
          1 + 2 * (ys.length + 1) + n + 2]
        (some ⟨some (body b terminal), (v, w), S⟩) =
          some ⟨some (body (!b) entry), (none, w), S'⟩ ∧
      (∀ j : K,
        S' (.inl j) =
          Function.update (fun _ : K => []) input
            ((List.replicate n true ++ false :: ys.map decodeOutput).map
              encodeInput) j) ∧
      (∀ h : Aux, S' (.inr h) = bank (!b) n q h) := by
  let P := machine M entry terminal input output decodeOutput encodeInput
  let S₁ := Function.update S (.inr counter) (List.replicate q true)
  have hc : S (.inr counter) = true :: List.replicate q true := by
    rw [haux, bank_counter]
    rfl
  have hterm : ShiTMSubroutine.run P
      (some ⟨some (body b terminal), (v, w), S⟩) =
        some ⟨some (phase b .toScratch), (some true, w), S₁⟩ := by
    exact terminal_more M entry terminal input output decodeOutput
      encodeInput b S v w true (List.replicate q true) hc
  have ho₁ : S₁ (.inl output) = ys := by simp [S₁, ho]
  have hbase₁ : ∀ j : K, j ≠ output → S₁ (.inl j) = [] := by
    intro j hj
    simpa [S₁] using hbase j hj
  have hs₁ : S₁ (.inr scratch) = [] := by
    simpa [S₁, scratch, counter, bank] using haux 0
  have hh₁ : S₁ (.inr (header b)) = List.replicate n true := by
    cases b with
    | false => simpa [S₁, bank, header, counter] using haux 1
    | true => simpa [S₁, bank, header, counter] using haux 2
  have hm₁ : S₁ (.inr (header (!b))) = [] := by
    cases b with
    | false =>
        change S₁ (.inr 2) = []
        simpa [S₁, bank, counter] using haux 2
    | true =>
        change S₁ (.inr 1) = []
        simpa [S₁, bank, counter] using haux 1
  obtain ⟨S₂, htransfer, hcanon, hscratch, hcounter,
      hheader, hmirror⟩ :=
    transfer_to_canonical_input M entry terminal input output hio
      decodeOutput encodeInput b n ys S₁ (some true) w
      ho₁ hbase₁ hs₁ hh₁ hm₁
  have haux₂ (h : Aux) : S₂ (.inr h) = bank (!b) n q h := by
    fin_cases h
    · simpa [bank, scratch] using hscratch
    · cases b with
      | false =>
          change S₂ (.inr 1) = []
          change S₂ (.inr 1) = [] at hheader
          exact hheader
      | true =>
          change S₂ (.inr 1) = List.replicate n true
          change S₂ (.inr 1) = List.replicate n true at hmirror
          exact hmirror
    · cases b with
      | false =>
          change S₂ (.inr 2) = List.replicate n true
          change S₂ (.inr 2) = List.replicate n true at hmirror
          exact hmirror
      | true =>
          change S₂ (.inr 2) = []
          change S₂ (.inr 2) = [] at hheader
          exact hheader
    · have hc₁ : S₁ (.inr counter) = List.replicate q true := by
        simp [S₁]
      simpa [bank, counter, hc₁] using hcounter.trans hc₁
  refine ⟨S₂, ?_, hcanon, haux₂⟩
  rw [show 1 + 2 * (ys.length + 1) + n + 2 =
      (2 * (ys.length + 1) + n + 2) + 1 by omega,
    Function.iterate_add_apply]
  change (ShiTMSubroutine.run P)^[2 * (ys.length + 1) + n + 2]
    (ShiTMSubroutine.run P
      (some ⟨some (body b terminal), (v, w), S⟩)) = _
  rw [hterm, htransfer]

end ShiTMRepeatController
