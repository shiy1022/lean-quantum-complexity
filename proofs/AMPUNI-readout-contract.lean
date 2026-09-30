import «AMPUNI-readout-run»
import «AMPUNI-fixed-block-payloads»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open Turing Turing.TM2

namespace ShiTMReadout
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMCircuitNormalization

/-- The finite command schedule is exactly the published explicit majority
readout payload, for arbitrary supplied (pairwise distinct) wire indices. -/
theorem programBytes_readCirc {N : Nat} (w₁ w₂ w₃ s : Fin N)
    (h₁₂ : w₁ ≠ w₂) (h₁₃ : w₁ ≠ w₃) (h₂₃ : w₂ ≠ w₃)
    (h₁s : w₁ ≠ s) (h₂s : w₂ ≠ s) (h₃s : w₃ ≠ s) :
    programBytes ![w₁.val, w₂.val, w₃.val, s.val] =
      (stripCircPrefix
        (ShiExplicitCirc.readCirc w₁ w₂ w₃ s h₁₂ h₁₃ h₂₃ h₁s h₂s h₃s)).map bit := by
  rw [readCirc_payload]
  simp [programBytes, program, gates, toff, gateCommands, bytes, unary,
    ShiExplicitCirc.toffGates, ShiBQP.encLayer, ShiBQP.encStr,
    ShiBQP.encInstr, ShiBQP.encNat, bit, List.append_assoc]

/-- A concrete finite machine emits the 111-layer majority payload. Wire
register preparation remains explicit; this theorem makes no assumption that
any verifier output is its terminal wire. -/
theorem typed_readout_run {N : Nat} (w₁ w₂ w₃ s : Fin N)
    (h₁₂ : w₁ ≠ w₂) (h₁₃ : w₁ ≠ w₃) (h₂₃ : w₂ ≠ w₃)
    (h₁s : w₁ ≠ s) (h₂s : w₂ ≠ s) (h₃s : w₃ ≠ s)
    (v : Sig) (S : ∀ j, List (TopGam j))
    (hvalues : ∀ h, S (wire h) =
      List.replicate (![w₁.val, w₂.val, w₃.val, s.val] h) Cell.mark)
    (ht : S scratch = []) :
    ∃ (U : ∀ j, List (TopGam j)) (v' : Sig),
      run^[scheduleCost ![w₁.val, w₂.val, w₃.val, s.val] program + 1]
        (some ⟨some (.dispatch 0), v, S⟩) = some ⟨some .finished, v', U⟩
      ∧ U output =
        ((stripCircPrefix
          (ShiExplicitCirc.readCirc w₁ w₂ w₃ s h₁₂ h₁₃ h₂₃ h₁s h₂s h₃s)).map bit).reverse ++ S output
      ∧ ∀ j, j ≠ output → U j = S j := by
  obtain ⟨U, v', hr, ho, hf⟩ := program_run _ v S hvalues ht
  refine ⟨U, v', hr, ?_, hf⟩
  simpa only [programBytes_readCirc w₁ w₂ w₃ s h₁₂ h₁₃ h₂₃ h₁s h₂s h₃s] using ho

theorem typed_readout_cost_le {N : Nat} (w₁ w₂ w₃ s : Fin N) :
    scheduleCost ![w₁.val, w₂.val, w₃.val, s.val] program + 1 ≤ 726*N+1453 := by
  apply program_cost_le
  intro h
  fin_cases h <;> simp <;> omega

end ShiTMReadout
