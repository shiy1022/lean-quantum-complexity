import «AMPUNI-normalized-circuit-valid-run»
import «AMPUNI-exact-output-contract»
import «AMPUNI-fanout-stage-contract»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open ShiShallow ShiClassQMAAmp ShiClassQMAAmpX
namespace ShiTMNormalizedCircuit
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMCompleteController

private theorem local_ampE_injective (n w a off : Nat)
    (hoff : off + (n + (w + (a + 1))) ≤ 3 * (n + (w + (a + 1)))) :
    Function.Injective (ampE n w a off hoff) := by
  have hs : Function.Injective (ampSig n w a) :=
    (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1.injective
  have he : Function.Injective (ampEmb (n + (w + (a + 1))) off hoff) := by
    intro x y hxy
    have hv := congrArg Fin.val hxy
    change off + x.val = off + y.val at hv
    exact Fin.val_injective (by omega)
  exact hs.comp he

theorem copy0_bytes_typed (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ShiTMPayloadCopyStage.payloadBytes 0 F n =
      (ShiTMCircuitNormalization.stripCircPrefix (embeddedCopy0 F n)).map bit := by
  simpa [ShiTMPayloadCopyStage.payloadBytes, ShiTMPieceController.expectedPieces, embeddedCopy0]
    using ShiTMPayload.copy0_payload_eq_strip n (F.wit n) (F.anc n) (by omega)
      (local_ampE_injective n (F.wit n) (F.anc n) 0 (by omega)) (F.circ n)

theorem copy1_bytes_typed (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ShiTMPayloadCopyStage.payloadBytes 1 F n =
      (ShiTMCircuitNormalization.stripCircPrefix (embeddedCopy1 F n)).map bit := by
  simpa [ShiTMPayloadCopyStage.payloadBytes, ShiTMPieceController.expectedPieces, embeddedCopy1]
    using ShiTMPayload.copy1_payload_eq_strip n (F.wit n) (F.anc n) (by omega)
      (local_ampE_injective n (F.wit n) (F.anc n) (n + (F.wit n + (F.anc n + 1))) (by omega)) (F.circ n)

theorem copy2_bytes_typed (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ShiTMPayloadCopyStage.payloadBytes 2 F n =
      (ShiTMCircuitNormalization.stripCircPrefix (embeddedCopy2 F n)).map bit := by
  simpa [ShiTMPayloadCopyStage.payloadBytes, ShiTMPieceController.expectedPieces, embeddedCopy2]
    using ShiTMPayload.copy2_payload_eq_strip n (F.wit n) (F.anc n) (by omega)
      (local_ampE_injective n (F.wit n) (F.anc n) (2 * (n + (F.wit n + (F.anc n + 1)))) (by omega)) (F.circ n)

/-- The assembled byte stream is the actual amplified circuit encoding. -/
theorem circuitBytes_eq_encoding (F : ShiClassQMA.QMAFamily) (n : Nat) :
    circuitBytes F n = (ShiBQP.encCirc (ampCircX F n)).map bit := by
  have hdepth := ampFamilyX_resource_identities_and_regularity.2.2.2.1 F n
  change (ampCircX F n).length = 3 * (F.circ n).length + 113 at hdepth
  rw [ampCircX_exact_copies] at hdepth
  simp only [List.length_append] at hdepth
  rw [ampCircX_exact_copies, ShiTMCircuitNormalization.six_block_normalization, hdepth]
  simp only [circuitBytes, copy0_bytes_typed, copy1_bytes_typed, copy2_bytes_typed,
    ShiTMFanoutStage.payload_first, ShiTMFanoutStage.payload_second,
    ShiBQP.encNat, List.map_append, List.append_assoc]

/-- Rephrase the verified circuit-run output in the target family's terms. -/
theorem circuit_output_typed (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V U : ∀ k, List (TopGam k))
    (hout : U ShiTMReadout.output = (circuitBytes F n).reverse ++ V ShiTMReadout.output) :
    U ShiTMReadout.output = ((ShiBQP.encCirc (ampCircX F n)).map bit).reverse ++
      V ShiTMReadout.output := by
  simpa only [circuitBytes_eq_encoding] using hout

/-- With the already emitted numeric fields, the output is the exact
amplified family encoding. Input initialization and totalization are separate. -/
theorem family_output_typed (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V U : ∀ k, List (TopGam k))
    (hfields : V ShiTMReadout.output =
      ((ShiBQP.encNat (3 * F.wit n) ++
        ShiBQP.encNat (2 * n + 3 * F.anc n + 3) ++
        ShiBQP.encNat (3 * n + 3 * F.wit n + 3 * F.anc n + 3)).map bit).reverse)
    (hout : U ShiTMReadout.output = (circuitBytes F n).reverse ++ V ShiTMReadout.output) :
    U ShiTMReadout.output =
      ((ShiClassQMAU.encQMAFamilyAt (ampFamilyX F) n).map bit).reverse := by
  rw [hout, circuitBytes_eq_encoding, hfields, amplified_family_encoding_header]
  simp only [List.map_append, List.reverse_append, List.append_assoc]

end ShiTMNormalizedCircuit
