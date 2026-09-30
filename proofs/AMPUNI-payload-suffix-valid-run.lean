import «AMPUNI-payload-copy-valid-run»
import «AMPUNI-payload-suffix-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMPayloadSuffix
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a+b] x = z := by
  rw [show a+b = b+a by omega, Function.iterate_add_apply, hxy, hyz]

/-- Starting after the first copy, emit both replayed copy payloads and
prepared majority readout in one finite controller. -/
theorem valid_suffix_run
    (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V : ∀ k, List (TopGam k))
    (hsource : V ShiTMReplayReload.source = [])
    (hscratch : V ShiTMReplayReload.scratch = [])
    (hmarks : V ShiTMReplayMarkSplit.marks = [])
    (harchive : V ShiTMReplayMarkSplit.archive =
      List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
        ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse)
    (hret : Retained n (F.wit n) (F.anc n) V)
    (h10 : V (.inl (.inl (10 : Fin 14))) = [])
    (h4 : V (.inl (.inl (4 : Fin 14))) = [Cell.delim])
    (h6 : V (.inl (.inl (6 : Fin 14))) = [])
    (h7 : V (.inl (.inl (7 : Fin 14))) = [])
    (h12 : V (.inl (.inl (12 : Fin 14))) = [])
    (hc0 : V (.inl (.inr (0 : Fin 2))) = [])
    (hc1 : V (.inl (.inr (1 : Fin 2))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v : Sig) (steps : Nat),
      run^[steps] (some ⟨some (entry false), none, V⟩) =
        some ⟨some (readoutLabel (ShiTMPreparedReadout.emitLabel .finished)), v, U⟩
      ∧ U ShiTMReadout.output =
        (ShiTMPayloadCopyStage.payloadBytes 1 F n ++
          ShiTMPayloadCopyStage.payloadBytes 2 F n ++
          (ShiTMCircuitNormalization.stripCircPrefix
            (ShiClassQMAAmpX.ampReadX n (F.wit n) (F.anc n) (F.out n))).map bit).reverse ++
          V ShiTMReadout.output := by
  obtain ⟨Q, t1, hr1, ho1, hs1, hm1, ht1, h101, ha1,
      h41, h61, h71, h121, hc01, hc11, hret1⟩ :=
    ShiTMPayloadCopyStage.valid_copy_run 1 F n V
      hsource hscratch hmarks harchive hret h10 h4 h6 h7 h12 hc0 hc1
  obtain ⟨R, t2, hr2, ho2, hs2, hm2, ht2, h102, ha2,
      h42, h62, h72, h122, hc02, hc12, hret2⟩ :=
    ShiTMPayloadCopyStage.valid_copy_run 2 F n Q
      hs1 ht1 hm1 (ha1.trans harchive) hret1 h101 h41 h61 h71 h121 hc01 hc11
  obtain ⟨A, B, C, U, vu, hr3, ho3⟩ :=
    ShiTMPreparedReadout.prepared_readout_run n (F.wit n) (F.anc n) (F.out n)
      ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse
      none R hret2 (ha2.trans (ha1.trans harchive)) ht2
  have h1 := copy_run false t1 V Q hr1
  have j1 := iterTwo run _ _ _ _ _ h1 (copy_handoff false Q)
  have h2 := iterTwo run _ _ _ _ _ j1 (copy_run true t2 Q R hr2)
  have j2 := iterTwo run _ _ _ _ _ h2 (copy_handoff true R)
  have h3 := iterTwo run _ _ _ _ _ j2 (readout_run _ vu R U hr3)
  refine ⟨U, vu, _, h3, ?_⟩
  change Q ShiTMReadout.output = (ShiTMPayloadCopyStage.payloadBytes 1 F n).reverse ++
    V ShiTMReadout.output at ho1
  change R ShiTMReadout.output = (ShiTMPayloadCopyStage.payloadBytes 2 F n).reverse ++
    Q ShiTMReadout.output at ho2
  rw [ho3, ho2, ho1]
  simp only [List.reverse_append, List.append_assoc]

end ShiTMPayloadSuffix
