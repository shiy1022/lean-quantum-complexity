import «AMPUNI-fanout-stage-bounds»
import «AMPUNI-fanout-contract»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2

namespace ShiTMFanoutStage
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMCircuitNormalization
open ShiClassQMAAmpX
open ShiTMFanoutPrepare (port scratch Retained)

theorem payload_first (n w a : Nat) :
    payload false n w a = (stripCircPrefix (ampFan2X n w a)).map bit := by
  exact ShiTMFanout.fanout2_bytes n w a

theorem payload_second (n w a : Nat) :
    payload true n w a = (stripCircPrefix (ampFan3X n w a)).map bit := by
  exact ShiTMFanout.fanout3_bytes n w a

/-- An executable two-fanout stage for a verifier family, including all
register preparation, sequencing, and cleanup. Its input circuit and archive
are framed; no precomputed target-base registers are assumed. -/
theorem family_stage_run (F : ShiClassQMA.QMAFamily) (n : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hret : Retained n (F.wit n) (F.anc n) S)
    (ht : S scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[stageCost n (F.wit n) (F.anc n) S]
        (some ⟨some (prepLabel false (.clear 0)), v, S⟩) =
        some ⟨some finished, none, U⟩
      ∧ U (port 0) = [] ∧ U (port 1) = [] ∧ U (port 2) = []
      ∧ U scratch = []
      ∧ U output =
        ((stripCircPrefix (ampFan2X n (F.wit n) (F.anc n)) ++
          stripCircPrefix (ampFan3X n (F.wit n) (F.anc n))).map bit).reverse ++ S output
      ∧ Retained n (F.wit n) (F.anc n) U
      ∧ ∀ j, Stable j → U j = S j := by
  obtain ⟨U, hr, h0, h1, h2, hs, ho, hretU, hf⟩ :=
    stage_run n (F.wit n) (F.anc n) v S hret ht
  refine ⟨U, hr, h0, h1, h2, hs, ?_, hretU, hf⟩
  simpa only [payload_first, payload_second, List.map_append] using ho

/-- The concrete stage's complete runtime is quadratic in the actual retained
Boolean input length, plus the length of any old work-register contents. -/
theorem family_stage_cost_le (F : ShiClassQMA.QMAFamily) (n : Nat)
    (S : ∀ j, List (TopGam j)) :
    let L := (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).length
    stageCost n (F.wit n) (F.anc n) S ≤ workSize S + 79*L*L := by
  apply stageCost_le
  simp only [ShiClassQMAU.encQMAFamilyAt, ShiBQP.encNat,
    List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

end ShiTMFanoutStage
