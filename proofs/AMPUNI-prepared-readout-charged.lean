import «AMPUNI-copy-stage-stack-bounds»
import «AMPUNI-runtime-charge»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open Turing Turing.TM2
namespace ShiTMPreparedReadout
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMStackGrowth ShiTMRetainedPayload

private theorem retained_stable (copy : Fin 3) (h : Fin 4) :
    ShiTMReadoutCopy.Stable copy (.inr h) := by
  simp [ShiTMReadoutCopy.Stable, ShiTMReadoutCopy.core, ShiTMReadoutLookup.core,
    ShiTMReadoutCopy.destination, ShiTMReadoutLookup.destination, ShiTMReadout.wire]

private theorem retained_after (copy : Fin 3) (n w a : Nat)
    (S U : ∀ k, List (TopGam k)) (hret : ShiTMPieceController.Retained n w a S)
    (hf : ∀ k, ShiTMReadoutCopy.Stable copy k → U k = S k) :
    ShiTMPieceController.Retained n w a U :=
  ⟨(hf _ (retained_stable copy 0)).trans hret.1,
    (hf _ (retained_stable copy 1)).trans hret.2.1,
    (hf _ (retained_stable copy 2)).trans hret.2.2⟩

private theorem output_stable (copy : Fin 3) : ShiTMReadoutCopy.Stable copy ShiTMReadout.output :=
  ⟨by decide, by decide, by decide, by decide,
    Ne.symm (ShiTMReadoutCopy.destination_ne_13 copy), by decide⟩

theorem prepared_readout_run_charged :
    ∃ K : Nat, 1 ≤ K ∧ ∀ (F : ShiClassQMA.QMAFamily) (n : Nat)
    (tail : List Cell) (v : Sig) (S : ∀ k, List (TopGam k))
    (hret : ShiTMPieceController.Retained n (F.wit n) (F.anc n) S)
    (ha : S ShiTMReadoutIndexLoad.archive = List.replicate (F.out n).val Cell.mark ++ Cell.mirrorEnd :: tail)
    (h3 : S ShiTMReadout.scratch = []),
    ∃ (A B C U : ∀ k, List (TopGam k)) (v' : Sig),
      run^[stageCost n (F.wit n) (F.anc n) (F.out n).val S A B C] (some ⟨some (entry 0), v, S⟩) =
        some ⟨some (emitLabel .finished), v', U⟩
      ∧ U ShiTMReadout.output =
        ((ShiTMCircuitNormalization.stripCircPrefix (ShiClassQMAAmpX.ampReadX n (F.wit n) (F.anc n) (F.out n))).map bit).reverse ++
          S ShiTMReadout.output
      ∧ stageCost n (F.wit n) (F.anc n) (F.out n).val S A B C +
          size U + (inputLength F n + 1) ≤ K * (size S + (inputLength F n + 1)) := by
  classical
  obtain ⟨growth, hg⟩ := finite_growth machine
  let k := 1 + 4000 * (growth + 1)
  refine ⟨k*(k*(k*(k*k))), by
    have hk : 1 ≤ k := by dsimp [k]; omega
    exact Nat.mul_le_mul hk (Nat.mul_le_mul hk (Nat.mul_le_mul hk (Nat.mul_le_mul hk hk))), ?_⟩
  intro F n tail v S hret ha h3
  obtain ⟨va, A, hrA, hvA, _, h3A, hwA, hfA⟩ :=
    ShiTMReadoutCopy.prepare_readout_operand 0 n (F.wit n) (F.anc n) (F.out n) tail v S hret ha h3
  obtain ⟨vb, B, hrB, hvB, _, h3B, hwB, hfB⟩ :=
    ShiTMReadoutCopy.prepare_readout_operand 1 n (F.wit n) (F.anc n) (F.out n) tail va A
      (retained_after 0 n (F.wit n) (F.anc n) S A hret hfA)
      ((hfA _ (retained_stable 0 3)).trans ha) h3A
  obtain ⟨vc, C, hrC, hvC, _, h3C, hwC, hfC⟩ :=
    ShiTMReadoutCopy.prepare_readout_operand 2 n (F.wit n) (F.anc n) (F.out n) tail vb B
      (retained_after 1 n (F.wit n) (F.anc n) A B (retained_after 0 n (F.wit n) (F.anc n) S A hret hfA) hfB)
      ((hfB _ (retained_stable 1 3)).trans ((hfA _ (retained_stable 0 3)).trans ha)) h3B
  have hretC := retained_after 2 n (F.wit n) (F.anc n) B C
    (retained_after 1 n (F.wit n) (F.anc n) A B (retained_after 0 n (F.wit n) (F.anc n) S A hret hfA) hfB) hfC
  obtain ⟨D, hrD, hvD, _, h3D, hfD⟩ := ShiTMReadoutScratch.prepare_run n (F.wit n) (F.anc n) vc C
    (by simpa [ShiTMFanoutPrepare.Retained, ShiTMFanoutPrepare.source, ShiTMPieceController.Retained] using hretC) h3C
  have hvalues : ∀ h, D (ShiTMReadout.wire h) =
      List.replicate (ShiTMReadout.amplifierValues n (F.wit n) (F.anc n) (F.out n).val h) Cell.mark := by
    intro h
    fin_cases h
    · exact (hfD _ (by simp [ShiTMReadoutScratch.Stable, ShiTMReadoutScratch.core,
        ShiTMReadout.wire])).trans
        ((hwC 0 (by decide)).trans ((hwB 0 (by decide)).trans hvA))
    · exact (hfD _ (by simp [ShiTMReadoutScratch.Stable, ShiTMReadoutScratch.core,
        ShiTMReadout.wire])).trans ((hwC 1 (by decide)).trans hvB)
    · exact (hfD _ (by simp [ShiTMReadoutScratch.Stable, ShiTMReadoutScratch.core,
        ShiTMReadout.wire])).trans hvC
    · change D (ShiTMReadoutScratch.core 7) =
        List.replicate (ShiTMReadoutScratch.value n (F.wit n) (F.anc n)) Cell.mark
      exact hvD
  obtain ⟨U, vu, hrU, hout, _⟩ := ShiTMReadout.amplifier_readout_run n (F.wit n) (F.anc n) (F.out n) none D hvalues h3D
  have hDoutput : D ShiTMReadout.output = S ShiTMReadout.output := by
    rw [hfD _ (by simp [ShiTMReadoutScratch.Stable, ShiTMReadoutScratch.core, ShiTMReadout.wire, ShiTMReadout.output]), hfC _ (output_stable 2), hfB _ (output_stable 1), hfA _ (output_stable 0)]
  have jump (copy : Fin 3) (var : Sig) (T : ∀ k, List (TopGam k)) :
      run^[1] (some ⟨some (copyLabel copy (ShiTMReadoutCopy.lookupLabel .finished)), var, T⟩) =
        some ⟨some (afterCopy copy), var, T⟩ := by
    simp [run, ShiTMSubroutine.run, machine, copyLabel, step, stepAux]
  have jA := jump 0 va A
  have jB := jump 1 vb B
  have jC := jump 2 vc C
  have jD : run^[1] (some ⟨some (scratchLabel (ShiTMReadoutScratch.localLabel 2)), none, D⟩) =
      some ⟨some (emitLabel (.dispatch 0)), none, D⟩ := by
    simp [run, ShiTMSubroutine.run, machine, scratchLabel, step, stepAux]
  have h0 := copy_run 0 _ _ _ _ _ hrA
  have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ h0 jA
  have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 (copy_run 1 _ _ _ _ _ hrB)
  have h4 := ShiTMFanout.iterTwo run _ _ _ _ _ h2 jB
  have h5 := ShiTMFanout.iterTwo run _ _ _ _ _ h4 (copy_run 2 _ _ _ _ _ hrC)
  have h6 := ShiTMFanout.iterTwo run _ _ _ _ _ h5 jC
  have h7 := ShiTMFanout.iterTwo run _ _ _ _ _ h6 (scratch_run _ _ _ _ _ hrD)
  have h8 := ShiTMFanout.iterTwo run _ _ _ _ _ h7 jD
  have h9 := ShiTMFanout.iterTwo run _ _ _ _ _ h8 (emit_run _ _ _ _ _ hrU)
  have rb := ShiTMFanout.iterTwo run _ _ _ _ _ (copy_run 1 _ _ _ _ _ hrB) jB
  have rc := ShiTMFanout.iterTwo run _ _ _ _ _ (copy_run 2 _ _ _ _ _ hrC) jC
  have rd := ShiTMFanout.iterTwo run _ _ _ _ _ (scratch_run _ _ _ _ _ hrD) jD
  have re := emit_run _ _ _ _ _ hrU
  have ca := run_charge_le machine growth hg _ _ _ (inputLength F n+1) 4000 h1 (by
    have hc := ShiTMCopyStageCost.readoutCopyCost_le_size 0 F n S
    change _ ≤ 4000*(size S+(inputLength F n+1))
    omega)
  have cb := run_charge_le machine growth hg _ _ _ (inputLength F n+1) 4000 rb (by
    have hc := ShiTMCopyStageCost.readoutCopyCost_le_size 1 F n A
    change _ ≤ 4000*(size A+(inputLength F n+1))
    omega)
  have cc := run_charge_le machine growth hg _ _ _ (inputLength F n+1) 4000 rc (by
    have hc := ShiTMCopyStageCost.readoutCopyCost_le_size 2 F n B
    change _ ≤ 4000*(size B+(inputLength F n+1))
    omega)
  have cd := run_charge_le machine growth hg _ _ _ (inputLength F n+1) 4000 rd (by
    have hc := ShiTMCopyStageCost.readoutScratchCost_le_size F n C
    change _ ≤ 4000*(size C+(inputLength F n+1))
    omega)
  have ce := run_charge_le machine growth hg _ _ _ (inputLength F n+1) 4000 re (by
    have hc := ShiTMReadout.family_readout_cost_le F n
    change _ ≤ 3631 * inputLength F n at hc
    omega)
  have cab := charge_comp ca cb (by omega)
  have cabc := charge_comp cab cc (by omega)
  have cabcd := charge_comp cabc cd (by omega)
  have cabcde := charge_comp cabcd ce (by omega)
  refine ⟨A, B, C, U, vu, h9, ?_, ?_⟩
  · rw [hout, hDoutput]
  · simpa only [stageCost, Nat.add_assoc] using cabcde

end ShiTMPreparedReadout
