import «AMPUNI-normalized-circuit-valid-run»
import «AMPUNI-payload-suffix-charged»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open Turing Turing.TM2
namespace ShiTMNormalizedCircuit
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController ShiTMStackGrowth
open ShiTMRetainedPayload
open ShiTMPayloadSuffix (reserve)

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a+b] x = z := by
  rw [show a+b = b+a by omega, Function.iterate_add_apply, hxy, hyz]

/-- A single finite controller emits the global header, both fanouts, all
three local-copy payloads and prepared majority readout from retained data. -/
theorem valid_circuit_run_charged :
    ∃ K : Nat, 1 ≤ K ∧ ∀ (F : ShiClassQMA.QMAFamily) (n : Nat) (v : Sig)
    (V : ∀ k, List (TopGam k))
    (hsource : V ShiTMReplayReload.source = (ShiBQP.encCirc (F.circ n)).map bit)
    (hscratch : V ShiTMReplayReload.scratch = [])
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
    (hc1 : V (.inl (.inr (1 : Fin 2))) = []),
    ∃ (U : ∀ k, List (TopGam k)) (vu : Sig) (steps : Nat),
      run^[steps] (some ⟨some (prefixLabel (.inl false)), v, V⟩) =
        some ⟨some (suffixLabel (ShiTMPayloadSuffix.readoutLabel
          (ShiTMPreparedReadout.emitLabel .finished))), vu, U⟩
      ∧ U ShiTMReadout.output = (circuitBytes F n).reverse ++ V ShiTMReadout.output
      ∧ steps+size U+reserve F n ≤ K*(size V+reserve F n) := by
  classical
  obtain ⟨growth, hg⟩ := finite_growth machine
  obtain ⟨ks, hks, suffix⟩ := ShiTMPayloadSuffix.valid_suffix_run_charged
  let k := 1+1500*(growth+1)
  refine ⟨ks*(k*k), by
    have hk : 1 ≤ k := by dsimp [k]; omega
    exact Nat.mul_le_mul hks (Nat.mul_le_mul hk hk), ?_⟩
  intro F n v V hsource hscratch harchive hret h10 h4 h6 h7 h12 hc0 hc1
  have hs : V ShiTMGlobalFanoutPrefix.source =
      (List.replicate (F.circ n).length true ++ [false]).map bit ++
        (ShiTMCircuitNormalization.stripCircPrefix (F.circ n)).map bit := by
    simpa [ShiTMCircuitNormalization.stripCircPrefix_eq_payload,
      ShiTMCircuitNormalization.payload, ShiBQP.encCirc, ShiBQP.encStr,
      ShiBQP.encNat, List.map_append] using hsource
  obtain ⟨P, hp, hps, hpc, hpo, hp0, hp1, hp2, hp3, hpret, hpf⟩ :=
    ShiTMGlobalFanoutPrefix.prefix_run n (F.wit n) (F.anc n) (F.circ n).length
      ((ShiTMCircuitNormalization.stripCircPrefix (F.circ n)).map bit) v V
      (by simpa [ShiTMFanoutPrepare.Retained, ShiTMFanoutPrepare.source, Retained] using hret)
      hs hscratch
  have hpc0 : P (.inl (.inr (0 : Fin 2))) = List.replicate (F.circ n).length Cell.mark := by
    change P (.inl (.inr (0 : Fin 2))) =
      List.replicate (F.circ n).length Cell.mark ++ V (.inl (.inr (0 : Fin 2))) at hpc
    simpa only [hc0, List.append_nil] using hpc
  have hretP : Retained n (F.wit n) (F.anc n) P := by
    simpa [ShiTMFanoutPrepare.Retained, ShiTMFanoutPrepare.source, Retained] using hpret
  have hp4 : P (.inl (.inl (4 : Fin 14))) = [Cell.delim] :=
    (hpf _ (by simp [ShiTMFanoutStage.Stable, ShiTMFanoutPrepare.Stable, ShiTMFanoutPrepare.port, ShiTMFanout.port, ShiTMFanoutStage.output]) (by decide) (by decide)).trans h4
  have hp6 : P (.inl (.inl (6 : Fin 14))) = [] :=
    (hpf _ (by simp [ShiTMFanoutStage.Stable, ShiTMFanoutPrepare.Stable, ShiTMFanoutPrepare.port, ShiTMFanout.port, ShiTMFanoutStage.output]) (by decide) (by decide)).trans h6
  have hp7 : P (.inl (.inl (7 : Fin 14))) = [] :=
    (hpf _ (by simp [ShiTMFanoutStage.Stable, ShiTMFanoutPrepare.Stable, ShiTMFanoutPrepare.port, ShiTMFanout.port, ShiTMFanoutStage.output]) (by decide) (by decide)).trans h7
  have hp10 : P (.inl (.inl (10 : Fin 14))) = [] :=
    (hpf _ (by simp [ShiTMFanoutStage.Stable, ShiTMFanoutPrepare.Stable, ShiTMFanoutPrepare.port, ShiTMFanout.port, ShiTMFanoutStage.output]) (by decide) (by decide)).trans h10
  have hp12 : P (.inl (.inl (12 : Fin 14))) = [] :=
    (hpf _ (by simp [ShiTMFanoutStage.Stable, ShiTMFanoutPrepare.Stable, ShiTMFanoutPrepare.port, ShiTMFanout.port, ShiTMFanoutStage.output]) (by decide) (by decide)).trans h12
  have hpc1 : P (.inl (.inr (1 : Fin 2))) = [] :=
    (hpf _ (by simp [ShiTMFanoutStage.Stable, ShiTMFanoutPrepare.Stable, ShiTMFanoutPrepare.port, ShiTMFanout.port, ShiTMFanoutStage.output]) (by decide) (by decide)).trans hc1
  have hpa : P ShiTMReplayReload.archive = V ShiTMReplayReload.archive :=
    hpf _ (by simp [ShiTMFanoutStage.Stable, ShiTMFanoutPrepare.Stable, ShiTMFanoutPrepare.port, ShiTMFanout.port, ShiTMFanoutStage.output]) (by decide) (by decide)
  obtain ⟨Q, tq, hq, hqo, hqs, hqm, hqt, hq10, hqa,
      hq4, hq6, hq7, hq12, hqc0, hqc1, hqret, hbq⟩ :=
    ShiTMFirstPayload.valid_first_run_bounded F n P hps hp3 hp0 hretP hp10 hp4 hp6 hp7 hp12 hpc0 hpc1
  obtain ⟨U, vu, tu, hu, huo, hbu⟩ := suffix F n Q
    hqs hqt hqm ((hqa.trans hpa).trans harchive) hqret hq10 hq4 hq6 hq7 hq12 hqc0 hqc1
  have r0 := prefix_run _ v V P hp
  have j0 := iterTwo run _ _ _ _ _ r0 (prefix_handoff P)
  have r1 := iterTwo run _ _ _ _ _ j0 (first_run tq P Q hq)
  have j1 := iterTwo run _ _ _ _ _ r1 (first_handoff Q)
  have r2 := iterTwo run _ _ _ _ _ j1 (suffix_run tu vu Q U hu)
  have rf := iterTwo run _ _ _ _ _ (first_run tq P Q hq) (first_handoff Q)
  have ca := run_charge_le machine growth hg _ _ _ (reserve F n) 1500 j0 (by
    have hs := ShiTMCopyStageCost.prefixCost_le_size F n V
    change _ ≤ 1500*(size V+reserve F n)
    dsimp [reserve]
    nlinarith)
  have cb := run_charge_le machine growth hg _ _ _ (reserve F n) 1500 rf (by
    have hs := ShiTMCopyStageCost.stageBound_le_size F n P
    change _ ≤ 1500*(size P+reserve F n)
    dsimp [reserve]
    nlinarith)
  have cab := charge_comp ca cb (by omega)
  have cabu := charge_comp cab hbu hks
  refine ⟨U, vu, _, r2, ?_, ?_⟩
  · change Q ShiTMReadout.output = (ShiTMPayloadCopyStage.payloadBytes 0 F n).reverse ++
      P ShiTMReadout.output at hqo
    change P ShiTMReadout.output =
      ((List.replicate (3*(F.circ n).length+113) true ++ [false]).map bit ++
        ShiTMFanoutStage.payload false n (F.wit n) (F.anc n) ++
        ShiTMFanoutStage.payload true n (F.wit n) (F.anc n)).reverse ++ V ShiTMReadout.output at hpo
    rw [huo, hqo, hpo]
    simp only [circuitBytes, List.reverse_append, List.append_assoc]

  · simpa only [Nat.add_assoc] using cabu

end ShiTMNormalizedCircuit
