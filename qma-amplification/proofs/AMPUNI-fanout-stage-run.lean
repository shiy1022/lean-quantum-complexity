import «AMPUNI-fanout-stage-block»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMFanoutStage
open ShiTMLayoutMachine ShiTMRetainedTop
open ShiTMFanoutPrepare (port scratch Retained base)

theorem clean_run (k : Fin 3) (xs : List (TopGam (port k))) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hs : S (port k) = xs) :
    run^[xs.length+1] (some ⟨some (cleanLabel k), v, S⟩) =
      some ⟨some (afterClean k), none, Function.update S (port k) []⟩ := by
  induction xs generalizing v S with
  | nil => simp [run, ShiTMSubroutine.run, machine, cleanLabel, step, stepAux, hs, pop, isSome]
  | cons x xs ih =>
      have hfirst : run (some ⟨some (cleanLabel k), v, S⟩) =
          some ⟨some (cleanLabel k), some x, Function.update S (port k) xs⟩ := by
        simp [run, ShiTMSubroutine.run, machine, cleanLabel, step, stepAux, hs, pop, isSome]
      rw [List.length_cons, Function.iterate_succ_apply, hfirst]
      simpa using ih (some x) (Function.update S (port k) xs) (by simp)

theorem clean_all_run (v : Sig) (S : ∀ j, List (TopGam j)) :
    ∃ U : ∀ j, List (TopGam j),
      run^[ShiTMFanoutPrepare.clearCost S] (some ⟨some (cleanLabel 0), v, S⟩) =
        some ⟨some finished, none, U⟩
      ∧ U (port 0) = [] ∧ U (port 1) = [] ∧ U (port 2) = []
      ∧ ∀ j, ShiTMFanoutPrepare.Stable j → U j = S j := by
  let T := Function.update S (port 0) []
  let V := Function.update T (port 1) []
  let U := Function.update V (port 2) []
  have h0 := clean_run 0 (S (port 0)) v S rfl
  have h1 := clean_run 1 (S (port 1)) none T (by simp [T])
  have h2 := clean_run 2 (S (port 2)) none V (by simp [V, T])
  rw [show afterClean 0 = cleanLabel 1 from rfl] at h0
  rw [show afterClean 1 = cleanLabel 2 from rfl] at h1
  rw [show afterClean 2 = finished from rfl] at h2
  have h01 := ShiTMFanout.iterTwo run _ _ _ _ _ h0 h1
  have h012 := ShiTMFanout.iterTwo run _ _ _ _ _ h01 h2
  refine ⟨U, ?_, by simp [U, V, T], by simp [U, V], by simp [U], ?_⟩
  · have hc : ((S (port 0)).length+1+((S (port 1)).length+1)) +
        ((S (port 2)).length+1) = ShiTMFanoutPrepare.clearCost S := by
        unfold ShiTMFanoutPrepare.clearCost; omega
    simpa only [hc] using h012
  · intro j hj
    simp [U, V, T, hj.1, hj.2.1, hj.2.2]

def stageCost (n w a : Nat) (S : ∀ j, List (TopGam j)) : Nat :=
  blockCost false n w a S + 1 +
    (base false n w a + 2*n + 2*(n+w+a) + 11 + emitCost n (base true n w a)) + 1 +
    (base true n w a + 2*n + 3)

def payload (second : Bool) (n w a : Nat) : List Cell :=
  ShiTMFanout.unary n ++ ShiTMFanout.recordBytes (base second n w a) 0 n

/-- The complete finite two-fanout stage: retained headers suffice, all work
registers are cleared at exit, and circuit/depth/archive stacks are preserved.
The output accumulator receives both exact layer payloads in circuit order. -/
theorem stage_run (n w a : Nat) (v : Sig) (S : ∀ j, List (TopGam j))
    (hret : Retained n w a S) (ht : S scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[stageCost n w a S] (some ⟨some (prepLabel false (.clear 0)), v, S⟩) =
        some ⟨some finished, none, U⟩
      ∧ U (port 0) = [] ∧ U (port 1) = [] ∧ U (port 2) = []
      ∧ U scratch = []
      ∧ U output = (payload false n w a ++ payload true n w a).reverse ++ S output
      ∧ Retained n w a U
      ∧ ∀ j, Stable j → U j = S j := by
  obtain ⟨A, ha, ha0, ha1, ha2, hat, hao, haret, haf⟩ := block_run false n w a v S hret ht
  have hah := emit_handoff false none A
  obtain ⟨B, hb, hb0, hb1, hb2, hbt, hbo, hbret, hbf⟩ := block_run true n w a none A haret hat
  have hbh := emit_handoff true none B
  obtain ⟨U, hu, hu0, hu1, hu2, huf⟩ := clean_all_run none B
  have hbc : blockCost true n w a A =
      base false n w a + 2*n + 2*(n+w+a) + 11 + emitCost n (base true n w a) := by
    simp [blockCost, ShiTMFanoutPrepare.cost, ShiTMFanoutPrepare.clearCost,
      ha0, ha1, ha2, List.length_replicate]
    omega
  have hcc : ShiTMFanoutPrepare.clearCost B = base true n w a + 2*n + 3 := by
    simp [ShiTMFanoutPrepare.clearCost, hb0, hb1, hb2, List.length_replicate]
    omega
  have hframe : ∀ j, Stable j → U j = S j := by
    intro j hj
    rw [huf j hj.1, hbf j hj, haf j hj]
  refine ⟨U, ?_, hu0, hu1, hu2, ?_, ?_, ?_, hframe⟩
  · have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ ha hah
    have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 hb
    have h3 := ShiTMFanout.iterTwo run _ _ _ _ _ h2 hbh
    have h4 := ShiTMFanout.iterTwo run _ _ _ _ _ h3 hu
    simpa only [stageCost, hbc, hcc] using h4
  · rw [huf scratch (by simp [ShiTMFanoutPrepare.Stable]), hbt]
  · rw [huf output (by simp [ShiTMFanoutPrepare.Stable]), hbo, hao]
    simp [payload, List.reverse_append, List.append_assoc]
  · exact ShiTMFanoutPrepare.retained_frame hret
      (fun h => hframe (ShiTMFanoutPrepare.source h)
        (by simp [Stable, ShiTMFanoutPrepare.Stable]))

end ShiTMFanoutStage
