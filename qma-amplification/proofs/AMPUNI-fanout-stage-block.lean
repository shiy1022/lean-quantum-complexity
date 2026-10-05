import «AMPUNI-fanout-stage-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2

namespace ShiTMFanoutStage
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOuterLift
open ShiTMFanoutPrepare (port scratch Retained base)

abbrev output : TopK := .inl ShiTMFanout.output

def Stable (j : TopK) : Prop := ShiTMFanoutPrepare.Stable j ∧ j ≠ output

def emitCost (n b : Nat) : Nat := 2*n*n+n*(2*b+7)+4

def blockCost (second : Bool) (n w a : Nat) (S : ∀ j, List (TopGam j)) : Nat :=
  ShiTMFanoutPrepare.cost n w a S + 1 + emitCost n (base second n w a)

/-- Execute an emitter inside the combined controller, with its unchanged
exact cost and a frame covering all retained headers and archived input. -/
theorem emit_run (second : Bool) (n b : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j))
    (h0 : S (port 0) = List.replicate n Cell.mark) (h1 : S (port 1) = [])
    (h2 : S (port 2) = List.replicate b Cell.mark) (ht : S scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[emitCost n b] (some ⟨some (emitLabel second (.copy 0)), v, S⟩) =
        some ⟨some (emitLabel second .finished), none, U⟩
      ∧ U (port 0) = []
      ∧ U (port 1) = List.replicate n Cell.mark
      ∧ U (port 2) = List.replicate (b+n) Cell.mark
      ∧ U scratch = []
      ∧ U output = (ShiTMFanout.unary n ++ ShiTMFanout.recordBytes b 0 n).reverse ++ S output
      ∧ ∀ j, Stable j → U j = S j := by
  let O : ∀ k, List (OuterGam k) := fun k => S (.inl k)
  let H : Fin 4 → List Cell := fun h => S (.inr h)
  have hS : topStacks O H = S := by funext j; cases j <;> rfl
  obtain ⟨V, hr, hv0, hv1, hv2, hvt, hvo, hvf⟩ :=
    ShiTMFanout.fanout_run n b v O h0 h1 h2 ht
  let U := topStacks V H
  have htop := ShiTMTopFrame.run_iter_frame ShiTMFanout.machine H (emitCost n b)
    (some ⟨some (.copy 0), v, O⟩)
  change (ShiTMSubroutine.run emitter)^[emitCost n b]
      (some ⟨some (.copy 0), v, topStacks O H⟩) =
      ((ShiTMFanout.run)^[emitCost n b]
        (some ⟨some (.copy 0), v, O⟩)).map (ShiTMTopFrame.cfg H) at htop
  change ShiTMFanout.run^[emitCost n b] (some ⟨some (.copy 0), v, O⟩) =
    some ⟨some .finished, none, V⟩ at hr
  rw [hr, hS] at htop
  have hlift := emit_run_lift second (emitCost n b)
    (some ⟨some (.copy 0), v, S⟩) ⟨some .finished, none, U⟩ rfl htop
  refine ⟨U, ?_, hv0, hv1, hv2, hvt, hvo, ?_⟩
  · simpa [ShiTMSubroutine.cfg] using hlift
  · intro j hj
    by_cases hjt : j = scratch
    · subst j; exact hvt.trans ht.symm
    cases j with
    | inl k =>
        apply hvf k
        exact ⟨by simpa using hj.1.1, by simpa using hj.1.2.1,
          by simpa using hj.1.2.2, by simpa using hjt, by simpa using hj.2⟩
    | inr h => rfl

/-- One prepared fanout block from retained fields. The active emit-finished
label is the explicit handoff to the next preparation or final cleanup. -/
theorem block_run (second : Bool) (n w a : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hret : Retained n w a S) (ht : S scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[blockCost second n w a S]
        (some ⟨some (prepLabel second (.clear 0)), v, S⟩) =
        some ⟨some (emitLabel second .finished), none, U⟩
      ∧ U (port 0) = []
      ∧ U (port 1) = List.replicate n Cell.mark
      ∧ U (port 2) = List.replicate (base second n w a+n) Cell.mark
      ∧ U scratch = []
      ∧ U output =
        (ShiTMFanout.unary n ++ ShiTMFanout.recordBytes (base second n w a) 0 n).reverse ++ S output
      ∧ Retained n w a U
      ∧ ∀ j, Stable j → U j = S j := by
  obtain ⟨T, hp, h0, h1, h2, hscratch, hretT, hf⟩ :=
    ShiTMFanoutPrepare.prepare_run second n w a v S hret ht
  have hp' := prep_run_lift second (ShiTMFanoutPrepare.cost n w a S)
    (some ⟨some (.clear 0), v, S⟩) ⟨some .finished, none, T⟩ rfl hp
  simp only [Option.map_some, ShiTMSubroutine.cfg, Option.map_some] at hp'
  have hhand := prep_handoff second none T
  obtain ⟨U, he, hu0, hu1, hu2, hut, huo, huf⟩ :=
    emit_run second n (base second n w a) none T h0 h1 h2 hscratch
  have hframe : ∀ j, Stable j → U j = S j := by
    intro j hj; rw [huf j hj, hf j hj.1]
  refine ⟨U, ?_, hu0, hu1, hu2, hut, ?_, ?_, hframe⟩
  · have hph := ShiTMFanout.iterTwo run _ _ _ _ _ hp' hhand
    exact ShiTMFanout.iterTwo run _ _ _ _ _ hph he
  · rw [huo, hf output (by simp [ShiTMFanoutPrepare.Stable])]
  · exact ShiTMFanoutPrepare.retained_frame hret
      (fun h => hframe (ShiTMFanoutPrepare.source h)
        (by simp [Stable, ShiTMFanoutPrepare.Stable]))

end ShiTMFanoutStage
