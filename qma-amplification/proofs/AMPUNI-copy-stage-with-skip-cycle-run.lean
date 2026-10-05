import «AMPUNI-copy-stage-with-skip-lift-run»
import «AMPUNI-replay-cycle-full-run»
import «AMPUNI-replay-header-skip-family»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

def cycleSkipCost (F : ShiClassQMA.QMAFamily) (n : Nat) : Nat :=
  ShiTMReplayCycle.cycleCost (F.out n : Nat)
    ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit)
  + 1 + ShiTMReplayHeaderSkip.skipCost n (F.wit n) (F.anc n) (F.out n : Nat) + 1

/-- One replay pass restores the archived verifier, traverses its four headers,
and reaches the table-clear entry with precisely the original circuit on the
source stack. This run is in the corrected finite copy-stage machine. -/
theorem cycle_skip_run (copy : Fin 3)
    (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V : ∀ k, List (TopGam k))
    (hsource : V ShiTMReplayReload.source = [])
    (hscratch : V ShiTMReplayReload.scratch = [])
    (hmarks : V ShiTMReplayMarkSplit.marks = [])
    (harchive : V ShiTMReplayMarkSplit.archive =
      List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
        ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse) :
    ∃ W : ∀ k, List (TopGam k),
      run^[cycleSkipCost F n]
        (some ⟨some (oldLabel (ShiTMCopyStage.cycleLabel copy
          (ShiTMReplayCycle.splitLabel false))), none, V⟩) =
        some ⟨some (oldLabel (ShiTMCopyStage.clearLabel copy .width)),
          some Cell.delim, W⟩
      ∧ W ShiTMReplayReload.source =
          (ShiBQP.encCirc (F.circ n)).map bit
      ∧ W ShiTMReplayReload.scratch = []
      ∧ W ShiTMReplayMarkRestore.marks = []
      ∧ W ShiTMReplayReload.archive =
          List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
            ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse
      ∧ ∀ j : TopK,
          j ≠ ShiTMReplayReload.source →
          j ≠ ShiTMReplayReload.scratch →
          j ≠ ShiTMReplayMarkRestore.marks →
          j ≠ ShiTMReplayReload.archive → W j = V j := by
  let s := (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit
  obtain ⟨U, hcycle, hUsource, hUscratch, hUmarks, hUarchive,
    hUframe⟩ :=
    ShiTMReplayCycle.full_cycle_run (F.out n : Nat) s V
      hsource hscratch hmarks harchive
  obtain ⟨W, hskip, hWsource, hSkipFrame⟩ :=
    ShiTMReplayHeaderSkip.skip_family_run F n none U hUsource
  have hcycle' : run^[ShiTMReplayCycle.cycleCost (F.out n : Nat) s]
      (some ⟨some (oldLabel (ShiTMCopyStage.cycleLabel copy
        (ShiTMReplayCycle.splitLabel false))), none, V⟩) =
        some ⟨some (oldLabel (ShiTMCopyStage.cycleLabel copy
          (ShiTMReplayCycle.restoreLabel true))), none, U⟩ := by
    simpa [liftCfg, oldLabel, ShiTMCopyStage.cycleLabel] using
      cycle_run_lift copy _
        (some ⟨some (ShiTMReplayCycle.splitLabel false), none, V⟩)
        ⟨some (ShiTMReplayCycle.restoreLabel true), none, U⟩ rfl hcycle
  have htoSkip : run^[1]
      (some ⟨some (oldLabel (ShiTMCopyStage.cycleLabel copy
        (ShiTMReplayCycle.restoreLabel true))), none, U⟩) =
        some ⟨some (skipLabel copy 0), none, U⟩ := by
    simpa using replay_to_skip_step copy none U
  have hskip' : run^[ShiTMReplayHeaderSkip.skipCost
      n (F.wit n) (F.anc n) (F.out n : Nat)]
      (some ⟨some (skipLabel copy 0), none, U⟩) =
        some ⟨some (skipLabel copy 4), some Cell.delim, W⟩ := by
    simpa [liftCfg, skipLabel] using
      skip_run_lift copy _
        (some ⟨some (0 : ShiTMReplayHeaderSkip.Phase), none, U⟩)
        ⟨some (4 : ShiTMReplayHeaderSkip.Phase), some Cell.delim, W⟩
        rfl hskip
  have htoClear : run^[1]
      (some ⟨some (skipLabel copy 4), some Cell.delim, W⟩) =
        some ⟨some (oldLabel (ShiTMCopyStage.clearLabel copy .width)),
          some Cell.delim, W⟩ := by
    simpa using skip_to_clear_step copy (some Cell.delim) W
  refine ⟨W, ?_, hWsource, ?_, ?_, ?_, ?_⟩
  · have h₁ := iterTwo run
      (ShiTMReplayCycle.cycleCost (F.out n : Nat) s) 1
      _ _ _ hcycle' htoSkip
    have h₂ := iterTwo run
      (ShiTMReplayCycle.cycleCost (F.out n : Nat) s + 1)
      (ShiTMReplayHeaderSkip.skipCost
        n (F.wit n) (F.anc n) (F.out n : Nat))
      _ _ _ h₁ hskip'
    exact iterTwo run
      (ShiTMReplayCycle.cycleCost (F.out n : Nat) s + 1 +
        ShiTMReplayHeaderSkip.skipCost
          n (F.wit n) (F.anc n) (F.out n : Nat)) 1
      _ _ _ h₂ htoClear
  · exact (hSkipFrame _ (by decide)).trans hUscratch
  · exact (hSkipFrame _ (by decide)).trans hUmarks
  · exact (hSkipFrame _ (by decide)).trans hUarchive
  · intro j hsrc hscratch' hmarks' harch
    exact (hSkipFrame j hsrc).trans
      (hUframe j hsrc hscratch' hmarks' harch)

end ShiTMCopyStageWithSkip
