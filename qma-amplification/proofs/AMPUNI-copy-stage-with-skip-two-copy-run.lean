import «AMPUNI-copy-stage-with-skip-parser-handoff»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController

def copyBytes (copy : Fin 3) (F : ShiClassQMA.QMAFamily) (n : Nat) :
    List Cell :=
  (ShiTMRawLayout.encodeCirc
    (ShiTMRawLayout.mapCirc depth
      (expectedPieces copy n (F.wit n) (F.anc n)) 0
      ((F.circ n).map (List.map ShiTMRawLayout.ofInstr)))).map bit

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- Both remaining verifier copies execute in one corrected finite machine.
The output accumulator records copy 1 and copy 2 in reverse-output order. -/
theorem two_copy_run (F : ShiClassQMA.QMAFamily) (n : Nat)
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
    ∃ (R : ∀ k, List (TopGam k)) (steps : Nat),
      run^[steps]
        (some ⟨some (oldLabel (ShiTMCopyStage.cycleLabel 1
          (ShiTMReplayCycle.splitLabel false))), none, V⟩) =
        some ⟨some (oldLabel ShiTMCopyStage.doneLabel), none, R⟩
      ∧ R (.inl (.inl (13 : Fin 14))) =
          (copyBytes 2 F n).reverse ++ (copyBytes 1 F n).reverse ++
            V (.inl (.inl (13 : Fin 14)))
      ∧ R ShiTMReplayReload.source = []
      ∧ R ShiTMReplayMarkSplit.marks = []
      ∧ R ShiTMReplayReload.scratch = []
      ∧ R ShiTMReplayReload.archive =
          List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
            ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse
      ∧ Retained n (F.wit n) (F.anc n) R := by
  obtain ⟨Q1, s1, hrun1, hacc1, hsrc1, hmark1, hscratch1,
    h101, harchive1, h41, h61, h71, h121, hc01, hc11, hret1⟩ :=
    full_copy_run 1 F n V hsource hscratch hmarks harchive hret h10
      h4 h6 h7 h12 hc0 hc1
  obtain ⟨R, s2, hrun2, hacc2, hsrc2, hmark2, hscratch2,
    _, harchive2, _, _, _, _, _, _, hret2⟩ :=
    full_copy_run 2 F n Q1 hsrc1 hscratch1 hmark1 harchive1
      hret1 h101 h41 h61 h71 h121 hc01 hc11
  have hbridge1 : run^[1]
      (some ⟨some (copyParserLabel 1 (.inl (.inr .exit))), none, Q1⟩) =
      some ⟨some (oldLabel (ShiTMCopyStage.cycleLabel 2
        (ShiTMReplayCycle.splitLabel false))), none, Q1⟩ := by
    simpa using copy1_to_copy2_step none Q1
  have hbridge2 : run^[1]
      (some ⟨some (copyParserLabel 2 (.inl (.inr .exit))), none, R⟩) =
      some ⟨some (oldLabel ShiTMCopyStage.doneLabel), none, R⟩ := by
    simpa using copy2_to_done_step none R
  have hfirst := iterTwo run s1 1 _ _ _ hrun1 hbridge1
  have hsecond := iterTwo run (s1 + 1) s2 _ _ _ hfirst hrun2
  have hdone := iterTwo run (s1 + 1 + s2) 1 _ _ _ hsecond hbridge2
  refine ⟨R, s1 + 1 + s2 + 1, hdone, ?_, hsrc2,
    hmark2, hscratch2, harchive2, hret2⟩
  rw [hacc2, hacc1]
  simp only [copyBytes, List.append_assoc]

end ShiTMCopyStageWithSkip
