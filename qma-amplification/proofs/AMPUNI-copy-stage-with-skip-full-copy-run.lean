import «AMPUNI-copy-stage-with-skip-copy-pass»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController
  ShiTMPieceSchedule

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- One entire later-copy cycle is a run of the corrected finite controller:
replay the retained verifier, build the copy-specific layout, and parse the
verifier circuit into the persistent reversed output accumulator. -/
theorem full_copy_run (copy : Fin 3)
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
    ∃ (Q : ∀ k, List (TopGam k)) (steps : Nat),
      run^[steps]
        (some ⟨some (oldLabel (ShiTMCopyStage.cycleLabel copy
          (ShiTMReplayCycle.splitLabel false))), none, V⟩) =
        some ⟨some (copyParserLabel copy (.inl (.inr .exit))), none, Q⟩
      ∧ Q (.inl (.inl (13 : Fin 14))) =
          ((ShiTMRawLayout.encodeCirc
            (ShiTMRawLayout.mapCirc depth
              (expectedPieces copy n (F.wit n) (F.anc n)) 0
              ((F.circ n).map (List.map ShiTMRawLayout.ofInstr)))).map bit).reverse ++
            V (.inl (.inl (13 : Fin 14)))
      ∧ Q ShiTMReplayReload.source = []
      ∧ Q ShiTMReplayMarkSplit.marks = []
      ∧ Q ShiTMReplayReload.scratch = []
      ∧ Q (.inl (.inl (10 : Fin 14))) = []
      ∧ Q ShiTMReplayReload.archive =
          List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
            ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse
      ∧ Q (.inl (.inl (4 : Fin 14))) = [Cell.delim]
      ∧ Q (.inl (.inl (6 : Fin 14))) = []
      ∧ Q (.inl (.inl (7 : Fin 14))) = []
      ∧ Q (.inl (.inl (12 : Fin 14))) = []
      ∧ Q (.inl (.inr (0 : Fin 2))) = []
      ∧ Q (.inl (.inr (1 : Fin 2))) = []
      ∧ Retained n (F.wit n) (F.anc n) Q := by
  obtain ⟨W, T, P, hprep, hPsrc, hParchive, hP0, hP1, hP2,
    hP3, hP4, hP6, hP7, hP8, hP9, hP10, hP12,
    hPC0, hPC1, hP13, hPret⟩ :=
    cycle_to_parser_layout copy F n V
      hsource hscratch hmarks harchive hret h10
      h4 h6 h7 h12 hc0 hc1
  obtain ⟨Q, bodyCost, hbody, hacc, hQsrc, hQ0,
    hQ3, hQ10, hQ4, hQ6, hQ7, hQ12, hQC0, hQC1, hQheaders⟩ :=
    typed_copy_pass_from_ready copy F n P
      hPsrc hP0 hP1 hP2 hP3 hP4 hP6 hP7
      hP8 hP9 hP10 hP12 hPC0 hPC1
  let prepCost := cycleSkipCost F n +
    ShiTMReplayTableClear.clearCost W + 1 +
    (scheduleCost n (F.wit n) (F.anc n) (program copy) + 1 + 1) +
    ((2 * (T (.inl (.inl (1 : Fin 14)))).length + 3) +
      (2 * (T (.inl (.inl (2 : Fin 14)))).length + 3) + 1)
  refine ⟨Q, prepCost + bodyCost, ?_, ?_, hQsrc, hQ0,
    hQ3, hQ10, ?_, hQ4, hQ6, hQ7, hQ12, hQC0, hQC1, ?_⟩
  · exact iterTwo run prepCost bodyCost _ _ _ hprep hbody
  · rw [hacc, hP13]
  · exact (hQheaders 3).trans hParchive
  · rcases hPret with ⟨h0, h1, h2⟩
    exact ⟨(hQheaders 0).trans h0,
      (hQheaders 1).trans h1,
      (hQheaders 2).trans h2⟩

end ShiTMCopyStageWithSkip
