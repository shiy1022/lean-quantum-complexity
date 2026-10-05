import «AMPUNI-replay-preface-entry-lift»
import «AMPUNI-replay-mark-split»
import «AMPUNI-replay-reload»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayPreface

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOutputEntry
  ShiTMPieceController

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- From an ordinary `initList` input, the finite preface/entry machine archives
the verifier, seeds the delimiter, retains the four unary fields, and completes
the first typed circuit pass. Its exit state meets the later-copy replay
contract. -/
theorem init_then_first_pass (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ∃ (V : ∀ k, List (TopGam k)) (steps : Nat),
      run^[steps]
        (some (Turing.initList finiteMachine
          ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit))) =
        some (liftEntryCfg
          ⟨some (parserLabel (.inl (.inr .exit))), none, V⟩)
      ∧ V ShiTMReplayReload.source = []
      ∧ V ShiTMReplayMarkSplit.marks = []
      ∧ V ShiTMReplayReload.scratch = []
      ∧ V (.inl (.inl (10 : Fin 14))) = []
      ∧ V ShiTMReplayReload.archive =
          List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
            ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse
      ∧ V (.inl (.inl (4 : Fin 14))) = [Cell.delim]
      ∧ V (.inl (.inl (6 : Fin 14))) = []
      ∧ V (.inl (.inl (7 : Fin 14))) = []
      ∧ V (.inl (.inl (12 : Fin 14))) = []
      ∧ V (.inl (.inr (0 : Fin 2))) = []
      ∧ V (.inl (.inr (1 : Fin 2))) = []
      ∧ Retained n (F.wit n) (F.anc n) V
      ∧ V (.inl (.inl (13 : Fin 14))) =
          ((ShiTMRawLayout.encodeCirc
              (ShiTMRawLayout.mapCirc depth
                (ShiTMRawLayout.ampPieces n (F.wit n) (F.anc n)) 0
                ((F.circ n).map (List.map ShiTMRawLayout.ofInstr)))).map bit).reverse ++
            ((ShiBQP.encNat (3 * F.wit n) ++
              ShiBQP.encNat (2 * n + 3 * F.anc n + 3) ++
              ShiBQP.encNat
                (3 * n + 3 * F.wit n + 3 * F.anc n + 3)).map bit).reverse := by
  let input := (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit
  obtain ⟨U, harchiveRun, hUsrc, hUscratch, hUarchive, hUempty⟩ :=
    archive_from_initList input
  let k4 : TopK := .inl (.inl (4 : Fin 14))
  let S : ∀ j, List (TopGam j) := Function.update U k4 [Cell.delim]
  have hU4 : U k4 = [] :=
    hUempty k4 (by decide) (by decide) (by decide)
  have hS4 : S k4 = [Cell.delim] := by
    change Function.update U k4 [Cell.delim] k4 = [Cell.delim]
    rw [Function.update_self]
  have hSempty (j : TopK) (hj4 : j ≠ k4)
      (hjsrc : j ≠ source) (hjscratch : j ≠ scratch)
      (hjarchive : j ≠ archive) : S j = [] := by
    change Function.update U k4 [Cell.delim] j = []
    rw [Function.update_of_ne hj4]
    exact hUempty j hjsrc hjscratch hjarchive
  have hSsrc : S source = input := by
    change Function.update U k4 [Cell.delim] source = input
    rw [Function.update_of_ne (by decide)]
    exact hUsrc
  have hSscratch : S scratch = [] := by
    change Function.update U k4 [Cell.delim] scratch = []
    rw [Function.update_of_ne (by decide)]
    exact hUscratch
  have hSarchive : S archive = Cell.mirrorEnd :: input.reverse := by
    change Function.update U k4 [Cell.delim] archive =
      Cell.mirrorEnd :: input.reverse
    rw [Function.update_of_ne (by decide)]
    exact hUarchive
  have hstart : run^[1]
      (some ⟨some (oldLabel startLabel), none, U⟩) =
      some (liftEntryCfg
        ⟨some (headerLabel .inputLength), none, S⟩) := by
    have h := run_old 1 (some ⟨some startLabel, none, U⟩)
    have hs : startedRun^[1]
        (some ⟨some startLabel, none, U⟩) =
        some (liftStartedCfg
          ⟨some (headerLabel .inputLength), none, S⟩) := by
      simpa [S, k4] using start_step U hU4
    rw [hs] at h
    simpa [liftEntryCfg, liftCfg] using h
  obtain ⟨E, V, bodySteps, hentry, hpass,
    hVsrc, hVmark, hVscratch, hV10, hVarchive,
    hV4, hV6, hV7, hV12, hVC0, hVC1, hVret, hVacc⟩ :=
    first_pass_replay_ready F n none S
      (by simpa [input, source] using hSsrc)
      (by simpa [input, archive] using hSarchive)
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
      (by simpa [scratch] using hSscratch)
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
      (by simpa [k4] using hS4)
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
  have hentryLift : run^[entryCost F n]
      (some (liftEntryCfg
        ⟨some (headerLabel .inputLength), none, S⟩)) =
      some (liftEntryCfg
        ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, E⟩) := by
    have h := run_entry_lift (entryCost F n)
      (some ⟨some (headerLabel .inputLength), none, S⟩)
    rw [hentry] at h
    simpa using h
  have hpassLift : run^[bodySteps]
      (some (liftEntryCfg
        ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, E⟩)) =
      some (liftEntryCfg
        ⟨some (parserLabel (.inl (.inr .exit))), none, V⟩) := by
    have h := run_entry_lift bodySteps
      (some ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, E⟩)
    rw [hpass] at h
    simpa using h
  have hprefix := iterTwo run (2 * (input.length + 1)) 1
    _ _ _ harchiveRun hstart
  have hprefix' := iterTwo run (2 * (input.length + 1) + 1)
    (entryCost F n) _ _ _ hprefix hentryLift
  have hwhole := iterTwo run
    (2 * (input.length + 1) + 1 + entryCost F n)
    bodySteps _ _ _ hprefix' hpassLift
  refine ⟨V, 2 * (input.length + 1) + 1 + entryCost F n + bodySteps,
    hwhole, hVsrc, hVmark, hVscratch,
    hV10, hVarchive, hV4, hV6, hV7, hV12, hVC0, hVC1,
    hVret, hVacc⟩

end ShiTMReplayPreface
