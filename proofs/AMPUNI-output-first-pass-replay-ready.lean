import «AMPUNI-output-entry-first-pass»
import «AMPUNI-output-first-pass-archive-frame»
import «AMPUNI-output-first-pass-retained»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop

/-- The first circuit pass leaves the exact state needed by the replay
boundary: consumed source, empty parser scratch, and retained input below the
output-index marks. -/
theorem first_pass_replay_ready
    (F : ShiClassQMA.QMAFamily) (n : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j))
    (hsrc : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit)
    (harchive : S (.inr (3 : Fin 4)) =
      Cell.mirrorEnd ::
        ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse)
    (hret0 : S (.inr (0 : Fin 4)) = [])
    (hret1 : S (.inr (1 : Fin 4)) = [])
    (hret2 : S (.inr (2 : Fin 4)) = [])
    (h13 : S (.inl (.inl (13 : Fin 14))) = [])
    (h3 : S (.inl (.inl (3 : Fin 14))) = [])
    (h1 : S (.inl (.inl (1 : Fin 14))) = [])
    (h2 : S (.inl (.inl (2 : Fin 14))) = [])
    (h8 : S (.inl (.inl (8 : Fin 14))) = [])
    (h9 : S (.inl (.inl (9 : Fin 14))) = [])
    (h10 : S (.inl (.inl (10 : Fin 14))) = [])
    (h0 : S (.inl (.inl (0 : Fin 14))) = [])
    (h4 : S (.inl (.inl (4 : Fin 14))) = [Cell.delim])
    (h6 : S (.inl (.inl (6 : Fin 14))) = [])
    (h7 : S (.inl (.inl (7 : Fin 14))) = [])
    (h12 : S (.inl (.inl (12 : Fin 14))) = [])
    (hc0 : S (.inl (.inr (0 : Fin 2))) = [])
    (hc1 : S (.inl (.inr (1 : Fin 2))) = []) :
    ∃ (U V : ∀ j, List (TopGam j)) (steps : Nat),
      run^[entryCost F n]
        (some { l := some (headerLabel .inputLength), var := v, stk := S }) =
          some ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, U⟩
      ∧ run^[steps]
          (some ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, U⟩) =
            some ⟨some (parserLabel (.inl (.inr .exit))), none, V⟩
      ∧ V (.inl (.inl (11 : Fin 14))) = []
      ∧ V (.inl (.inl (0 : Fin 14))) = []
      ∧ V (.inl (.inl (3 : Fin 14))) = []
      ∧ V (.inl (.inl (10 : Fin 14))) = []
      ∧ V (.inr (3 : Fin 4)) =
          List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
            ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse
      ∧ V (.inl (.inl (4 : Fin 14))) = [Cell.delim]
      ∧ V (.inl (.inl (6 : Fin 14))) = []
      ∧ V (.inl (.inl (7 : Fin 14))) = []
      ∧ V (.inl (.inl (12 : Fin 14))) = []
      ∧ V (.inl (.inr (0 : Fin 2))) = []
      ∧ V (.inl (.inr (1 : Fin 2))) = []
      ∧ ShiTMPieceController.Retained n (F.wit n) (F.anc n) V
      ∧ V (.inl (.inl (13 : Fin 14))) =
          ((ShiTMRawLayout.encodeCirc
              (ShiTMRawLayout.mapCirc depth
                (ShiTMRawLayout.ampPieces n (F.wit n) (F.anc n)) 0
                ((F.circ n).map (List.map ShiTMRawLayout.ofInstr)))).map bit).reverse ++
            ((ShiBQP.encNat (3 * F.wit n) ++
              ShiBQP.encNat (2 * n + 3 * F.anc n + 3) ++
              ShiBQP.encNat
                (3 * n + 3 * F.wit n + 3 * F.anc n + 3)).map bit).reverse := by
  obtain ⟨U, V, steps, hentry, hpass, hout, hV11, hV0, hV3, hV10,
    hV4, hV6, hV7, hV12, hVC0, hVC1⟩ :=
    entry_then_first_circuit_pass F n v S hsrc
      hret0 hret1 hret2 h13 h3 h1 h2 h8 h9 h10
      h0 h4 h6 h7 h12 hc0 hc1
  refine ⟨U, V, steps, hentry, hpass, hV11, hV0, hV3, hV10,
    ?_, hV4, hV6, hV7, hV12, hVC0, hVC1, ?_, hout⟩
  · have hVarchive := first_pass_archive_frame F n S U V steps v hsrc
      hret0 hret1 hret2 h13 h3 h1 h2 h8 h9 h10 hentry hpass
    rw [harchive] at hVarchive
    exact hVarchive
  · exact first_pass_retained F n v S U V steps hsrc
      hret0 hret1 hret2 h13 h3 h1 h2 h8 h9 h10 hentry hpass

end ShiTMOutputEntry
