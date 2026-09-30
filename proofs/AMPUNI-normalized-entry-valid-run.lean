import «AMPUNI-normalized-entry-archive»
import «AMPUNI-normalized-entry-headers»
import «AMPUNI-normalized-circuit-contract»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMNormalizedEntry
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a+b] x = z := by
  rw [show a+b = b+a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The finite typed machine starts from ordinary input, constructs all retained
state and numeric fields, and emits the exact amplified family encoding.
Polynomial time, totalization, and canonical Boolean cleanup are separate. -/
theorem init_to_amplified_encoding (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ∃ (V : ∀ k, List (TopGam k)) (v : Sig) (steps : Nat),
      run^[steps] (some (Turing.initList finiteMachine
        ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit))) =
          some ⟨some finished, v, V⟩
      ∧ V ShiTMReadout.output =
        ((ShiClassQMAU.encQMAFamilyAt (ShiClassQMAAmpX.ampFamilyX F) n).map bit).reverse := by
  let input := (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit
  obtain ⟨U, ha, hUsrc, hUscratch, hUarchive, hUempty⟩ := archive_from_initList input
  let k4 : TopK := .inl (.inl (4 : Fin 14))
  let S : ∀ j, List (TopGam j) := Function.update U k4 [Cell.delim]
  have hU4 : U k4 = [] := hUempty k4 (by decide) (by decide) (by decide)
  have hS4 : S k4 = [Cell.delim] := by
    change Function.update U k4 [Cell.delim] k4 = [Cell.delim]
    rw [Function.update_self]
  have hSempty (j : TopK) (hj4 : j ≠ k4)
      (hjsrc : j ≠ source) (hjscratch : j ≠ scratch) (hjarchive : j ≠ archive) : S j = [] := by
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
    change Function.update U k4 [Cell.delim] archive = Cell.mirrorEnd :: input.reverse
    rw [Function.update_of_ne (by decide)]
    exact hUarchive
  have hstart := start_step U hU4
  obtain ⟨H, hh, hHsrc, hH0, hH1, hH2, hH3, hhf⟩ :=
    family_headers_to_output F n [] none S (by simpa [input] using hSsrc)
  have hretH : Retained n (F.wit n) (F.anc n) H := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hSempty (.inr 0) (by decide) (by decide) (by decide) (by decide),
        List.append_nil] using hH0
    · simpa only [hSempty (.inr 1) (by decide) (by decide) (by decide) (by decide),
        List.append_nil] using hH1
    · simpa only [hSempty (.inr 2) (by decide) (by decide) (by decide) (by decide),
        List.append_nil] using hH2
  have hHscratch : H scratch = [] := (hhf (.inl 3) (by decide)).trans hSscratch
  have hHout : H ShiTMReadout.output = [] :=
    (hhf (.inl 13) (by decide)).trans
      (hSempty _ (by decide) (by decide) (by decide) (by decide))
  have hHarchive : H archive =
      List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd :: input.reverse := by
    change H archive = List.replicate (F.out n : Nat) Cell.mark ++ S archive at hH3
    rw [hH3, hSarchive]
  obtain ⟨P, vp, hn, hno, hretP, hPscratch, hnf⟩ :=
    ShiTMOutputHeader.run_program_finished n (F.wit n) (F.anc n)
      (some Cell.delim) H hretH hHscratch
  have hPsrc : P ShiTMReplayReload.source = (ShiBQP.encCirc (F.circ n)).map bit := by
    have he := hnf source (by simp [ShiTMOutputHeader.OutsideWrites, source])
    exact he.trans (by simpa only [List.append_nil] using hHsrc)
  have hParchive : P ShiTMReplayMarkSplit.archive =
      List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd :: input.reverse :=
    (hnf archive (by simp [ShiTMOutputHeader.OutsideWrites, archive])).trans hHarchive
  have hP4 : P k4 = [Cell.delim] :=
    (hnf k4 (by simp [ShiTMOutputHeader.OutsideWrites, k4])).trans
      ((hhf (.inl 4) (by decide)).trans hS4)
  have hP10 : P (.inl (.inl (10 : Fin 14))) = [] :=
    (hnf _ (by simp [ShiTMOutputHeader.OutsideWrites])).trans
      ((hhf (.inl (10 : Fin 14)) (by decide)).trans
        (hSempty _ (by decide) (by decide) (by decide) (by decide)))
  have hP6 : P (.inl (.inl (6 : Fin 14))) = [] :=
    (hnf _ (by simp [ShiTMOutputHeader.OutsideWrites])).trans
      ((hhf (.inl (6 : Fin 14)) (by decide)).trans
        (hSempty _ (by decide) (by decide) (by decide) (by decide)))
  have hP7 : P (.inl (.inl (7 : Fin 14))) = [] :=
    (hnf _ (by simp [ShiTMOutputHeader.OutsideWrites])).trans
      ((hhf (.inl (7 : Fin 14)) (by decide)).trans
        (hSempty _ (by decide) (by decide) (by decide) (by decide)))
  have hP12 : P (.inl (.inl (12 : Fin 14))) = [] :=
    (hnf _ (by simp [ShiTMOutputHeader.OutsideWrites])).trans
      ((hhf (.inl (12 : Fin 14)) (by decide)).trans
        (hSempty _ (by decide) (by decide) (by decide) (by decide)))
  have hPc0 : P (.inl (.inr (0 : Fin 2))) = [] :=
    (hnf _ (by simp [ShiTMOutputHeader.OutsideWrites])).trans
      ((hhf (.inr (0 : Fin 2)) (by decide)).trans
        (hSempty _ (by decide) (by decide) (by decide) (by decide)))
  have hPc1 : P (.inl (.inr (1 : Fin 2))) = [] :=
    (hnf _ (by simp [ShiTMOutputHeader.OutsideWrites])).trans
      ((hhf (.inr (1 : Fin 2)) (by decide)).trans
        (hSempty _ (by decide) (by decide) (by decide) (by decide)))
  have hfields : P ShiTMReadout.output =
      ((ShiBQP.encNat (3 * F.wit n) ++
        ShiBQP.encNat (2 * n + 3 * F.anc n + 3) ++
        ShiBQP.encNat (3 * n + 3 * F.wit n + 3 * F.anc n + 3)).map bit).reverse := by
    change P ShiTMReadout.output = ShiTMOutputHeader.eval n (F.wit n) (F.anc n)
      ShiTMOutputHeader.program (H ShiTMReadout.output) at hno
    rw [hno, hHout, ShiTMOutputHeader.program_correct_encoding]
  obtain ⟨V, vv, tc, hc, hco⟩ := ShiTMNormalizedCircuit.valid_circuit_run F n vp P
    hPsrc hPscratch hParchive hretP hP10 hP4 hP6 hP7 hP12 hPc0 hPc1
  have hout := ShiTMNormalizedCircuit.family_output_typed F n P V hfields hco
  have r0 := iterTwo run _ _ _ _ _ ha hstart
  have r1 := iterTwo run _ _ _ _ _ r0 hh
  have r2 := iterTwo run _ _ _ _ _ r1 (output_run _ (some Cell.delim) vp H P hn)
  have r3 := iterTwo run _ _ _ _ _ r2 (output_handoff vp P)
  have r4 := iterTwo run _ _ _ _ _ r3 (circuit_run tc vp vv P V hc)
  exact ⟨V, vv, _, r4, hout⟩

end ShiTMNormalizedEntry
