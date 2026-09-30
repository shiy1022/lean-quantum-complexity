import «AMPUNI-normalized-entry-archive»
import «AMPUNI-normalized-circuit-charged»
import «AMPUNI-normalized-boolean-valid-run»
import «AMPUNI-boolean-controller-bounds»
import «AMPUNI-normalized-entry-headers»
import «AMPUNI-normalized-circuit-contract»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open Turing Turing.TM2
namespace ShiTMNormalizedEntry
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController ShiTMStackGrowth
open ShiTMRetainedPayload
open ShiTMPayloadSuffix (reserve)

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a+b] x = z := by
  rw [show a+b = b+a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The finite typed machine starts from ordinary input, constructs all retained
state and numeric fields, and emits the exact amplified family encoding.
A uniform quadratic bound includes all input preparation and circuit stages.
Malformed-input totalization remains separate. -/
theorem init_to_amplified_encoding_charged :
    ∃ K : Nat, ∀ (F : ShiClassQMA.QMAFamily) (n : Nat),
    ∃ (V : ∀ k, List (TopGam k)) (v : Sig) (steps : Nat),
      run^[steps] (some (Turing.initList finiteMachine
        ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit))) =
          some ⟨some finished, v, V⟩
      ∧ V ShiTMReadout.output =
        ((ShiClassQMAU.encQMAFamilyAt (ShiClassQMAAmpX.ampFamilyX F) n).map bit).reverse
      ∧ steps+size V+reserve F n ≤ K*reserve F n := by
  classical
  obtain ⟨growth, hg⟩ := finite_growth machine
  obtain ⟨kc, hkc, circuit⟩ := ShiTMNormalizedCircuit.valid_circuit_run_charged
  let k := 1+1500*(growth+1)
  refine ⟨2*(kc*k), ?_⟩
  intro F n
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
  obtain ⟨V, vv, tc, hc, hco, hbc⟩ := circuit F n vp P
    hPsrc hPscratch hParchive hretP hP10 hP4 hP6 hP7 hP12 hPc0 hPc1
  have hout := ShiTMNormalizedCircuit.family_output_typed F n P V hfields hco
  have r0 := iterTwo run _ _ _ _ _ ha hstart
  have r1 := iterTwo run _ _ _ _ _ r0 hh
  have r2 := iterTwo run _ _ _ _ _ r1 (output_run _ (some Cell.delim) vp H P hn)
  have r3 := iterTwo run _ _ _ _ _ r2 (output_handoff vp P)
  have r4 := iterTwo run _ _ _ _ _ r3 (circuit_run tc vp vv P V hc)
  have hinput : input.length = inputLength F n := by simp [input, inputLength]
  have hinit : size (K := TopK) (G := TopGam)
      (Turing.initList finiteMachine input).stk = inputLength F n := by
    have hi := congrArg (fun c : Cfg TopGam Label Sig => size c.stk)
      (typed_initial_eq (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n))
    exact hi.trans (ShiTMBooleanWrapper.initialTop_size _)
  have ca := run_charge_le machine growth hg _ _ _ (reserve F n) 1500 r3 (by
    have hp := ShiTMOutputHeader.programCost_le n (F.wit n) (F.anc n)
    have hf := resources_le_inputLength F n
    have hhcost : (n+1)+(F.wit n+1)+(F.anc n+1)+((F.out n : Nat)+1) ≤ inputLength F n := by
      rw [inputLength_eq]
      omega
    simp only [hinput]
    dsimp [reserve]
    nlinarith)
  have hb := charge_comp ca hbc hkc
  have hl : inputLength F n ≤ reserve F n := by dsimp [reserve]; nlinarith
  refine ⟨V, vv, _, r4, hout, ?_⟩
  calc
    _ ≤ (kc*k)*(size (K := TopK) (G := TopGam)
        (Turing.initList finiteMachine input).stk+reserve F n) := hb
    _ = (kc*k)*(inputLength F n+reserve F n) :=
      congrArg (fun s => (kc*k)*(s+reserve F n)) hinit
    _ ≤ (kc*k)*(2*reserve F n) := Nat.mul_le_mul_left _ (by omega)
    _ = (2*(kc*k))*reserve F n := by ring

end ShiTMNormalizedEntry
