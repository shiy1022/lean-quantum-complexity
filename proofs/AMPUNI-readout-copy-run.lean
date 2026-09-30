import «AMPUNI-readout-copy-machine»
import «AMPUNI-piece-expected-width»
import «AMPUNI-readout-lookup-bounds»
import «AMPUNI-readout-amplifier-contract»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMReadoutCopy
open ShiTMLayoutMachine ShiTMRetainedTop
open ShiTMPieceController (Retained expectedPieces)

theorem destination_ne_core (copy : Fin 3) (k : Fin 14)
    (hk : k.val < 4 ∨ 7 < k.val) : destination copy ≠ core k := by
  intro he
  have hv := congrArg (fun j : TopK => match j with
    | .inl (.inl i) => i.val
    | _ => 0) he
  change copy.val+4 = k.val at hv
  omega

@[simp] theorem destination_ne_0 (copy : Fin 3) : destination copy ≠ core 0 := destination_ne_core copy 0 (by decide)
@[simp] theorem destination_ne_1 (copy : Fin 3) : destination copy ≠ core 1 := destination_ne_core copy 1 (by decide)
@[simp] theorem destination_ne_2 (copy : Fin 3) : destination copy ≠ core 2 := destination_ne_core copy 2 (by decide)
@[simp] theorem destination_ne_3 (copy : Fin 3) : destination copy ≠ core 3 := destination_ne_core copy 3 (by decide)
@[simp] theorem destination_ne_10 (copy : Fin 3) : destination copy ≠ core 10 := destination_ne_core copy 10 (by decide)
@[simp] theorem destination_ne_13 (copy : Fin 3) : destination copy ≠ core 13 := destination_ne_core copy 13 (by decide)

def cleared (copy : Fin 3) (S : ∀ k, List (TopGam k)) : ∀ k, List (TopGam k) :=
  Function.update (Function.update (Function.update S (core 1) []) (core 2) []) (destination copy) []
def clearCost (copy : Fin 3) (S : ∀ k, List (TopGam k)) : Nat :=
  (S (core 1)).length+(S (core 2)).length+(S (destination copy)).length+3

theorem clear_all_run (copy : Fin 3) (v : Sig) (S : ∀ k, List (TopGam k)) :
    (run copy)^[clearCost copy S] (some ⟨some (clearLabel 0), v, S⟩) =
      some ⟨some (tableLabel (.dispatch copy 0)), none, cleared copy S⟩ := by
  let T := Function.update S (core 1) []
  let V := Function.update T (core 2) []
  have h0 : (run copy)^[(S (core 1)).length+1]
      (some ⟨some (clearLabel 0), v, S⟩) = some ⟨some (clearLabel 1), none, T⟩ :=
    clear_run copy 0 (S (core 1)) v S rfl
  have h1 : (run copy)^[(S (core 2)).length+1]
      (some ⟨some (clearLabel 1), none, T⟩) = some ⟨some (clearLabel 2), none, V⟩ :=
    clear_run copy 1 (S (core 2)) none T (by
      change Function.update S (core 1) [] (core 2) = S (core 2)
      rw [Function.update_of_ne (show (core 2 : TopK) ≠ core 1 by decide)])
  have h2 : (run copy)^[(S (destination copy)).length+1]
      (some ⟨some (clearLabel 2), none, V⟩) =
      some ⟨some (tableLabel (.dispatch copy 0)), none, cleared copy S⟩ :=
    clear_run copy 2 (S (destination copy)) none V (by
      change Function.update (Function.update S (core 1) []) (core 2) [] (destination copy) = S (destination copy)
      rw [Function.update_of_ne (destination_ne_2 copy), Function.update_of_ne (destination_ne_1 copy)])
  have h01 := ShiTMFanout.iterTwo (run copy) _ _ _ _ _ h0 h1
  have h012 := ShiTMFanout.iterTwo (run copy) _ _ _ _ _ h01 h2
  have he : ((S (core 1)).length+1)+((S (core 2)).length+1)+
      ((S (destination copy)).length+1) = clearCost copy S := by unfold clearCost; omega
  simpa only [he] using h012

/-- The stacks that may change during a single readout-wire preparation. -/
def Stable (copy : Fin 3) (k : TopK) : Prop :=
  k ≠ core 0 ∧ k ≠ core 1 ∧ k ≠ core 2 ∧ k ≠ core 3 ∧
    k ≠ destination copy ∧ k ≠ core 10

theorem cleared_frame (copy : Fin 3) (S : ∀ k, List (TopGam k)) (k : TopK)
    (h1 : k ≠ core 1) (h2 : k ≠ core 2) (hd : k ≠ destination copy) :
    cleared copy S k = S k := by simp [cleared, h1, h2, hd]

def copyCost (copy : Fin 3) (n w a out : Nat) (S : ∀ k, List (TopGam k)) : Nat :=
  clearCost copy S + (ShiTMPieceController.scheduleCost n w a (ShiTMPieceSchedule.program copy)+1)+1+
    ((S (core 0)).length+2*out+3)+1+cost (expectedPieces copy n w a) out

private theorem program_tables (copy : Fin 3) (n w a : Nat) :
    ShiTMPieceSchedule.runCommands n w a (ShiTMPieceSchedule.program copy) ([], []) =
      (pieceCells Prod.fst (expectedPieces copy n w a), pieceCells Prod.snd (expectedPieces copy n w a)) := by
  fin_cases copy
  · simpa [expectedPieces] using ShiTMPieceSchedule.run_program0 n w a [] []
  · simpa [expectedPieces] using ShiTMPieceSchedule.run_program1 n w a [] []
  · simpa [expectedPieces] using ShiTMPieceSchedule.run_program2 n w a [] []

/-- Starting with retained resource headers and an archived input, compute
one embedded output wire directly in its final readout register. The original
output index and archive are restored, so the next copy can use them again. -/
theorem prepare_copy_run (copy : Fin 3) (n w a out : Nat) (tail : List Cell)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (hret : Retained n w a S)
    (ha : S ShiTMReadoutIndexLoad.archive = List.replicate out Cell.mark ++ Cell.mirrorEnd :: tail)
    (h3 : S (core 3) = []) (hout : out < n+(w+(a+1))) :
    ∃ (v' : Sig) (U : ∀ k, List (TopGam k)),
      (run copy)^[copyCost copy n w a out S] (some ⟨some (clearLabel 0), v, S⟩) =
        some ⟨some (lookupLabel .finished), v', U⟩
      ∧ U (destination copy) = List.replicate (depth (expectedPieces copy n w a) out) Cell.mark
      ∧ U (core 0) = [] ∧ U (core 3) = []
      ∧ ∀ k, Stable copy k → U k = S k := by
  let C := cleared copy S
  have hretC : Retained n w a C := by
    simpa [C, cleared, Retained, core, destination, slot, ShiTMReadoutLookup.destination,
      ShiTMReadout.wire] using hret
  have h3C : C (core 3) = [] := by
    simpa [C, cleared, Ne.symm (destination_ne_3 copy), core] using h3
  obtain ⟨T, vt, ht, htables, hretT, h3T, hframeT⟩ :=
    ShiTMPieceController.run_program_finished_frame copy n w a none C hretC h3C
  have hCtables : ShiTMPieceController.tableState C = ([], []) := by
    simp [ShiTMPieceController.tableState, C, cleared, Ne.symm (destination_ne_1 copy),
      Ne.symm (destination_ne_2 copy), core]
  rw [hCtables, program_tables] at htables
  have hTframe (k : TopK) (hk1 : k ≠ core 1) (hk2 : k ≠ core 2) (hk3 : k ≠ core 3) : T k = C k := by
    by_cases h0 : k = .inr (0 : Fin 4)
    · subst k; exact hretT.1.trans hretC.1.symm
    by_cases h1 : k = .inr (1 : Fin 4)
    · subst k; exact hretT.2.1.trans hretC.2.1.symm
    by_cases h2 : k = .inr (2 : Fin 4)
    · subst k; exact hretT.2.2.trans hretC.2.2.symm
    exact hframeT k ⟨hk1, hk2, hk3, h0, h1, h2⟩
  have hTa : T ShiTMReadoutIndexLoad.archive = List.replicate out Cell.mark ++ Cell.mirrorEnd :: tail := by
    rw [hTframe _ (by decide) (by decide) (by decide)]
    simpa [C, cleared, ShiTMReadoutIndexLoad.archive, core, destination, slot,
      ShiTMReadoutLookup.destination, ShiTMReadout.wire] using ha
  have hT0 : T (core 0) = S (core 0) := by
    rw [hTframe _ (by decide) (by decide) (by decide)]
    simp [C, cleared, Ne.symm (destination_ne_0 copy), core]
  have hTd : T (destination copy) = [] := by
    rw [hTframe _ (destination_ne_1 copy) (destination_ne_2 copy) (destination_ne_3 copy)]
    simp [C, cleared]
  let I := Function.update T (core 0) (List.replicate out Cell.mark)
  have hil := ShiTMReadoutIndexLoad.load_run out tail vt T hTa h3T
  have hi : (run copy)^[(S (core 0)).length+2*out+3]
      (some ⟨some (indexLabel .clear), vt, T⟩) =
      some ⟨some (indexLabel .finished), none, I⟩ := by
    have h := index_run copy _ _ _ _ _ hil
    simpa only [ShiTMReadoutIndexLoad.index, hT0] using h
  have hI1 : I (core 1) = pieceCells Prod.fst (expectedPieces copy n w a) := by
    simpa [I, core, ShiTMPieceController.tableState] using congrArg Prod.fst htables
  have hI2 : I (core 2) = pieceCells Prod.snd (expectedPieces copy n w a) := by
    simpa [I, core, ShiTMPieceController.tableState] using congrArg Prod.snd htables
  obtain ⟨vu, U, hl, hd, h0U, h3U, _, _, hfU⟩ := ShiTMReadoutLookup.lookup_run
    (slot copy) (expectedPieces copy n w a) out none I
    (by simpa only [ShiTMPieceController.expectedPieces_width] using hout)
    (by simp [I]) hI1 hI2 (by simpa [I, core] using h3T)
  have hlt := lookup_run copy _ _ _ _ _ hl
  have hc := clear_all_run copy v S
  have htt := table_run copy _ _ _ _ _ ht
  have hj1 : (run copy)^[1] (some ⟨some (tableLabel (.finished copy)), vt, T⟩) =
      some ⟨some (indexLabel .clear), vt, T⟩ := by
    simp [run, ShiTMSubroutine.run, machine, tableLabel, step, stepAux]
  have hj2 : (run copy)^[1] (some ⟨some (indexLabel .finished), none, I⟩) =
      some ⟨some (lookupLabel .wire), none, I⟩ := by rfl
  have h01 := ShiTMFanout.iterTwo (run copy) _ _ _ _ _ hc htt
  have h02 := ShiTMFanout.iterTwo (run copy) _ _ _ _ _ h01 hj1
  have h03 := ShiTMFanout.iterTwo (run copy) _ _ _ _ _ h02 hi
  have h04 := ShiTMFanout.iterTwo (run copy) _ _ _ _ _ h03 hj2
  have h05 := ShiTMFanout.iterTwo (run copy) _ _ _ _ _ h04 hlt
  refine ⟨vu, U, h05, ?_, h0U, h3U, ?_⟩
  · simpa [I, hTd] using hd
  · intro k hk
    rcases hk with ⟨hk0, hk1, hk2, hk3, hkd, hk10⟩
    rw [hfU k hk0 hk1 hk2 hk3 hkd hk10]
    simp only [I, Function.update_of_ne hk0]
    rw [hTframe k hk1 hk2 hk3]
    exact cleared_frame copy S k hk1 hk2 hkd

/-- Each four-piece local-copy lookup has a uniform linear bound. -/
theorem lookupCost_le (copy : Fin 3) (n w a out : Nat) :
    cost (ShiTMPieceController.expectedPieces copy n w a) out ≤ 20*(n+w+a+1) := by
  have h := ShiTMReadoutLookup.cost_le_table_sum (ShiTMPieceController.expectedPieces copy n w a) out
  fin_cases copy <;>
    simp [ShiTMPieceController.expectedPieces, copyPieces0, copyPieces1, copyPieces2] at h ⊢ <;> omega

def initialWorkSize (copy : Fin 3) (S : ∀ k, List (TopGam k)) : Nat :=
  (S (core 0)).length+(S (core 1)).length+(S (core 2)).length+(S (destination copy)).length

/-- Preparing a readout wire costs a linear function of the retained
resource lengths plus the four old work stacks that must be cleared. -/
theorem copyCost_le (copy : Fin 3) (n w a out L : Nat)
    (S : ∀ k, List (TopGam k)) (hlen : n+w+a+1 ≤ L)
    (hout : out < n+(w+(a+1))) :
    copyCost copy n w a out S ≤ initialWorkSize copy S+415*L := by
  have hp := ShiTMPieceController.programCost_le copy n w a
  have hl := lookupCost_le copy n w a out
  unfold copyCost clearCost initialWorkSize
  omega

theorem expected_depth_eq_value (copy : Fin 3) (n w a out : Nat) :
    depth (ShiTMPieceController.expectedPieces copy n w a) out =
      ShiTMReadout.amplifierValues n w a out (slot copy) := by
  fin_cases copy <;> simp [ShiTMPieceController.expectedPieces, ShiTMReadout.amplifierValues, slot]

theorem other_wire_stable (copy : Fin 3) (h : Fin 4) (hne : h ≠ slot copy) :
    Stable copy (ShiTMReadout.wire h) := by
  have hval : h.val ≠ copy.val := by
    intro he
    apply hne
    apply Fin.ext
    exact he
  fin_cases copy <;> fin_cases h <;>
    simp_all [Stable, destination, slot, ShiTMReadoutLookup.destination, ShiTMReadout.wire, core]

/-- Executable preparation of any of the three amplifier readout operands,
with the exact value used by the already checked majority-readout emitter.
Other readout operands can have arbitrary contents and are preserved. -/
theorem prepare_readout_operand (copy : Fin 3) (n w a : Nat)
    (out : Fin (n+(w+(a+1)))) (tail : List Cell)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (hret : ShiTMPieceController.Retained n w a S)
    (ha : S ShiTMReadoutIndexLoad.archive = List.replicate out.val Cell.mark ++ Cell.mirrorEnd :: tail)
    (h3 : S (core 3) = []) :
    ∃ (v' : Sig) (U : ∀ k, List (TopGam k)),
      (run copy)^[copyCost copy n w a out.val S] (some ⟨some (clearLabel 0), v, S⟩) =
        some ⟨some (lookupLabel .finished), v', U⟩
      ∧ U (ShiTMReadout.wire (slot copy)) =
          List.replicate (ShiTMReadout.amplifierValues n w a out.val (slot copy)) Cell.mark
      ∧ U (core 0) = [] ∧ U (core 3) = []
      ∧ (∀ h, h ≠ slot copy → U (ShiTMReadout.wire h) = S (ShiTMReadout.wire h))
      ∧ ∀ k, Stable copy k → U k = S k := by
  obtain ⟨v', U, hr, hd, h0, ht, hf⟩ := prepare_copy_run copy n w a out.val tail v S hret ha h3 out.isLt
  refine ⟨v', U, hr, ?_, h0, ht, ?_, hf⟩
  · simpa only [expected_depth_eq_value] using hd
  · intro h hh
    exact hf _ (other_wire_stable copy h hh)

end ShiTMReadoutCopy
