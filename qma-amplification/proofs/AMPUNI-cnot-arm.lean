import «AMPUNI-cnot-machine-blocks»
import «AMPUNI-cnot-midpoint»
import «AMPUNI-cnot-final-layout»

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

open Turing Turing.TM2

namespace ShiTMLayoutMachine

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat) (x y z : A)
    (hxy : f^[a] x = y) (hyz : f^[b] y = z) : f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- Complete CNOT arm after tag dispatch. -/
theorem cnot_arm
    (ps : List (Nat × Nat)) (i j : Nat) (rest : List Cell)
    (pa ta pb tb : List Cell) (v : Sig) (S : ∀ k, List (Gam k))
    (hi : i < (ps.map Prod.fst).sum) (hj : j < (ps.map Prod.fst).sum)
    (hSsrc : S 11 = (ShiBQP.encNat i ++ ShiBQP.encNat j).map bit ++ rest)
    (hS0 : S 0 = []) (hS1 : S 1 = pieceCells Prod.fst ps)
    (hS2 : S 2 = pieceCells Prod.snd ps) (hS3 : S 3 = [])
    (hS4 : S 4 = [.delim]) (hS6 : S 6 = []) (hS7 : S 7 = [])
    (hS8 : S 8 = pa ++ .mirrorEnd :: ta)
    (hS9 : S 9 = pb ++ .mirrorEnd :: tb) (hS10 : S 10 = [])
    (hS12 : S 12 = [])
    (hpa : pa.reverse = pieceCells Prod.fst ps)
    (hpb : pb.reverse = pieceCells Prod.snd ps)
    (hpaGood : ∀ y ∈ pa, y ≠ .mirrorEnd)
    (hpbGood : ∀ y ∈ pb, y ≠ .mirrorEnd) :
    ∃ (vout : Sig) (U : ∀ k, List (Gam k))
      (a1 a2 b1 b2 : Nat) (garbage : List Cell),
      a1 ≤ (pieceCells Prod.fst ps).length ∧
      a2 ≤ (pieceCells Prod.snd ps).length ∧
      b1 ≤ (pieceCells Prod.fst ps).length ∧
      b2 ≤ (pieceCells Prod.snd ps).length ∧
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[
          (i + 1) + (j + 1) + 1 +
          ((cost ps j + (depth ps j + 0 + 3) +
              (a1 + a2 + 2 * (pa.length + pb.length) + 8)) + 1 + 1 +
                (garbage.length + 1) + (i + 1) + 1) +
          ((cost ps i + (depth ps i + 4 + 3) +
              (b1 + b2 + 2 * (pa.length + pb.length) + 8)) + 1 +
                ((cnotChunk ps i j).length + 1))]
        (some { l := some (b .readCnotFirst), var := v, stk := S }) =
          some { l := some (b .instructionDone), var := vout, stk := U }
      ∧ U 13 = (cnotChunk ps i j).reverse ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = []
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ garbage = []
      ∧ a1 = residualPiece ps j ∧ a2 = residualBase ps j
      ∧ b1 = residualPiece ps i ∧ b2 = residualBase ps i
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  let T1 := Function.update (Function.update S 11
    ((ShiBQP.encNat j).map bit ++ rest)) 12 (List.replicate i .mark ++ S 12)
  let v1 := scanVar i v
  have hsrc1 : S 11 = (ShiBQP.encNat i).map bit ++
      ((ShiBQP.encNat j).map bit ++ rest) := by
    simpa only [List.map_append, List.append_assoc] using hSsrc
  have hrun1 :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[i + 1]
        (some { l := some (b .readCnotFirst), var := v, stk := S }) =
          some { l := some (b .readCnotSecond), var := v1, stk := T1 } := by
    simpa only [T1, v1] using
      scan_cnot_first i ((ShiBQP.encNat j).map bit ++ rest) v S hsrc1
  let T2 := Function.update (Function.update T1 11 rest) 0
    (List.replicate j .mark ++ T1 0)
  let v2 := scanVar j v1
  have hT1src : T1 11 = (ShiBQP.encNat j).map bit ++ rest := by simp [T1]
  have hrun2 :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[j + 1]
        (some { l := some (b .readCnotSecond), var := v1, stk := T1 }) =
          some { l := some (b .finishCnotMid), var := v2, stk := T2 } := by
    simpa only [T2, v2] using scan_cnot_second j rest v1 T1 hT1src
  have h12 := iterTwo _ (i + 1) (j + 1) _ _ _ hrun1 hrun2
  have hT2seven : T2 7 = [] := by simp [T2, T1, hS7]
  let T3 := Function.update T2 7 [tagCell 0, .continueCnotMid]
  have hsetup := finish_cnot_mid_to_wire v2 T2
  have h123 :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[
          ((i + 1) + (j + 1)) + 1]
        (some { l := some (b .readCnotFirst), var := v, stk := S }) =
          some { l := some (b .wire), var := v2, stk := T3 } :=
    iterTwo _ ((i + 1) + (j + 1)) 1 _ _ _ h12
      (by simpa only [T3, hT2seven] using hsetup)
  have hT30 : T3 0 = List.replicate j .mark := by simp [T3, T2, T1, hS0]
  have hT31 : T3 1 = pieceCells Prod.fst ps := by simp [T3, T2, T1, hS1]
  have hT32 : T3 2 = pieceCells Prod.snd ps := by simp [T3, T2, T1, hS2]
  have hT33 : T3 3 = [] := by simp [T3, T2, T1, hS3]
  have hT34 : T3 4 = [.delim] := by simp [T3, T2, T1, hS4]
  have hT36 : T3 6 = [] := by simp [T3, T2, T1, hS6]
  have hT37 : T3 7 = [tagCell 0, .continueCnotMid] := by simp [T3]
  have hT38 : T3 8 = pa ++ .mirrorEnd :: ta := by simp [T3, T2, T1, hS8]
  have hT39 : T3 9 = pb ++ .mirrorEnd :: tb := by simp [T3, T2, T1, hS9]
  have hT310 : T3 10 = [] := by simp [T3, T2, T1, hS10]
  have hT312 : T3 12 = List.replicate i .mark := by simp [T3, T2, T1, hS12]
  obtain ⟨vm, W, a1, a2, garbage, ha1, ha2, hmid, hW0, hW1, hW2, hW3, hW4,
      hW6, hW7, hW8, hW9, hW10, hW11, hW12, hW13, hgarbage, ha1eq, ha2eq⟩ :=
    cnot_midpoint ps i j pa ta pb tb v2 T3 hj hT30 hT31 hT32 hT33 hT34 hT36 hT37
      hT38 hT39 hT310 hT312 hpa hpb hpaGood hpbGood
  let qmid := (cost ps j + (depth ps j + 0 + 3) +
      (a1 + a2 + 2 * (pa.length + pb.length) + 8)) + 1 + 1 +
        (garbage.length + 1) + (i + 1) + 1
  have hpreMid :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[
          (((i + 1) + (j + 1)) + 1) + qmid]
        (some { l := some (b .readCnotFirst), var := v, stk := S }) =
          some { l := some (b .wire), var := vm, stk := W } :=
    iterTwo _ (((i + 1) + (j + 1)) + 1) qmid _ _ _ h123
      (by simpa [qmid] using hmid)
  obtain ⟨vout, U, b1, b2, hb1, hb2, hfinal, hacc, hU6, hU7, hU11, hU12,
      hU0, hU1, hU2, hb1eq, hb2eq, hU3, hU4, hU8, hU9, hU10⟩ :=
    cnot_final_layout ps i j pa ta pb tb vm W hi hW0 hW1 hW2 hW3 hW4 hW6 hW7
      (by simpa [hW8, hS8]) (by simpa [hW9, hS9]) hW10 hpa hpb hpaGood hpbGood
  let qfinal := (cost ps i + (depth ps i + 4 + 3) +
      (b1 + b2 + 2 * (pa.length + pb.length) + 8)) + 1 +
        ((cnotChunk ps i j).length + 1)
  have hall := iterTwo _ ((((i + 1) + (j + 1)) + 1) + qmid) qfinal _ _ _ hpreMid
    (by simpa [qfinal] using hfinal)
  have hT3src : T3 11 = rest := by simp [T3, T2, T1]
  have hWsrc : W 11 = rest := by simpa only [hT3src] using hW11
  have hT3acc : T3 13 = S 13 := by simp [T3, T2, T1]
  have hWacc : W 13 = S 13 := by simpa only [hT3acc] using hW13
  refine ⟨vout, U, a1, a2, b1, b2, garbage, ha1, ha2, hb1, hb2,
    ?_, ?_, hU6, hU7, ?_, ?_, hU0, hU1, hU2, hgarbage,
    ha1eq, ha2eq, hb1eq, hb2eq, hU3, hU4, ?_, ?_, hU10⟩
  · exact hall
  · simpa only [hWacc] using hacc
  · simpa only [hWsrc] using hU11
  · simpa only [hW12] using hU12
  · rw [hU8, hW8, hT38]
    exact hS8.symm
  · rw [hU9, hW9, hT39]
    exact hS9.symm

end ShiTMLayoutMachine
