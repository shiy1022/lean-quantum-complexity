import «AMPUNI-operand-reader»
import «AMPUNI-one-index-layout-reverse-exact»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Turing Turing.TM2

namespace ShiTMLayoutMachine

def operandScanVar (i : Nat) (v : Sig) : Sig :=
  pop (List.foldl (fun w y => pop w (some y)) v
    (List.replicate i (bit true))) (some (bit false))

def operandScanStacks (i : Nat) (rest : List Cell)
    (S : ∀ k, List (Gam k)) : ∀ k, List (Gam k) :=
  Function.update (Function.update S 11 rest) 0
    (List.replicate i .mark ++ S 0)

def operandWireStacks (t : Fin 5) (S : ∀ k, List (Gam k)) : ∀ k, List (Gam k) :=
  Function.update S 7 [tagCell t, .continueSingle]

private theorem iterTwoExactArm {A : Type} (f : A → A) (a b : Nat) (x y z : A)
    (hxy : f^[a] x = y) (hyz : f^[b] y = z) : f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

noncomputable def oneIndexCost (t : Fin 5) (ps : List (Nat × Nat)) (i : Nat)
    (pa pb : List Cell) : Nat :=
  (i + 1) + 1 +
    (cost ps i + (depth ps i + t.val + 3) +
      (residualPiece ps i + residualBase ps i + 2 * (pa.length + pb.length) + 8) + 1 +
        ((encodedChunk t ps i).length + 1))

/-- Fixed-cost one-index handler, suitable as an element body for nested iteration. -/
theorem one_index_arm_exact
    (t : Fin 5) (ht : t.val < 4) (ps : List (Nat × Nat)) (i : Nat)
    (rest : List Cell) (pa ta pb tb : List Cell) (v : Sig)
    (S : ∀ k, List (Gam k))
    (hw : i < (ps.map Prod.fst).sum)
    (hSsrc : S 11 = (ShiBQP.encNat i).map bit ++ rest)
    (hS0 : S 0 = []) (hS1 : S 1 = pieceCells Prod.fst ps)
    (hS2 : S 2 = pieceCells Prod.snd ps) (hS3 : S 3 = [])
    (hS4 : S 4 = [.delim]) (hS6 : S 6 = []) (hS7 : S 7 = [])
    (hS8 : S 8 = pa ++ .mirrorEnd :: ta)
    (hS9 : S 9 = pb ++ .mirrorEnd :: tb) (hS10 : S 10 = [])
    (hpa : pa.reverse = pieceCells Prod.fst ps)
    (hpb : pb.reverse = pieceCells Prod.snd ps)
    (hpaGood : ∀ y ∈ pa, y ≠ .mirrorEnd)
    (hpbGood : ∀ y ∈ pb, y ≠ .mirrorEnd) :
    ∃ (vout : Sig) (U : ∀ k, List (Gam k)),
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[
          oneIndexCost t ps i pa pb]
        (some { l := some (operandLoopLabel t), var := v, stk := S }) =
          some { l := some (b .instructionDone), var := vout, stk := U }
      ∧ U 13 = (encodedChunk t ps i).reverse ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = S 12
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  let vscan := operandScanVar i v
  let Tscan := operandScanStacks i rest S
  have hscan :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[i + 1]
        (some { l := some (operandLoopLabel t), var := v, stk := S }) =
          some { l := some (operandFinishLabel t), var := vscan, stk := Tscan } := by
    simpa only [vscan, Tscan, operandScanVar, operandScanStacks] using
      (scan_one_operand t ht i rest v S hSsrc).1
  have hTscan7 : Tscan 7 = [] := by
    simp [Tscan, operandScanStacks, hS7]
  let Twire := operandWireStacks t Tscan
  have hsetup :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[1]
        (some { l := some (operandFinishLabel t), var := vscan, stk := Tscan }) =
          some { l := some (b .wire), var := vscan, stk := Twire } := by
    simpa only [Twire, operandWireStacks, hTscan7] using
      finish_one_operand_to_wire t ht vscan Tscan
  have hprefix :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[(i + 1) + 1]
        (some { l := some (operandLoopLabel t), var := v, stk := S }) =
          some { l := some (b .wire), var := vscan, stk := Twire } :=
    iterTwoExactArm _ (i + 1) 1 _ _ _ hscan hsetup
  have hW0 : Twire 0 = List.replicate i .mark := by
    simp [Twire, operandWireStacks, Tscan, operandScanStacks, hS0]
  have hW1 : Twire 1 = pieceCells Prod.fst ps := by
    simp [Twire, operandWireStacks, Tscan, operandScanStacks, hS1]
  have hW2 : Twire 2 = pieceCells Prod.snd ps := by
    simp [Twire, operandWireStacks, Tscan, operandScanStacks, hS2]
  have hW3 : Twire 3 = [] := by
    simp [Twire, operandWireStacks, Tscan, operandScanStacks, hS3]
  have hW4 : Twire 4 = [.delim] := by
    simp [Twire, operandWireStacks, Tscan, operandScanStacks, hS4]
  have hW6 : Twire 6 = [] := by
    simp [Twire, operandWireStacks, Tscan, operandScanStacks, hS6]
  have hW7 : Twire 7 = [tagCell t, .continueSingle] := by simp [Twire, operandWireStacks]
  have hW8 : Twire 8 = pa ++ .mirrorEnd :: ta := by
    simp [Twire, operandWireStacks, Tscan, operandScanStacks, hS8]
  have hW9 : Twire 9 = pb ++ .mirrorEnd :: tb := by
    simp [Twire, operandWireStacks, Tscan, operandScanStacks, hS9]
  have hW10 : Twire 10 = [] := by
    simp [Twire, operandWireStacks, Tscan, operandScanStacks, hS10]
  obtain ⟨vout, U, harm, hacc, hU6, hU7, hU11, hU12,
      hU0, hU1, hU2, _, _, hU3, hU4, hU8, hU9, hU10⟩ :=
    one_index_layout_then_reverse_exact t ps i pa ta pb tb vscan Twire hw hW0 hW1 hW2 hW3
      hW4 hW6 hW7 hW8 hW9 hW10 hpa hpb hpaGood hpbGood
  let qarm := cost ps i + (depth ps i + t.val + 3) +
    (residualPiece ps i + residualBase ps i + 2 * (pa.length + pb.length) + 8) + 1 +
      ((encodedChunk t ps i).length + 1)
  have hall := iterTwoExactArm _ ((i + 1) + 1) qarm _ _ _ hprefix
    (by simpa only [qarm] using harm)
  have hW13 : Twire 13 = S 13 := by
    simp [Twire, operandWireStacks, Tscan, operandScanStacks]
  have hW11 : Twire 11 = rest := by
    simp [Twire, operandWireStacks, Tscan, operandScanStacks]
  have hW12 : Twire 12 = S 12 := by
    simp [Twire, operandWireStacks, Tscan, operandScanStacks]
  refine ⟨vout, U, ?_, ?_, hU6, hU7, ?_, ?_, hU0, hU1, hU2,
    hU3, hU4, ?_, ?_, hU10⟩
  · simpa only [oneIndexCost, qarm] using hall
  · simpa only [hW13] using hacc
  · simpa only [hW11] using hU11
  · simpa only [hW12] using hU12
  · rw [hU8, hW8]
    exact hS8.symm
  · rw [hU9, hW9]
    exact hS9.symm

end ShiTMLayoutMachine
