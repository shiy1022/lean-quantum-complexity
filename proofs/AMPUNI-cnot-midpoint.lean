import «AMPUNI-layout-runner-exact»
import «AMPUNI-cnot-machine-blocks»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Turing Turing.TM2

namespace ShiTMLayoutMachine

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat) (x y z : A)
    (hxy : f^[a] x = y) (hyz : f^[b] y = z) : f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

def cnotTail (ps : List (Nat × Nat)) (j : Nat) : List Cell :=
  (ShiBQP.encNat (depth ps j)).map bit

/-- From the second-operand layout entry to the first-operand layout entry.  The zero tag
emitted for the second operand is stripped, scratch stack 3 is drained, and the saved first
operand is restored as the next bare wire. -/
theorem cnot_midpoint
    (ps : List (Nat × Nat)) (i j : Nat) (pa ta pb tb : List Cell)
    (v : Sig) (S : ∀ k, List (Gam k))
    (hj : j < (ps.map Prod.fst).sum)
    (hS0 : S 0 = List.replicate j .mark)
    (hS1 : S 1 = pieceCells Prod.fst ps)
    (hS2 : S 2 = pieceCells Prod.snd ps)
    (hS3 : S 3 = []) (hS4 : S 4 = [.delim]) (hS6 : S 6 = [])
    (hS7 : S 7 = [tagCell 0, .continueCnotMid])
    (hS8 : S 8 = pa ++ .mirrorEnd :: ta)
    (hS9 : S 9 = pb ++ .mirrorEnd :: tb) (hS10 : S 10 = [])
    (hS12 : S 12 = List.replicate i .mark)
    (hpa : pa.reverse = pieceCells Prod.fst ps)
    (hpb : pb.reverse = pieceCells Prod.snd ps)
    (hpaGood : ∀ y ∈ pa, y ≠ .mirrorEnd)
    (hpbGood : ∀ y ∈ pb, y ≠ .mirrorEnd) :
    ∃ (vout : Sig) (W : ∀ k, List (Gam k)) (r1 r2 : Nat) (garbage : List Cell),
      r1 ≤ (pieceCells Prod.fst ps).length ∧
      r2 ≤ (pieceCells Prod.snd ps).length ∧
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[
          (cost ps j + (depth ps j + 0 + 3) +
            (r1 + r2 + 2 * (pa.length + pb.length) + 8)) + 1 + 1 +
              (garbage.length + 1) + (i + 1) + 1]
        (some { l := some (b .wire), var := v, stk := S }) =
          some { l := some (b .wire), var := vout, stk := W }
      ∧ W 0 = List.replicate i .mark
      ∧ W 1 = pieceCells Prod.fst ps ∧ W 2 = pieceCells Prod.snd ps
      ∧ W 3 = [] ∧ W 4 = [.delim] ∧ W 6 = cnotTail ps j
      ∧ W 7 = [tagCell 4, .continueCnotEnd]
      ∧ W 8 = S 8 ∧ W 9 = S 9 ∧ W 10 = []
      ∧ W 11 = S 11 ∧ W 12 = [] ∧ W 13 = S 13
      ∧ garbage = []
      ∧ r1 = residualPiece ps j ∧ r2 = residualBase ps j := by
  obtain ⟨vL, T, hrun, hout, hT4, hT0, hT1, hT2, hT7,
      hT8, hT9, hT10, hT3, hr1, hr2, hframe⟩ :=
    layoutRunnerExact (0 : Fin 5) [.continueCnotMid] ps j pa ta pb tb v S hj hS0 hS1 hS2 hS3
      hS4 hS7 hS8 hS9 hS10
      (by simpa using hpa) (by simpa using hpb)
      (fun _ y hy => by simp [notMirrorEnd, pop, hpaGood y hy])
      (fun _ => rfl)
      (fun _ y hy => by simp [notMirrorEnd, pop, hpbGood y hy])
      (fun _ => rfl)
  let r1 := residualPiece ps j
  let r2 := residualBase ps j
  let q0 := cost ps j + (depth ps j + (0 : Fin 5).val + 3) +
    (r1 + r2 + 2 * (pa.length + pb.length) + 8)
  let payload := cnotTail ps j
  have houtNum : T 6 = (ShiBQP.encNat 0 ++ ShiBQP.encNat (depth ps j)).map bit ++ S 6 := by
    simpa [layoutStack] using hout
  have hT6 : T 6 = .delim :: payload := by
    rw [houtNum, hS6, List.append_nil]
    rfl
  have hdone := done_to_cnot_strip vL T [] hT7
  let A := Function.update T 7 []
  have hrunA :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[q0 + 1]
        (some { l := some (b .wire), var := v, stk := S }) =
          some { l := some (b .stripCnotZero), var := pop vL (some .continueCnotMid), stk := A } :=
    iterTwo _ q0 1 _ _ _ (by simpa only [q0] using hrun) (by simpa only [A] using hdone)
  have hA6 : A 6 = .delim :: payload := by simp [A, hT6]
  have hstrip := strip_cnot_zero (pop vL (some .continueCnotMid)) A payload hA6
  let B := Function.update A 6 payload
  have hrunB :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[(q0 + 1) + 1]
        (some { l := some (b .wire), var := v, stk := S }) =
          some ({
            l := some (b .clearScratch)
            var := pop (pop vL (some .continueCnotMid)) (some .delim)
            stk := B } : Cfg Gam Label Sig) :=
    iterTwo _ (q0 + 1) 1 _ _ _ hrunA (by simpa only [B] using hstrip)
  let garbage := B 3
  have hclear := clear_layout_scratch garbage
    (pop (pop vL (some .continueCnotMid)) (some .delim)) B rfl
  let C := clearedScratchStacks garbage B
  let vC := pop (garbage.foldl (fun w y => pop w (some y))
    (pop (pop vL (some .continueCnotMid)) (some .delim))) none
  have hrunC :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[
          ((q0 + 1) + 1) + (garbage.length + 1)]
        (some { l := some (b .wire), var := v, stk := S }) =
          some { l := some (b .restoreCnotFirst), var := vC, stk := C } :=
    iterTwo _ ((q0 + 1) + 1) (garbage.length + 1) _ _ _ hrunB
      (by simpa only [C, vC] using hclear)
  have outside12 : ∀ x : Fin 11, (12 : Fin 14) ≠ layoutStack x := by
    intro x h
    have hv := congrArg (fun z : Fin 14 => z.val) h
    simp [layoutStack] at hv
    omega
  have hT12 : T 12 = S 12 := hframe 12 outside12
  have hC12 : C 12 = List.replicate i .mark := by
    simp [C, clearedScratchStacks, B, A, hT12, hS12]
  let saved := List.replicate i Cell.mark
  have hrestore := restore_cnot_first saved vC C (by simpa only [saved] using hC12)
  let D := restoredStacks saved C
  let vD := restoreVar saved vC
  have hrunD :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[
          (((q0 + 1) + 1) + (garbage.length + 1)) + (i + 1)]
        (some { l := some (b .wire), var := v, stk := S }) =
          some { l := some (b .finishCnotEnd), var := vD, stk := D } := by
    have hslen : saved.length + 1 = i + 1 := by simp [saved]
    exact iterTwo _ (((q0 + 1) + 1) + (garbage.length + 1)) (i + 1) _ _ _ hrunC
      (by simpa only [D, vD, hslen] using hrestore)
  have hD7 : D 7 = [] := by simp [D, restoredStacks, C, clearedScratchStacks, B, A]
  have hfinish := finish_cnot_end_to_wire vD D
  let W := Function.update D 7 [tagCell 4, .continueCnotEnd]
  have hall :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[
          ((((q0 + 1) + 1) + (garbage.length + 1)) + (i + 1)) + 1]
        (some { l := some (b .wire), var := v, stk := S }) =
          some { l := some (b .wire), var := vD, stk := W } :=
    iterTwo _ ((((q0 + 1) + 1) + (garbage.length + 1)) + (i + 1)) 1 _ _ _ hrunD
      (by simpa only [W, hD7] using hfinish)
  have hT0' : T 0 = [] := by simpa [layoutStack] using hT0
  have hT1' : T 1 = pieceCells Prod.fst ps := by simpa [layoutStack] using hT1
  have hT2' : T 2 = pieceCells Prod.snd ps := by simpa [layoutStack] using hT2
  have hT4' : T 4 = [.delim] := by simpa [layoutStack] using hT4
  have hT8' : T 8 = S 8 := by simpa [layoutStack] using hT8
  have hT9' : T 9 = S 9 := by simpa [layoutStack] using hT9
  have hT10' : T 10 = [] := by simpa [layoutStack] using hT10
  have outside11 : ∀ x : Fin 11, (11 : Fin 14) ≠ layoutStack x := by
    intro x h
    have hv := congrArg (fun z : Fin 14 => z.val) h
    simp [layoutStack] at hv
    omega
  have outside13 : ∀ x : Fin 11, (13 : Fin 14) ≠ layoutStack x := by
    intro x h
    have hv := congrArg (fun z : Fin 14 => z.val) h
    simp [layoutStack] at hv
    omega
  have hT11 : T 11 = S 11 := hframe 11 outside11
  have hT13 : T 13 = S 13 := hframe 13 outside13
  refine ⟨vD, W, r1, r2, garbage, hr1, hr2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simpa [q0, Nat.add_assoc] using hall
  · simp [W, D, restoredStacks, saved, C, clearedScratchStacks, B, A, hT0']
  · simp [W, D, restoredStacks, C, clearedScratchStacks, B, A, hT1']
  · simp [W, D, restoredStacks, C, clearedScratchStacks, B, A, hT2']
  · simp [W, D, restoredStacks, C, clearedScratchStacks]
  · simp [W, D, restoredStacks, C, clearedScratchStacks, B, A, hT4']
  · simp [W, D, restoredStacks, C, clearedScratchStacks, B, payload]
  · simp [W]
  · simp [W, D, restoredStacks, C, clearedScratchStacks, B, A, hT8']
  · simp [W, D, restoredStacks, C, clearedScratchStacks, B, A, hT9']
  · simp [W, D, restoredStacks, C, clearedScratchStacks, B, A, hT10']
  · simp [W, D, restoredStacks, C, clearedScratchStacks, B, A, hT11]
  · simp [W, D, restoredStacks, C, clearedScratchStacks, B, A]
  · simp [W, D, restoredStacks, C, clearedScratchStacks, B, A, hT13]
  · have hT3' : T 3 = [] := by simpa [layoutStack] using hT3
    exact (show B 3 = T 3 by rfl).trans hT3'

end ShiTMLayoutMachine
