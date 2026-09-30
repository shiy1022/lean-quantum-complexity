import «AMPUNI-layout-runner-exact»
import «AMPUNI-cnot-midpoint»
import «AMPUNI-concrete-output-reverse»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Turing Turing.TM2

namespace ShiTMLayoutMachine

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat) (x y z : A)
    (hxy : f^[a] x = y) (hyz : f^[b] y = z) : f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

def cnotChunk (ps : List (Nat × Nat)) (i j : Nat) : List Cell :=
  (ShiBQP.encNat 4 ++ ShiBQP.encNat (depth ps i) ++ ShiBQP.encNat (depth ps j)).map bit

/-- The second CNOT layout pass emits tag 4 and the first image above the saved second-image
field, then reverses the complete three-field instruction onto the accumulator. -/
theorem cnot_final_layout
    (ps : List (Nat × Nat)) (i j : Nat) (pa ta pb tb : List Cell)
    (v : Sig) (S : ∀ k, List (Gam k))
    (hi : i < (ps.map Prod.fst).sum)
    (hS0 : S 0 = List.replicate i .mark)
    (hS1 : S 1 = pieceCells Prod.fst ps)
    (hS2 : S 2 = pieceCells Prod.snd ps)
    (hS3 : S 3 = []) (hS4 : S 4 = [.delim])
    (hS6 : S 6 = cnotTail ps j)
    (hS7 : S 7 = [tagCell 4, .continueCnotEnd])
    (hS8 : S 8 = pa ++ .mirrorEnd :: ta)
    (hS9 : S 9 = pb ++ .mirrorEnd :: tb) (hS10 : S 10 = [])
    (hpa : pa.reverse = pieceCells Prod.fst ps)
    (hpb : pb.reverse = pieceCells Prod.snd ps)
    (hpaGood : ∀ y ∈ pa, y ≠ .mirrorEnd)
    (hpbGood : ∀ y ∈ pb, y ≠ .mirrorEnd) :
    ∃ (vout : Sig) (U : ∀ k, List (Gam k)) (r1 r2 : Nat),
      r1 ≤ (pieceCells Prod.fst ps).length ∧
      r2 ≤ (pieceCells Prod.snd ps).length ∧
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[
          (cost ps i + (depth ps i + 4 + 3) +
            (r1 + r2 + 2 * (pa.length + pb.length) + 8)) + 1 +
              ((cnotChunk ps i j).length + 1)]
        (some { l := some (b .wire), var := v, stk := S }) =
          some { l := some (b .instructionDone), var := vout, stk := U }
      ∧ U 13 = (cnotChunk ps i j).reverse ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = S 11 ∧ U 12 = S 12
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ r1 = residualPiece ps i ∧ r2 = residualBase ps i
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  obtain ⟨vL, T, hrun, hout, hT4, hT0, hT1, hT2, hT7,
      hT8, hT9, hT10, hT3, hr1, hr2, hframe⟩ :=
    layoutRunnerExact (4 : Fin 5) [.continueCnotEnd] ps i pa ta pb tb v S hi hS0 hS1 hS2 hS3
      hS4 hS7 hS8 hS9 hS10
      (by simpa using hpa) (by simpa using hpb)
      (fun _ y hy => by simp [notMirrorEnd, pop, hpaGood y hy])
      (fun _ => rfl)
      (fun _ y hy => by simp [notMirrorEnd, pop, hpbGood y hy])
      (fun _ => rfl)
  let r1 := residualPiece ps i
  let r2 := residualBase ps i
  let q4 := cost ps i + (depth ps i + (4 : Fin 5).val + 3) +
    (r1 + r2 + 2 * (pa.length + pb.length) + 8)
  have houtNum : T 6 =
      (ShiBQP.encNat 4 ++ ShiBQP.encNat (depth ps i)).map bit ++ S 6 := by
    simpa [layoutStack] using hout
  have hT6 : T 6 = cnotChunk ps i j := by
    rw [houtNum, hS6]
    simp only [cnotChunk, cnotTail, List.map_append, List.append_assoc]
  have hdone := done_to_reverse .continueCnotEnd (Or.inr rfl) vL T [] hT7
  let R := Function.update T 7 []
  have htoReverse :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[q4 + 1]
        (some { l := some (b .wire), var := v, stk := S }) =
          some { l := some (b .reverseOutput), var := pop vL (some .continueCnotEnd), stk := R } :=
    iterTwo _ q4 1 _ _ _ (by simpa only [q4] using hrun) (by simpa only [R] using hdone)
  have hR6 : R 6 = cnotChunk ps i j := by simp [R, hT6]
  obtain ⟨vout, U, hall, hacc, hU6, hUframe, hUeval⟩ :=
    reverse_chunk_into_accumulator (q4 + 1)
      { l := some (b .wire), var := v, stk := S }
      (pop vL (some .continueCnotEnd)) S R (cnotChunk ps i j) htoReverse hR6
  have outside13 : ∀ x : Fin 11, (13 : Fin 14) ≠ layoutStack x := by
    intro x h
    have hv := congrArg (fun z : Fin 14 => z.val) h
    simp [layoutStack] at hv
    omega
  have outside11 : ∀ x : Fin 11, (11 : Fin 14) ≠ layoutStack x := by
    intro x h
    have hv := congrArg (fun z : Fin 14 => z.val) h
    simp [layoutStack] at hv
    omega
  have outside12 : ∀ x : Fin 11, (12 : Fin 14) ≠ layoutStack x := by
    intro x h
    have hv := congrArg (fun z : Fin 14 => z.val) h
    simp [layoutStack] at hv
    omega
  have hR13 : R 13 = S 13 := by simp [R, hframe 13 outside13]
  have hR11 : R 11 = S 11 := by simp [R, hframe 11 outside11]
  have hR12 : R 12 = S 12 := by simp [R, hframe 12 outside12]
  have hT0' : T 0 = [] := by simpa [layoutStack] using hT0
  have hT1' : T 1 = pieceCells Prod.fst ps := by simpa [layoutStack] using hT1
  have hT2' : T 2 = pieceCells Prod.snd ps := by simpa [layoutStack] using hT2
  have hT3' : T 3 = [] := by simpa [layoutStack] using hT3
  have hT4' : T 4 = [.delim] := by simpa [layoutStack] using hT4
  have hT8' : T 8 = S 8 := by simpa [layoutStack] using hT8
  have hT9' : T 9 = S 9 := by simpa [layoutStack] using hT9
  have hT10' : T 10 = [] := by simpa [layoutStack] using hT10
  refine ⟨vout, U, r1, r2, hr1, hr2, ?_, ?_, hU6, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [q4] using hall
  · simpa only [hR13] using hacc
  · rw [hUframe 7 (by decide) (by decide)]
    simp [R]
  · rw [hUframe 11 (by decide) (by decide), hR11]
  · rw [hUframe 12 (by decide) (by decide), hR12]
  · rw [hUframe 0 (by decide) (by decide)]
    simp [R, hT0']
  · rw [hUframe 1 (by decide) (by decide)]
    simp [R, hT1']
  · rw [hUframe 2 (by decide) (by decide)]
    simp [R, hT2']
  · rw [hUframe 3 (by decide) (by decide)]
    simp [R, hT3']
  · rw [hUframe 4 (by decide) (by decide)]
    simp [R, hT4']
  · rw [hUframe 8 (by decide) (by decide)]
    simp [R, hT8']
  · rw [hUframe 9 (by decide) (by decide)]
    simp [R, hT9']
  · rw [hUframe 10 (by decide) (by decide)]
    simp [R, hT10']

end ShiTMLayoutMachine
