import «AMPUNI-concrete-instruction-front»
import «AMPUNI-concrete-dispatch-step»
import «AMPUNI-cnot-arm-exact»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Turing Turing.TM2

namespace ShiTMLayoutMachine

private theorem iterThreeCnot {A : Type} (f : A → A) (a b c : Nat)
    (x y z w : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z)
    (hzw : f^[c] z = w) : f^[a + b + c] x = w := by
  rw [show a + b + c = c + (b + a) from by omega,
    Function.iterate_add_apply f c (b + a), Function.iterate_add_apply f b a,
    hxy, hyz, hzw]

/-- Parse a valid CNOT source record, dispatch it, and emit both mapped operands. -/
theorem concrete_cnot_instruction
    (ps : List (Nat × Nat)) (i j : Nat) (rest : List Cell)
    (pa ta pb tb : List Cell) (v : Sig) (S : ∀ k, List (Gam k))
    (hi : i < (ps.map Prod.fst).sum) (hj : j < (ps.map Prod.fst).sum)
    (hSsrc : S 11 =
      (ShiBQP.encNat 4 ++ ShiBQP.encNat i ++ ShiBQP.encNat j).map bit ++ rest)
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
    ∃ (vout : Sig) (U : ∀ k, List (Gam k)),
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[
          (4 + 1 + (4 + 1)) + 1 + cnotArmCost ps i j pa pb]
        (some { l := some (b .parseTag), var := v, stk := S }) =
          some { l := some (b .instructionDone), var := vout, stk := U }
      ∧ U 13 = (cnotChunk ps i j).reverse ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = []
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  have hsrc : S 11 =
      List.map bit (ShiBQP.encNat 4 ++ (ShiBQP.encNat i ++ ShiBQP.encNat j)) ++ rest := by
    simpa only [List.append_assoc] using hSsrc
  obtain ⟨v1, T, hfront, hT11, hT7, hT12, hframe, _⟩ :=
    concrete_instruction_front 4 (by decide)
      (ShiBQP.encNat i ++ ShiBQP.encNat j) rest v S hsrc hS12
  have hT7' : T 7 = tagCell (4 : Fin 5) :: [] := by
    simpa [hS7] using hT7
  let R := Function.update T 7 []
  have hdispatch :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[1]
        (some { l := some (b .instructionDispatch), var := v1, stk := T }) =
          some { l := some (b .readCnotFirst), var := some (tagCell (4 : Fin 5)), stk := R } := by
    have h := instruction_dispatch_step (4 : Fin 5) [] v1 T hT7'
    rw [instructionArmLabel_cnot] at h
    simpa only [R] using h
  have hkeep : ∀ k, k ≠ 11 → k ≠ 12 → k ≠ 7 → R k = S k := by
    intro k hk11 hk12 hk7
    rw [show R k = T k by simp [R, Function.update_of_ne hk7]]
    exact hframe k hk11 hk12 hk7
  have hR11 : R 11 =
      (ShiBQP.encNat i ++ ShiBQP.encNat j).map bit ++ rest := by
    simpa [R] using hT11
  have hR12 : R 12 = [] := by simpa [R] using hT12
  have hR7 : R 7 = [] := by simp [R]
  have hR0 : R 0 = [] := by rw [hkeep 0 (by decide) (by decide) (by decide)]; exact hS0
  have hR1 : R 1 = pieceCells Prod.fst ps := by
    rw [hkeep 1 (by decide) (by decide) (by decide)]; exact hS1
  have hR2 : R 2 = pieceCells Prod.snd ps := by
    rw [hkeep 2 (by decide) (by decide) (by decide)]; exact hS2
  have hR3 : R 3 = [] := by rw [hkeep 3 (by decide) (by decide) (by decide)]; exact hS3
  have hR4 : R 4 = [.delim] := by
    rw [hkeep 4 (by decide) (by decide) (by decide)]; exact hS4
  have hR6 : R 6 = [] := by rw [hkeep 6 (by decide) (by decide) (by decide)]; exact hS6
  have hR8 : R 8 = pa ++ .mirrorEnd :: ta := by
    rw [hkeep 8 (by decide) (by decide) (by decide)]; exact hS8
  have hR9 : R 9 = pb ++ .mirrorEnd :: tb := by
    rw [hkeep 9 (by decide) (by decide) (by decide)]; exact hS9
  have hR10 : R 10 = [] := by
    rw [hkeep 10 (by decide) (by decide) (by decide)]; exact hS10
  have hR13 : R 13 = S 13 := hkeep 13 (by decide) (by decide) (by decide)
  obtain ⟨vout, U, harm, hacc, hU6, hU7, hU11, hU12, hU0, hU1, hU2,
      hU3, hU4, hU8, hU9, hU10⟩ :=
    cnot_arm_exact ps i j rest pa ta pb tb (some (tagCell (4 : Fin 5))) R hi hj
      hR11 hR0 hR1 hR2 hR3 hR4 hR6 hR7 hR8 hR9 hR10 hR12
      hpa hpb hpaGood hpbGood
  refine ⟨vout, U, ?_, ?_, hU6, hU7, hU11, hU12, hU0, hU1, hU2,
    hU3, hU4, ?_, ?_, hU10⟩
  · exact iterThreeCnot (A := Option (Cfg Gam Label Sig)) _ (4 + 1 + (4 + 1)) 1
      (cnotArmCost ps i j pa pb)
      (some { l := some (b .parseTag), var := v, stk := S })
      (some { l := some (b .instructionDispatch), var := v1, stk := T })
      (some { l := some (b .readCnotFirst), var := some (tagCell (4 : Fin 5)), stk := R })
      (some { l := some (b .instructionDone), var := vout, stk := U })
      hfront hdispatch harm
  · rw [hacc, hR13]
  · rw [hU8, hR8]
    exact hS8.symm
  · rw [hU9, hR9]
    exact hS9.symm

end ShiTMLayoutMachine
