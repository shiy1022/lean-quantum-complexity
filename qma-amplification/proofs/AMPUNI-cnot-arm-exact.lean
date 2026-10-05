import «AMPUNI-cnot-arm»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMLayoutMachine

/-- The complete CNOT handler has a cost determined by the parsed operands and layout,
not by any intermediate machine configuration. -/
noncomputable def cnotArmCost (ps : List (Nat × Nat)) (i j : Nat)
    (pa pb : List Cell) : Nat :=
  (i + 1) + (j + 1) + 1 +
    ((cost ps j + (depth ps j + 0 + 3) +
        (residualPiece ps j + residualBase ps j + 2 * (pa.length + pb.length) + 8))
      + 1 + 1 + 1 + (i + 1) + 1) +
    ((cost ps i + (depth ps i + 4 + 3) +
        (residualPiece ps i + residualBase ps i + 2 * (pa.length + pb.length) + 8))
      + 1 + ((cnotChunk ps i j).length + 1))

theorem cnot_arm_exact
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
    ∃ (vout : Sig) (U : ∀ k, List (Gam k)),
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[
          cnotArmCost ps i j pa pb]
        (some { l := some (b .readCnotFirst), var := v, stk := S }) =
          some { l := some (b .instructionDone), var := vout, stk := U }
      ∧ U 13 = (cnotChunk ps i j).reverse ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = []
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  obtain ⟨vout, U, a1, a2, b1, b2, garbage, _, _, _, _, hrun,
    hacc, hU6, hU7, hU11, hU12, hU0, hU1, hU2,
    hgarbage, ha1, ha2, hb1, hb2, hU3, hU4, hU8, hU9, hU10⟩ :=
    cnot_arm ps i j rest pa ta pb tb v S hi hj hSsrc hS0 hS1 hS2 hS3
      hS4 hS6 hS7 hS8 hS9 hS10 hS12 hpa hpb hpaGood hpbGood
  refine ⟨vout, U, ?_, hacc, hU6, hU7, hU11, hU12, hU0, hU1, hU2,
    hU3, hU4, hU8, hU9, hU10⟩
  simpa [cnotArmCost, ha1, ha2, hb1, hb2, hgarbage] using hrun

end ShiTMLayoutMachine
