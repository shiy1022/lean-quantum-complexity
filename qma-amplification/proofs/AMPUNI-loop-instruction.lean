import «AMPUNI-loop-machine»
import «AMPUNI-concrete-single-instruction»
import «AMPUNI-concrete-cnot-instruction»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Turing Turing.TM2

namespace ShiTMLayoutMachine

/-- A well-scoped source instruction, with the original circuit width in its type. -/
inductive SourceRecord (ps : List (Nat × Nat)) where
  | single (t : Fin 5) (ht : t.val < 4) (i : Nat)
      (hi : i < (ps.map Prod.fst).sum) : SourceRecord ps
  | cnot (i j : Nat) (hi : i < (ps.map Prod.fst).sum)
      (hj : j < (ps.map Prod.fst).sum) : SourceRecord ps

def SourceRecord.source {ps : List (Nat × Nat)} : SourceRecord ps → List Cell
  | .single t _ i _ => (ShiBQP.encNat t.val ++ ShiBQP.encNat i).map bit
  | .cnot i j _ _ =>
      (ShiBQP.encNat 4 ++ ShiBQP.encNat i ++ ShiBQP.encNat j).map bit

def SourceRecord.target {ps : List (Nat × Nat)} : SourceRecord ps → List Cell
  | .single t _ i _ => encodedChunk t ps i
  | .cnot i j _ _ => cnotChunk ps i j

noncomputable def SourceRecord.cost {ps : List (Nat × Nat)} (pa pb : List Cell) :
    SourceRecord ps → Nat
  | .single t _ i _ =>
      (t.val + 1 + (t.val + 1)) + 1 + oneIndexCost t ps i pa pb
  | .cnot i j _ _ => (4 + 1 + (4 + 1)) + 1 + cnotArmCost ps i j pa pb

/-- Both valid instruction forms have the same repeatable stack postcondition. -/
theorem loop_instruction (ps : List (Nat × Nat)) (r : SourceRecord ps)
    (rest : List Cell) (pa ta pb tb : List Cell) (v : Sig)
    (S : ∀ k, List (Gam k))
    (hSsrc : S 11 = r.source ++ rest)
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
      loopRun^[r.cost pa pb]
        (some { l := some (b .parseTag), var := v, stk := S }) =
          some { l := some (b .instructionDone), var := vout, stk := U }
      ∧ U 13 = r.target.reverse ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = []
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  cases r with
  | single t ht i hi =>
    obtain ⟨vout, U, hrun, hacc, h6, h7, h11, h12, h0, h1, h2,
      h3, h4, h8, h9, h10⟩ :=
      concrete_single_instruction t ht ps i rest pa ta pb tb v S hi
        hSsrc hS0 hS1 hS2 hS3 hS4 hS6 hS7 hS8 hS9 hS10 hS12
        hpa hpb hpaGood hpbGood
    refine ⟨vout, U, ?_, hacc, h6, h7, h11, h12, h0, h1, h2,
      h3, h4, h8, h9, h10⟩
    exact transport_run_to_instructionDone _ _ _ rfl hrun
  | cnot i j hi hj =>
    obtain ⟨vout, U, hrun, hacc, h6, h7, h11, h12, h0, h1, h2,
      h3, h4, h8, h9, h10⟩ :=
      concrete_cnot_instruction ps i j rest pa ta pb tb v S hi hj
        hSsrc hS0 hS1 hS2 hS3 hS4 hS6 hS7 hS8 hS9 hS10 hS12
        hpa hpb hpaGood hpbGood
    refine ⟨vout, U, ?_, hacc, h6, h7, h11, h12, h0, h1, h2,
      h3, h4, h8, h9, h10⟩
    exact transport_run_to_instructionDone _ _ _ rfl hrun

end ShiTMLayoutMachine
