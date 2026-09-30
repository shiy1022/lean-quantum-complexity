import «AMPUNI-uniform-thresholds»

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiQMAVariableRounds
open ShiShallow ShiClassQMA ShiClassQMAAmpX

/-- The explicit three-copy verifier iterated a fixed number of rounds. -/
noncomputable def iter (F : QMAFamily) : Nat → QMAFamily
  | 0 => F
  | r + 1 => ampFamilyX (iter F r)

/-- At each input length, choose a possibly different number of rounds. -/
noncomputable def varying (F : QMAFamily) (rounds : Nat → Nat) : QMAFamily where
  wit n := (iter F (rounds n)).wit n
  anc n := (iter F (rounds n)).anc n
  circ n := (iter F (rounds n)).circ n
  out n := (iter F (rounds n)).out n

/-- Each round triples the witness register. -/
theorem iter_wit (F : QMAFamily) (r n : Nat) :
    (iter F r).wit n = 3 ^ r * F.wit n := by
  induction r with
  | zero => simp [iter]
  | succ r ih =>
      rw [iter, ampFamilyX_resource_identities_and_regularity.1, ih, pow_succ]
      ring

/-- An exact affine recurrence for the ancilla count. -/
theorem iter_anc_identity (F : QMAFamily) (r n : Nat) :
    2 * (iter F r).anc n + (2 * n + 3) =
      3 ^ r * (2 * F.anc n + 2 * n + 3) := by
  induction r with
  | zero => simp [iter]; omega
  | succ r ih =>
      rw [iter, ampFamilyX_resource_identities_and_regularity.2.1, pow_succ]
      calc
        2 * (2 * n + 3 * (iter F r).anc n + 3) + (2 * n + 3) =
            3 * (2 * (iter F r).anc n + (2 * n + 3)) := by omega
        _ = 3 * (3 ^ r * (2 * F.anc n + 2 * n + 3)) := by rw [ih]
        _ = 3 ^ r * 3 * (2 * F.anc n + 2 * n + 3) := by ring

/-- A bound for all ancillas, including fan-out and majority readout. -/
theorem iter_anc_le (F : QMAFamily) (r n : Nat) :
    (iter F r).anc n ≤ 3 ^ r * (F.anc n + 2 * n + 3) := by
  have h := iter_anc_identity F r n
  nlinarith

/-- An exact affine recurrence for circuit depth. -/
theorem iter_depth_identity (F : QMAFamily) (r n : Nat) :
    2 * depth ((iter F r).circ n) + 113 =
      3 ^ r * (2 * depth (F.circ n) + 113) := by
  induction r with
  | zero => simp [iter]
  | succ r ih =>
      rw [iter, ampFamilyX_resource_identities_and_regularity.2.2.2.1, pow_succ]
      calc
        2 * (3 * depth ((iter F r).circ n) + 113) + 113 =
            3 * (2 * depth ((iter F r).circ n) + 113) := by omega
        _ = 3 * (3 ^ r * (2 * depth (F.circ n) + 113)) := by rw [ih]
        _ = 3 ^ r * 3 * (2 * depth (F.circ n) + 113) := by ring

/-- A bound for circuit depth across any number of rounds. -/
theorem iter_depth_le (F : QMAFamily) (r n : Nat) :
    depth ((iter F r).circ n) ≤ 3 ^ r * (depth (F.circ n) + 113) := by
  have h := iter_depth_identity F r n
  nlinarith

/-- One bound for all non-input wires. -/
theorem iter_wit_add_anc_le (F : QMAFamily) (r n : Nat) :
    (iter F r).wit n + (iter F r).anc n ≤
      3 ^ r * (F.wit n + F.anc n + 2 * n + 3) := by
  have hw := iter_wit F r n
  have ha := iter_anc_le F r n
  nlinarith

/-- Well-formed layers are preserved for every fixed iteration count. -/
theorem iter_wellFormed (F : QMAFamily) (r : Nat)
    (hF : ShiBQP.WellFormed F.toFamily) :
    ShiBQP.WellFormed (iter F r).toFamily := by
  induction r with
  | zero => exact hF
  | succ r ih =>
      exact ampFamilyX_resource_identities_and_regularity.2.2.2.2.1 (iter F r) ih

/-- The length-dependent family inherits well-formedness pointwise. -/
theorem variable_wellFormed (F : QMAFamily) (rounds : Nat → Nat)
    (hF : ShiBQP.WellFormed F.toFamily) :
    ShiBQP.WellFormed (varying F rounds).toFamily := by
  intro n l hl
  exact iter_wellFormed F (rounds n) hF n l hl

end ShiQMAVariableRounds

#print axioms ShiQMAVariableRounds.variable_wellFormed
#print axioms ShiQMAVariableRounds.iter_wit_add_anc_le
