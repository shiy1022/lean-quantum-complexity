import «BQP-program-count-bridge»
import «BQP-normalized-threshold»

set_option autoImplicit false
namespace BQPProgram
open ShiShallow BQPPaths ShiClassPP

def familyH (F : ShiClass.Family) (x : List Bool) : ℕ :=
  hadamardCount (F.circ x.length).flatten

def familyProgram (F : ShiClass.Family) (x : List Bool) : List ℕ :=
  compile (F.circ x.length).flatten (ShiBQP.toBits x) (F.out x.length)

def familyResidue (C : Checker) (F : ShiClass.Family) (d : ℕ)
    (p : List Bool × List Bool) : Bool :=
  C.relation (d : ZMod 8) (C.encode (familyProgram F p.1), p.2)

 theorem family_count (C : Checker) (F : ShiClass.Family) (d : ℕ) (x : List Bool) :
    countAccept (familyResidue C F d) x (2 * familyH F x) =
      circuitCount (F.circ x.length) (ShiBQP.toBits x) (F.out x.length) (d : ZMod 8).val := by
  rw [two_mul]
  exact (circuitCount_checker C (F.circ x.length) (ShiBQP.toBits x)
    (F.out x.length) (d : ZMod 8)).symm

/-- Exact acceptance representation for the residue relation built from the
concrete compiled program and the same polynomial-time single-run checker.
Polynomial time of the preprocessing map is a separate construction obligation. -/
theorem family_acceptance (C : Checker) (F : ShiClass.Family) (x : List Bool) :
    F.accept x.length (ShiBQP.toBits x) = (1 / 2 : ℝ) ^ familyH F x *
      ((BQPCounting.coefficient (familyH F) (familyResidue C F) 0 4 x : ℝ) +
        (BQPCounting.coefficient (familyH F) (familyResidue C F) 1 3 x : ℝ) * Real.sqrt 2) := by
  have h := canonical_acceptance (F.circ x.length) (ShiBQP.toBits x) (F.out x.length)
  simp only [BQPCounting.coefficient, Int.cast_sub, Int.cast_natCast, family_count]
  norm_num only [ZMod.val_natCast, Nat.reduceMod]
  rw [show (0 : ZMod 8).val = 0 by decide,
    show (1 : ZMod 8).val = 1 by decide,
    show (3 : ZMod 8).val = 3 by decide,
    show (4 : ZMod 8).val = 4 by decide]
  simpa only [ShiClass.Family.accept, familyH, mul_comm] using h

end BQPProgram
