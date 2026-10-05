import «BQP-prefix-outputs»
import «BQP-family-counting»

set_option autoImplicit false
namespace BQPProgram

/-- The normalized opcode checker has a concrete polynomial-time machine,
 without any compiler or router runtime hypothesis. -/
theorem normalized_opcode_checker_polyTime (C : Checker) (d : ZMod 8) :
    PvsNP.PolyTimeChecker (BQPCounting.pairedPrefix (C.relation d)) :=
  BQPPrefixMachine.pairedPrefix_polyTime _ (C.polyTime d)

/-- The preprocessing target retains every witness bit, including the two
 normalization bits, while replacing the instance by its compiled program. -/
def familyPreprocess (C : Checker) (F : ShiClass.Family)
    (p : List Bool × List Bool) : List Bool × List Bool :=
  (C.encode (familyProgram F p.1), p.2)

/-- Normalization can follow compilation, using the normalized opcode machine
 just constructed. Polynomial time of familyPreprocess remains to be proved. -/
theorem normalized_family_factorization (C : Checker) (F : ShiClass.Family) (d : ℕ) :
    BQPCounting.pairedPrefix (familyResidue C F d) =
      (BQPCounting.pairedPrefix (C.relation (d : ZMod 8))) ∘ familyPreprocess C F := by
  funext p
  rcases p with ⟨x,w⟩
  cases w with
  | nil => rfl
  | cons a w => cases w <;> rfl

end BQPProgram
