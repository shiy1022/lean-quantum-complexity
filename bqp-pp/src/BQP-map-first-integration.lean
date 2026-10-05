import «BQP-map-first-polytime»
import «BQP-prefix-integration»

set_option autoImplicit false
namespace BQPProgram

/-- The witness-preserving preprocessor is a proved machine construction.
Its remaining premise is precisely the string compiler's polynomial runtime. -/
theorem familyPreprocess_polyTime_of_compiler (C : Checker) (F : ShiClass.Family)
    (hcompile : PvsNP.PolyTimeComputable (fun x => C.encode (familyProgram F x))) :
    Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair
      (familyPreprocess C F)) :=
  BQPMapFirst.map_first_polyTime _ hcompile

/-- Compilation, witness retention, and normalization compose with the concrete
opcode checker. Proving hcompile and the combined router remains separate. -/
theorem normalized_family_polyTime_of_compiler (C : Checker) (F : ShiClass.Family) (d : ℕ)
    (hcompile : PvsNP.PolyTimeComputable (fun x => C.encode (familyProgram F x))) :
    PvsNP.PolyTimeChecker (BQPCounting.pairedPrefix (familyResidue C F d)) := by
  rw [normalized_family_factorization]
  exact BQPMapFirst.checker_preprocess _ _ hcompile (normalized_opcode_checker_polyTime C (d : ZMod 8))

end BQPProgram
