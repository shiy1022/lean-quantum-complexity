import «BQP-router-threshold-values»
import «BQP-router-family-seed»
import «BQP-binary-add-pair»
import «BQP-pair-generation»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BQPRouterArithmetic
open Turing BQPProgram BQPBinaryAdd

/-- Prefixing a fixed finite string is a proved finite composition. -/
theorem prefix_string_polyTime (p : List Bool) :
    PvsNP.PolyTimeComputable (fun s => p++s) := by
  induction p with
  | nil => exact ⟨idComputableInPolyTime (id : List Bool → List Bool)⟩
  | cons b p ih =>
      simpa only [PvsNP.PolyTimeComputable, Function.comp_def, List.cons_append] using
        BQPTypedPolyTime.comp ih (BQPStringPrimitives.prefix_polyTime b)

theorem constant_polyTime (p : List Bool) :
    PvsNP.PolyTimeComputable (fun _ => p) := by
  simpa only [PvsNP.PolyTimeComputable, Function.comp_def, List.append_nil] using
    BQPTypedPolyTime.comp empty_polyTime (prefix_string_polyTime p)

theorem shift_polyTime (k : ℕ) : PvsNP.PolyTimeComputable (shift k) :=
  prefix_string_polyTime (List.replicate k false)

/-- Addition closure uses the actual tagged-pair generator and complete adder. -/
theorem add_polyTime (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable f) (hg : PvsNP.PolyTimeComputable g) :
    PvsNP.PolyTimeComputable (fun x => add (f x) (g x) false) := by
  have h := BQPGeneralPolyTime.comp (Sum.inl false)
    (BQPPairGeneration.pair_polyTime f g hf hg) BQPBinaryAddPair.polyTime
  exact h

theorem family_power_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) (k : ℕ) :
    PvsNP.PolyTimeComputable (fun x => power (familyH F x+1+k)) := by
  have hz : PvsNP.PolyTimeComputable (fun x => List.replicate (familyH F x) false) := by
    simpa only [PvsNP.PolyTimeComputable, Function.comp_def, List.map_replicate,
      Equiv.swap_apply_left] using
      BQPTypedPolyTime.comp (BQPOpcodeCount.family_polyTime F hu)
        (BQPStringPrimitives.rename_polyTime (Equiv.swap true false))
  have hp := BQPTypedPolyTime.comp hz (shift_polyTime (1+k))
  have h := BQPJoint.polyTimeComputable_append _ _ hp (constant_polyTime [true])
  have he (x : List Bool) : shift (1+k) (List.replicate (familyH F x) false) ++ [true] =
      power (familyH F x+1+k) := by
    simp only [shift, power, ← List.replicate_add]
    congr 2 <;> omega
  simpa only [PvsNP.PolyTimeComputable, Function.comp_def, he] using h

/-- All five exact thresholds of the actual uniform family are computed in
polynomial time, with no assumed arithmetic or generator certificate. -/
theorem family_threshold_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) (i : Fin 5) :
    PvsNP.PolyTimeComputable (fun x => thresholds (familyH F x+1) i) := by
  have hp := family_power_polyTime F hu 5
  have hs := family_squareRoot_polyTime F hu
  have hs1 := BQPTypedPolyTime.comp hs (shift_polyTime 1)
  have hs2 := BQPTypedPolyTime.comp hs (shift_polyTime 2)
  have ha1 := add_polyTime _ _ hp hs1
  have ha2 := add_polyTime _ _ hp hs2
  have ha3 := add_polyTime _ _ ha2 (constant_polyTime (power 4))
  fin_cases i
  · exact family_power_polyTime F hu 4
  · exact hp
  · exact ha1
  · exact ha2
  · exact ha3

end BQPRouterArithmetic
