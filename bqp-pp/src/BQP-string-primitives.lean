import «AMPUNI-subroutine-lift»

set_option autoImplicit false
namespace BQPStringPrimitives
open Turing Turing.TM2

abbrev prefixMachine (b : Bool) : FinTM2 where
  K := Unit
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  ΛFin := inferInstance
  σ := Unit
  initialState := ()
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := fun _ => .push () (fun _ => b) .halt

set_option backward.isDefEq.respectTransparency false in
def prefix_outputs (b : Bool) (s : List Bool) :
    TM2OutputsInTime (prefixMachine b) s (some (b::s)) 1 := by
  refine { steps := 1, steps_le_m := le_refl _, evals_in_steps := ?_ }
  change ShiTMSubroutine.run (prefixMachine b).m (some (initList (prefixMachine b) s)) =
    some (haltList (prefixMachine b) (b::s))
  simp [ShiTMSubroutine.run, step, stepAux, prefixMachine, initList, haltList]
  all_goals (funext u; cases u; rfl)

 theorem prefix_polyTime (b : Bool) :
    Nonempty (TM2ComputableInPolyTime id id (fun s : List Bool => b::s)) := by
  refine ⟨{ tm := prefixMachine b
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.C 1
            outputsFun := ?_ }⟩
  intro s
  simpa only [id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl,
    List.map_id, Polynomial.eval_C] using prefix_outputs b s

/-- A bijective letter renaming changes only the output alphabet interpretation. -/
theorem rename_polyTime (e : Bool ≃ Bool) :
    Nonempty (TM2ComputableInPolyTime id id (List.map e)) := by
  let A := idComputableInPolyTime (id : List Bool → List Bool)
  refine ⟨{ tm := A.tm
            inputAlphabet := A.inputAlphabet
            outputAlphabet := A.outputAlphabet.trans e
            time := A.time
            outputsFun := ?_ }⟩
  intro s
  simpa [List.map_map, Function.comp_def] using A.outputsFun s

end BQPStringPrimitives
