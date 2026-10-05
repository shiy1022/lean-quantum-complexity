import «BQP-bit-blocks-integration»

set_option autoImplicit false
namespace BQPBitBlocks
open Turing Turing.TM2

abbrev machine (no yes : List ℕ) : FinTM2 where
  K := K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := 0
  k₁ := 1
  Γ := Gam
  Λ := Unit
  main := ()
  ΛFin := inferInstance
  σ := Bool
  initialState := false
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := program no yes

theorem initial_eq (no yes : List ℕ) (s : List Bool) :
    initList (machine no yes) s = cfg false s [] := by
  apply congrArg (fun S => (⟨some (),false,S⟩ : Cfg Gam Unit Bool))
  funext k; fin_cases k <;> rfl

theorem final_eq (no yes : List ℕ) (s : List Bool) :
    (⟨none,false,tapes [] s⟩ : Cfg Gam Unit Bool) = haltList (machine no yes) s := by
  apply congrArg (fun S => (⟨none,false,S⟩ : Cfg Gam Unit Bool))
  funext k; fin_cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
def outputs (no yes : List ℕ) (s : List Bool) :
    TM2OutputsInTime (machine no yes) s
      (some (BQPOpcodeEmission.encode (render no yes s))) (s.length+1) := by
  refine { steps := s.length+1, steps_le_m := le_refl _, evals_in_steps := ?_ }
  change (ShiTMSubroutine.run (program no yes))^[s.length+1]
    (some (initList (machine no yes) s)) = some (haltList (machine no yes) _)
  rw [initial_eq, ← final_eq]
  simpa only [List.append_nil] using render_run no yes s [] false

theorem polyTime (no yes : List ℕ) :
    PvsNP.PolyTimeComputable (fun s => BQPOpcodeEmission.encode (render no yes s)) := by
  refine ⟨{ tm := machine no yes
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.X + Polynomial.C 1
            outputsFun := ?_ }⟩
  intro s
  simpa only [id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl,
    List.map_id, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] using outputs no yes s
end BQPBitBlocks

namespace BQPProgram

theorem load_polyTime (C : Checker) :
    PvsNP.PolyTimeComputable (fun s => C.encode (load s)) := by
  simpa only [checker_encode_eq, render_load] using BQPBitBlocks.polyTime [1] [5,1]

theorem endpoint_polyTime (C : Checker) :
    PvsNP.PolyTimeComputable (fun s => C.encode (endpoint s)) := by
  simpa only [checker_encode_eq, render_endpoint] using BQPBitBlocks.polyTime [5,8,5,1] [8,1]

theorem return_polyTime (C : Checker) :
    PvsNP.PolyTimeComputable (fun s : List Bool => C.encode (List.replicate s.length 0)) := by
  simpa only [checker_encode_eq, render_return] using BQPBitBlocks.polyTime [0] [0]

end BQPProgram
