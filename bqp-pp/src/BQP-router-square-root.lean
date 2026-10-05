import «BQP-typed-polytime»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BQPRouterArithmetic
open Turing Polynomial

def bits : ℕ → ℕ → List Bool
  | 0, _ => []
  | k+1, n => (n % 2 == 1) :: bits k (n/2)

/-- The already reconstructed restoring-square-root machine is a genuine typed
polynomial-time computation of the router's exact threshold seed. -/
theorem squareRoot_polyTime :
    Nonempty (TM2ComputableInPolyTime ShiBQP.encNat id
      (fun h => bits (h+7) (Nat.sqrt (2*4^(h+3))))) := by
  obtain ⟨tm,ei,eo,hgood,_⟩ := BQPChecked.reference35.1
  refine ⟨{ tm := tm
            inputAlphabet := ei
            outputAlphabet := eo
            time := C 2 * X * X + C 27 * X + C 67
            outputsFun := ?_ }⟩
  intro h
  let ho := Classical.choice (hgood bits (fun _ => rfl) (fun _ _ => rfl) h)
  have ht : ho.steps ≤ (C 2 * X * X + C 27 * X + C 67 : Polynomial ℕ).eval
      (ShiBQP.encNat h).length := by
    have hb := ho.steps_le_m
    simp only [ShiBQP.encNat, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil, eval_add, eval_mul, eval_C, eval_X]
    nlinarith
  exact { ho with steps_le_m := ht }

end BQPRouterArithmetic
