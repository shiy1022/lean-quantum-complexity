import ReversibleMachineUniformFamilyData

set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleGateBridge

theorem castLayered_gateCount {a b : Nat} (h : a=b) (gs : ShiShallow.Layered a) :
    (castLayered h gs).flatten.length=gs.flatten.length := by cases h; rfl

/-- Direct polynomial gate-count bound for the actual uniform quantum family. -/
theorem paddedMachineUniformFamily_gates_polynomial (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d : Nat) :
    ∃ q : Polynomial Nat,∀ n,((paddedMachineUniformFamily tm e₀ e₁ c d).circ n).flatten.length ≤ q.eval n := by
  obtain ⟨q,hq⟩ := paddedMachineQuantumCircuit_gates_polynomial tm e₀ e₁ ((Polynomial.X+Polynomial.C c)^d)
  refine ⟨q,?_⟩
  intro n
  change (castLayered _ _).flatten.length ≤ _
  rw [castLayered_gateCount]
  have hb : Polynomial.eval n ((Polynomial.X+Polynomial.C c)^d) = (n+c)^d := by
    simp only [Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  rw [← hb]
  exact hq n

end ShiReversibleGenerator
