import ReversibleMachineUniformFamilyClean
import ReversibleMachineUniformFamily
import ReversiblePolynomialMajorant

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversible ShiReversibleTM

/-- Efficient reversible simulation: every actual polynomial-time classical string computation has a polynomial-time-uniform, polynomially bounded, well-formed quantum circuit family with exact full-string output and zero quantum workspace. -/
theorem efficientReversibleSimulation {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) :
    ∃ c d : Nat,
      ShiBQP.Uniform (paddedMachineUniformFamily M.tm M.inputAlphabet M.outputAlphabet c d) ∧
      ShiBQP.WellFormed (paddedMachineUniformFamily M.tm M.inputAlphabet M.outputAlphabet c d) ∧
      ShiBQP.PolyBounded (paddedMachineUniformFamily M.tm M.inputAlphabet M.outputAlphabet c d) ∧
      PaddedMachineFamilyClean M.tm M.inputAlphabet M.outputAlphabet c d f ∧
      (∀ n (x : Bits n),outputDecode (outputCode (n+(n+c)^d*machinePushBound M.tm+1)
        (f (List.ofFn x)))=f (List.ofFn x)) := by
  let c := M.time.eval 1+1
  let d := M.time.natDegree+1
  let time : Polynomial Nat := (Polynomial.X+Polynomial.C c)^d
  have hp : ∀ n,M.time.eval n ≤ time.eval n := by
    intro n
    simpa [time,c,d] using polynomial_shifted_power_bound M.time n
  let N := enlargePolyClock M time hp
  have hc : 0<c := by dsimp [c]; omega
  refine ⟨c,d,paddedMachineUniformFamily_uniform M.tm M.inputAlphabet M.outputAlphabet c d hc,
    paddedMachineUniformFamily_wellFormed _ _ _ _ _,paddedMachineUniformFamily_polyBounded _ _ _ _ _,
    paddedMachineUniformFamily_clean N c d rfl,?_⟩
  intro n x
  have h := polyTime_paddedRawOutputCircuit_decoded N n x
  rw [polyTime_paddedRawOutputCircuit_output] at h
  simpa only [N,enlargePolyClock,time,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C] using h

end ShiReversibleGenerator
