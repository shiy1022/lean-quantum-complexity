import ReversibleEfficientSimulationSize
import ReversibleEfficientSimulation

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversible ShiReversibleTM

/-- Every polynomial-time classical TM2 string computation admits an exact, clean, polynomial-time-uniform family of polynomial-size reversible quantum circuits. The input is retained, every quantum work wire is zero at the endpoint, and the separate fixed-width output register decodes to the entire classical output string. -/
theorem efficient_reversible_simulation {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) :
    ∃ c d : Nat,∃ q : Polynomial Nat,
      let F := paddedMachineUniformFamily M.tm M.inputAlphabet M.outputAlphabet c d
      ShiBQP.Uniform F ∧ ShiBQP.WellFormed F ∧ ShiBQP.PolyBounded F ∧
        (∀ n,(F.circ n).flatten.length ≤ q.eval n) ∧
        PaddedMachineFamilyClean M.tm M.inputAlphabet M.outputAlphabet c d f ∧
        (∀ n (x : Bits n),outputDecode (outputCode (n+(n+c)^d*machinePushBound M.tm+1)
          (f (List.ofFn x)))=f (List.ofFn x)) := by
  obtain ⟨c,d,hu,hw,hp,hclean,hdecode⟩ := efficientReversibleSimulation M
  obtain ⟨q,hq⟩ := paddedMachineUniformFamily_gates_polynomial M.tm M.inputAlphabet M.outputAlphabet c d
  exact ⟨c,d,q,hu,hw,hp,hq,hclean,hdecode⟩

end ShiReversibleGenerator
