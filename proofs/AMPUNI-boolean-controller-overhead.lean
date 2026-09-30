import «AMPUNI-boolean-controller-bounds»
import «AMPUNI-finite-stack-growth»

set_option autoImplicit false
open Turing Turing.TM2
noncomputable section
namespace ShiTMBooleanWrapper
open ShiTMLayoutMachine (Sig bit)
open ShiTMRetainedTop
variable {L : Type} [DecidableEq L] [Fintype L]

/-- Every finite typed body admits a Boolean boundary wrapper with linear
runtime overhead on its verified runs. The constant depends only on the
machine, not on its input, output, runtime, or final work-stack contents.
This does not assert termination of the body on unverified inputs. -/
theorem finite_body_overhead (M : L → Stmt TopGam L Sig) (main terminal : L)
    (hterminal : M terminal = .halt) :
    ∃ C : Nat, ∀ (xs ys : List Bool) (bodySteps : Nat) (v : Sig)
      (S : ∀ k, List (TopGam k)),
      (ShiTMSubroutine.run M)^[bodySteps]
        (some ⟨some main, none, initialTop xs⟩) = some ⟨some terminal, v, S⟩ →
      S cellOutput = (ys.map bit).reverse →
      Nonempty (Turing.TM2OutputsInTime (finiteMachine M main terminal) xs (some ys)
        (C*bodySteps+4*xs.length+28)) := by
  obtain ⟨C, hC⟩ := ShiTMStackGrowth.finite_growth M
  refine ⟨2*C+1, ?_⟩
  intro xs ys bodySteps v S hr ho
  exact valid_input_outputs_bound M main terminal hterminal C hC xs ys bodySteps v S hr ho

end ShiTMBooleanWrapper
