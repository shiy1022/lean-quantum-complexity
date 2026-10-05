import Definitions.Def_ShiQMAVariableRounds
import Definitions.Def_ShiQMAErrorIteration
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false

namespace ShiQMAVariableRounds
open ShiClassQMA ShiQMAErrorIteration Polynomial

noncomputable def polynomialFamily (F : QMAFamily) (p : Polynomial ℕ) : QMAFamily :=
  varying F (fun n => roundsFor (p.eval n))

end ShiQMAVariableRounds
