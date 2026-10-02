import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Definitions.Def_ShiQMACenteredGapGeneralSchedule

set_option autoImplicit false

namespace ShiQMACenteredGap

noncomputable def schedulePolynomial (A D : Nat) : Polynomial ℕ :=
  Polynomial.monomial D (2 ^ A)
noncomputable def gapPolynomial (q p : Polynomial ℕ) : Polynomial ℕ :=
  schedulePolynomial
    (3 * (Nat.log 2 (q.eval 1 + 1) + 4) + Nat.log 2 (p.eval 1 + 1) + 4)
    (3 * q.natDegree + p.natDegree)

end ShiQMACenteredGap
