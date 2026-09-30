import «AMPUNI-repeat-loop-induction»

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiTMRepeatController

/-- A uniform bound on the source-call cost and intermediate output length
bounds the entire preloaded loop. The bound is restricted to the finite
prefix actually visited by the controller. -/
theorem preloadedCost_le_linear
    (n R A B : Nat) (resultLen times : Nat → Nat)
    (htimes : ∀ r, r ≤ R → times r ≤ A)
    (hlength : ∀ r, r ≤ R → resultLen r ≤ B) :
    ∀ (r q : Nat), r + q ≤ R →
      preloadedCost n resultLen times r q ≤
        (q + 1) * (A + 2 * (B + 1) + n + 3) + n + 2 := by
  intro r q
  induction q generalizing r with
  | zero =>
      intro hr
      have ht := htimes r (by omega)
      simp only [preloadedCost]
      omega
  | succ q ih =>
      intro hr
      have ht := htimes r (by omega)
      have hl := hlength r (by omega)
      have hi := ih (r + 1) (by omega)
      have htwice : 2 * (resultLen r + 1) ≤ 2 * (B + 1) := by
        omega
      have hmul : (q + 1 + 1) * (A + 2 * (B + 1) + n + 3) =
          (A + 2 * (B + 1) + n + 3) +
            (q + 1) * (A + 2 * (B + 1) + n + 3) := by ring
      simp only [preloadedCost]
      rw [hmul]
      omega

end ShiTMRepeatController
