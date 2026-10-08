import ReversibleTickResourceHistoryHypotheses

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickRuntimeCapacityPolynomial (tm : Turing.FinTM2) (time : Polynomial Nat) : Polynomial Nat :=
  Polynomial.X+time*Polynomial.C (machinePushBound tm)+Polynomial.C 1

noncomputable def tickRuntimeWidthPolynomial (tm : Turing.FinTM2) (time : Polynomial Nat) : Polynomial Nat :=
  Polynomial.C (tickWidthSlope tm)*tickRuntimeCapacityPolynomial tm time+Polynomial.C (tickWidthOffset tm)

noncomputable def tickRuntimeHistoryBudgetPolynomial (tm : Turing.FinTM2) (time : Polynomial Nat) : Polynomial Nat :=
  resourceCounterBudgetPolynomial tm time+Polynomial.C (tickSizeBound tm+17)

noncomputable def tickRuntimeHistoryLayerPolynomial (tm : Turing.FinTM2) (time : Polynomial Nat) : Polynomial Nat :=
  time*tickRuntimeWidthPolynomial tm time*Polynomial.C (37*tickSizeBound tm+1)

theorem tickRuntimeCapacityPolynomial_eval (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat) :
    (tickRuntimeCapacityPolynomial tm time).eval n=n+time.eval n*machinePushBound tm+1 := by
  simp [tickRuntimeCapacityPolynomial]

theorem tickRuntimeWidthPolynomial_eval (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat) :
    (tickRuntimeWidthPolynomial tm time).eval n=configurationWidth tm (n+time.eval n*machinePushBound tm+1) := by
  rw [tickWidth_affine]
  simp [tickRuntimeWidthPolynomial,tickRuntimeCapacityPolynomial]

theorem tickRuntimeHistoryBudgetPolynomial_eval (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat) :
    (tickRuntimeHistoryBudgetPolynomial tm time).eval n=(resourceCounterBudgetPolynomial tm time).eval n+tickSizeBound tm+17 := by
  simp [tickRuntimeHistoryBudgetPolynomial,Nat.add_assoc]

theorem tickRuntimeHistoryLayerPolynomial_eval (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat) :
    (tickRuntimeHistoryLayerPolynomial tm time).eval n=
      time.eval n*configurationWidth tm (n+time.eval n*machinePushBound tm+1)*(37*tickSizeBound tm+1) := by
  simp only [tickRuntimeHistoryLayerPolynomial,Polynomial.eval_mul,Polynomial.eval_C,tickRuntimeWidthPolynomial_eval]

end ShiReversibleGenerator
