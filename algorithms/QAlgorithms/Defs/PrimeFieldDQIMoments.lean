import QAlgorithms.Defs.DQI
import QAlgorithms.Defs.FieldCodeGeometry

noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.PrimeFieldDQI

/-- Already-normalized real polynomial probability weights; 2607.28120 pp.3,13.
The normalization binder excludes zero or arbitrary unnormalized polynomials.
No averaging over the acceptance sets occurs. -/
def realPolynomialWeights {p m n : ℕ} [NeZero p]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (P : Polynomial ℝ)
    (_normalized : ∑ x : Fin n → ZMod p, (P.eval (linsatObjective B F x : ℝ))^2 = 1) :
    (Fin n → ZMod p) → ℝ :=
  fun x => (P.eval (linsatObjective B F x : ℝ))^2

example {p m n : ℕ} [NeZero p] (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (P : Polynomial ℝ)
    (h : ∑ x : Fin n → ZMod p, (P.eval (linsatObjective B F x : ℝ))^2 = 1) :
    ∑ x, realPolynomialWeights B F P h x = 1 := h

end QAlgorithms.PrimeFieldDQI

