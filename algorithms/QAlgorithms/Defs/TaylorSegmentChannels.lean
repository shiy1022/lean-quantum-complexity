import QAlgorithms.Defs.PositiveLCU
import QAlgorithms.Defs.TaylorLCUWords
import QAlgorithms.Defs.Measurement

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.TaylorSimulation

/-- QAlgorithms.TaylorSimulation.amplifiedUnitary: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.3. Source domains are explicit below. -/
def amplifiedUnitary {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]
    (zero : J) (W : Matrix.unitaryGroup (J × I) ℂ) : Matrix (J × I) (J × I) ℂ :=
  let R := 1-(2 : ℂ) • Matrix.kronecker (pureDensity (ket zero)) (1 : Matrix I I ℂ)
  show Matrix (J × I) (J × I) ℂ from -((W : Matrix _ _ ℂ)*R*star (W : Matrix _ _ ℂ)*R*(W : Matrix _ _ ℂ))

/-- QAlgorithms.TaylorSimulation.segmentChannel: arxiv-1412.4687v1 PDF p.3. Source domains are explicit below. -/
def segmentChannel {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]
    (zero : J) (W : Matrix.unitaryGroup (J × I) ℂ) : Superop I I :=
  fun rho => traceLeft (conjSuperop (amplifiedUnitary zero W)
    (Matrix.kronecker (pureDensity (ket zero)) rho))

example {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]
    (zero : J) (W : Matrix.unitaryGroup (J × I) ℂ) : segmentChannel zero W 0 = 0 := by
  ext i j
  simp [segmentChannel, conjSuperop, traceLeft]

end QAlgorithms.TaylorSimulation
