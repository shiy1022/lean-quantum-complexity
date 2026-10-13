import QAlgorithms.Defs.TaylorSimulationData

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.TaylorSimulation

/-- QAlgorithms.TaylorSimulation.TaylorWord: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.3. Source domains are explicit below. -/
abbrev TaylorWord (L K : ℕ) := (k : Fin (K+1)) × (Fin k.val → Fin L)

/-- QAlgorithms.TaylorSimulation.wordCoefficient: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.3, arxiv-1412.4687v1 PDF p.4. Source domains are explicit below. -/
def wordCoefficient {I : Type*} [Fintype I] [DecidableEq I]
    (H : UnitaryDecomposition I) (dt : ℝ) {K : ℕ} (w : TaylorWord H.L K) : ℝ :=
  dt^w.1.val/(w.1.val.factorial : ℝ)*∏ i, H.alpha (w.2 i)

/-- QAlgorithms.TaylorSimulation.wordUnitary: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.3, arxiv-1412.4687v1 PDF p.4. Source domains are explicit below. -/
def wordUnitary {I : Type*} [Fintype I] [DecidableEq I]
    (H : UnitaryDecomposition I) {K : ℕ} (w : TaylorWord H.L K) : Matrix I I ℂ :=
  (-Complex.I)^w.1.val • (List.ofFn fun i => (H.terms (w.2 i) : Matrix I I ℂ)).prod

/-- QAlgorithms.TaylorSimulation.segmentSchedule: arxiv-1412.4687v1 PDF p.3. Source domains are explicit below. -/
def segmentSchedule {I : Type*} [Fintype I] [DecidableEq I]
    (H : UnitaryDecomposition I) (mass_pos : 0 < ∑ i, H.alpha i)
    (t : ℝ) (ht : 0 ≤ t) : List ℝ :=
  let mass := ∑ i, H.alpha i
  let r := ⌈mass*t/Real.log 2⌉₊
  if r = 0 then [] else List.replicate (r-1) (Real.log 2/mass) ++ [t-(r-1)*Real.log 2/mass]

/-- QAlgorithms.TaylorSimulation.normalizationRotation: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.3, arxiv-1412.4687v1 PDF p.4. Source domains are explicit below. -/
def normalizationRotation (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 2) : Matrix Bool Bool ℂ :=
  rotY (2*Real.arccos (s/2))

example {I : Type*} [Fintype I] [DecidableEq I] (H : UnitaryDecomposition I)
    (hp : 0 < ∑ i, H.alpha i) : segmentSchedule H hp 0 le_rfl = [] := by simp [segmentSchedule]

example {I : Type*} [Fintype I] [DecidableEq I] (H : UnitaryDecomposition I) (dt : ℝ) (K : ℕ) :
    wordCoefficient H dt (⟨⟨0,by omega⟩,Fin.elim0⟩ : TaylorWord H.L K) = 1 := by
  simp [wordCoefficient]



end QAlgorithms.TaylorSimulation
