import QAlgorithms.Defs.ZeroSumDynamics

noncomputable section

open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapO07

open QAlgorithms.ZeroSum

/-- Extract the setup, update body and finishing pass of the frozen dense implementation.
This syntax accessor is used only on `denseImplementation`, whose setup consists of
unconditional instructions before its single outer loop (arXiv:1904.03180v1, PDF p.6). -/
def denseLoopParts : ClassicalEntryProgram →
    ClassicalEntryProgram × (ClassicalEntryProgram × ClassicalEntryProgram)
  | .done => (.done, .done, .done)
  | .step op next =>
      let parts := denseLoopParts (next false)
      (.step op (fun _ => parts.1), parts.2)
  | .loop _ body rest => (.done, body, rest)

/-- Lemma 3 of van Apeldoorn and Gilyen, *Quantum algorithms for zero-sum games*,
arXiv:1904.03180v1, PDF p.6: the classical dense-entry implementation of Algorithm 1.
The fixed-accuracy branch uses the ceiling specified in Lemma 1 (PDF p.3) and counts
completed updates from the zero accumulators. Work is ideal numerical work, including
linear cumulative-distribution sampling, as in the proof on p.6; no bit-runtime claim
is made. The concrete program is fixed before the payoff matrix, and both optimality
conditions use the value of the game defined on PDF p.2. -/
theorem classical_dense_algorithm1 :
    ∃ C : ℝ, 0 < C ∧ ∃ size0 : ℕ, 1 ≤ size0 ∧
      ∀ (n m : ℕ) [NeZero n] [NeZero m] (A : Game n m)
        (eps delta : ℝ), 0 < eps → eps < 1 → 0 < delta → delta < 1 / 3 →
      let T : ℕ := ⌈16 * Real.log ((n : ℝ) * m / delta) / eps ^ 2⌉₊
      let initial : EntryState n m := ⟨0, [], 0, false⟩
      let program := denseImplementation n m eps T
      let law := entryProgramLaw A.payoff program initial
      let parts := denseLoopParts program
      let readout : EntryState n m → Option ((Fin n → ℝ) × (Fin m → ℝ)) :=
        fun s => if s.failed then none
          else some (fun i => s.memory i.val, fun j => s.memory (n + j.val))
      let prefixLaw := fun t : ℕ =>
        (entryProgramLaw A.payoff parts.1 initial).bind
          (entryProgramLaw A.payoff (.loop t parts.2.1 .done))
      law.map readout = fixedAccuracyRun A.payoff eps T ∧
      (∀ s ∈ (entryProgramLaw A.payoff parts.1 initial).support,
        s.failed = false ∧ s.trace = [] ∧
          (size0 ≤ n + m → (s.work : ℝ) ≤ C * (n + m))) ∧
      (∀ t < T, ∀ s ∈ (prefixLaw t).support,
        ∀ s' ∈ (entryProgramLaw A.payoff parts.2.1 s).support,
          s'.failed = false ∧ s'.trace.length = s.trace.length + (n + m) ∧
            (size0 ≤ n + m → (s'.work : ℝ) ≤ s.work + C * (n + m))) ∧
      (∀ s ∈ (prefixLaw T).support,
        ∀ s' ∈ (entryProgramLaw A.payoff parts.2.2 s).support,
          s'.failed = false ∧ s'.trace = s.trace ∧
            (size0 ≤ n + m → (s'.work : ℝ) ≤ s.work + C * (n + m))) ∧
      (∀ s ∈ law.support, s.failed = false ∧ s.trace.length = T * (n + m)) ∧
      (law.toOuterMeasure {s | ∃ x y, readout s = some (x, y) ∧
        IsEpsOptimalPair A eps x y}).toReal ≥ 1 - delta := by sorry

end QAlgorithms.Papers.RoadmapO07