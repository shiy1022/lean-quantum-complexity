import QAlgorithms.Defs.OnlineThresholdSearch

namespace QAlgorithms.Papers.RoadmapL23

/-- Badescu and O'Donnell, *Improved quantum data analysis*, arXiv:2011.10908v4,
Theorem 1.1 (PDF p.3; standing assumptions pp.2-3 and 8-10, reductions pp.19-21).
There is a dimension-independent copy count bounded by
`O(((log m)^2 + log(1/delta)) * log(1/delta) / eps^2)` and an online protocol
whose final claim is correct with probability at least `1 - delta`.
The protocol starts with a single batch of independent copies. Each stage sees only
the observable/threshold prefix, passes or selects that stage, and after all passes
claims every expectation is at most its threshold. Selection uses the strict
inequality `expectation > threshold - eps`; no existence promise is assumed. -/
theorem onlineThresholdSearch_sampleBound :
    ∃ C : ℝ, 0 < C ∧ ∃ nTS : ℕ → ℝ → ℝ → ℕ,
      ∀ m : ℕ, 1 ≤ m → ∀ eps delta : ℝ,
        0 < eps → eps < 1 / 2 → 0 < delta → delta < 1 / 2 →
        nTS m eps delta ≤
          ⌈C * ((Real.log (m : ℝ)) ^ 2 + Real.log (1 / delta)) *
            Real.log (1 / delta) / eps ^ 2⌉₊ ∧
        ∀ d : ℕ, 1 ≤ d →
          ∃ P : QAlgorithms.ThresholdSearch.OnlineProtocol d m (nTS m eps delta),
            QAlgorithms.ThresholdSearch.IsCorrect P eps delta := by sorry

end QAlgorithms.Papers.RoadmapL23
