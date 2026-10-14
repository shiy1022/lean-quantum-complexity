import QAlgorithms.Defs.IntrinsicWorldLearning

namespace QAlgorithms.Papers.RoadmapL11

open QAlgorithms.IntrinsicLearning

/-- Huang, Flammia, and Preskill, *Foundations for learning from noisy quantum experiments*,
arXiv:2204.13691v1, Theorem 2 (PDF p.4), formally restated as Theorem D.1 (PDF p.21).
For fixed finite action and outcome spaces and positive finite dimension, every model class
whose members are universal is intrinsically learnable in the sense of Definition C.5 (p.20).
The unknown universality witnesses remain inside each world. A single family of finite adaptive
experimental programs is chosen before the true world; its eventual per-world guarantees use
one common unitary or anti-unitary gauge outside the individual probability clauses, unhalved
trace norm for states and effects, and diamond norm for channels. The staged interpretation is
the precision-halving procedure of D.2 (p.23) and D.7, Eqs. (D109)--(D111) (p.33).
The finite-action scope follows D.1; the main-text statement does not explicitly impose it.
-/
theorem universalModels_intrinsicallyLearnable
    {d : ℕ} (hd : 0 < d) {X Y Z B : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype B]
    (Q : Set (WorldModel d X Y Z B))
    (hQ : ∀ W ∈ Q, IsUniversalWorld W) :
    IsIntrinsicallyLearnable Q := by sorry

end QAlgorithms.Papers.RoadmapL11
