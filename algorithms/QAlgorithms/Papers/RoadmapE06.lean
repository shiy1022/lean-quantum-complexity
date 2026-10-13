import QAlgorithms.Defs.NoisyTannerDecoding

noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapE06

open QAlgorithms.NoisyTanner

/-- The actual CSS distance of the Tanner code, as defined on PDF p.5 of
arXiv:2306.12470v2. Here `qtCode0 = C_X` and `qtCode1 = C_Z`.
The infima are in `ℕ∞`: an empty logical-error set has distance infinity. -/
def tannerQuantumDistance {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (C : CodeData G) : ℕ∞ :=
  min (⨅ x ∈ qtCode1 C.CA C.CB, ⨅ (_ : x ∉ codeDual (qtCode0 C.CA C.CB)),
      (hammingNorm x : ℕ∞))
    (⨅ x ∈ qtCode0 C.CA C.CB, ⨅ (_ : x ∉ codeDual (qtCode1 C.CA C.CB)),
      (hammingNorm x : ℕ∞))

/-- Theorem 4.17 (Main Theorem for the Sequential Decoder), arXiv:2306.12470v2,
PDF pp.26–27; Algorithms 1–2 on p.13; standing construction assumptions on pp.4–7.
The inherited parameter domain is made explicit: `0 < delta`, `2 * delta < eps < 1`
(p.22). This clarifies the printed theorem's unspecified domains without changing
its bound or its non-strict threshold. The degree threshold depends only on the
fixed code/decoder parameters and precedes the group, code, check presentation,
selector and errors. `CodeData` carries the symmetric generating sets, exact
rates, four local-distance bounds, two product-expansion conditions and the
source's one-sided second-eigenvalue Ramanujan convention. The decoder is fixed
before the errors and receives only the noisy syndrome. A terminal execution
exists, and every lawful terminal execution satisfies the printed residual bound.
The frozen `sequentialDecoder` uses the source's `V_01`, `C_hat_1 + R_hat_0`
output, a consistent minimum-weight local selector with zero fallback, and
maximal termination. No decomposability or residual bound is assumed. -/
theorem singleShot_sequential
    (rate relativeDistance kappa delta eps : ℝ)
    (hrate : 0 < rate ∧ rate < 1)
    (hdistance : 0 < relativeDistance ∧ relativeDistance < 1)
    (hkappa : 0 < kappa ∧ kappa < 1)
    (hdelta : 0 < delta) (hseparation : 2 * delta < eps) (heps : eps < 1) :
    ∃ degreeThreshold : ℕ, 1 ≤ degreeThreshold ∧
      ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G],
      ∀ C : CodeData G, C.rate = rate → C.relativeDistance = relativeDistance →
        C.kappa = kappa → degreeThreshold ≤ C.degree →
      ∀ (H : CheckPresentation C) (selector : LocalCorrectionSelector H),
      let parameters : ConstantDomain :=
        { degree := C.degree
          degree_pos := C.degree_pos
          kappa := kappa
          relativeDistance := relativeDistance
          delta := delta
          eps := eps
          kappa_pos := hkappa.1
          relativeDistance_range := hdistance
          delta_pos := hdelta
          separation := hseparation
          eps_lt := heps }
      let constants := decoderConstants parameters
      let finiteThreshold := constants 2 * (Fintype.card G * C.degree ^ 2 : ℕ)
      let threshold := if tannerQuantumDistance C = ⊤ then finiteThreshold
        else min finiteThreshold (((tannerQuantumDistance C).toNat : ℝ) / (C.degree : ℝ))
      ∀ (e : G × C.A × C.B → ZMod 2)
        (D : {v : G × (Bool × Bool) // v.2.1 ≠ v.2.2} × Fin H.zCount → ZMod 2),
        constants 0 * (reducedWeight C e : ℝ) +
          constants 1 * (syndromeVertexWeight H D : ℝ) ≤ threshold →
        (∃ correction, sequentialDecoder selector eps (noisySyndrome H e D) correction) ∧
        ∀ correction, sequentialDecoder selector eps (noisySyndrome H e D) correction →
          (reducedWeight C (e + correction) : ℝ) ≤
            constants 5 * (syndromeVertexWeight H D : ℝ) := by sorry

end QAlgorithms.Papers.RoadmapE06

