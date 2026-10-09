import QAlgorithms.Defs.Information

/-!
# de Wolf, Chapter 18: the impossibility of perfect quantum bit commitment

R. de Wolf, *Quantum Computing: Lecture Notes*, §18.3–§18.4 (PDF pp. 170–172).

The source models a bit-commitment protocol by the two joint pure states `|ϕ_0⟩, |ϕ_1⟩` that
Alice and Bob hold after the commit phase when Alice honestly commits to `b = 0, 1` (purity is
without loss of generality, p.172 footnote 5). Alice's space is `ℂ^{d_A}` (index `Fin dA`), Bob's
is `ℂ^{d_B}` (index `Fin dB`); the joint space is indexed by `Fin dA × Fin dB`, Alice's register
first. The protocol is perfectly concealing when Bob's reduced density matrices agree,
`Tr_A |ϕ_0⟩⟨ϕ_0| = Tr_A |ϕ_1⟩⟨ϕ_1|` (`traceLeft`, `pureDensity`). It is "not binding at all" when
Alice, acting on her register alone, can turn `|ϕ_0⟩` into `|ϕ_1⟩` by a unitary `U ⊗ I`.
-/

namespace QAlgorithms.DeWolf

/-- de Wolf §18.4 (PDF pp. 171–172), unnumbered: a perfectly concealing quantum bit commitment
cannot be binding at all. For all dimensions `d_A, d_B` and all unit vectors
`|ϕ_0⟩, |ϕ_1⟩ ∈ ℂ^{d_A} ⊗ ℂ^{d_B}` (Alice's factor first) with equal reduced states on Bob's side,
`Tr_A(|ϕ_0⟩⟨ϕ_0|) = Tr_A(|ϕ_1⟩⟨ϕ_1|)`, there is a unitary `U` on Alice's space `ℂ^{d_A}` with
`(U ⊗ I)|ϕ_0⟩ = |ϕ_1⟩`. -/
theorem perfectBitCommitment_impossible (dA dB : ℕ)
    (phi0 phi1 : EuclideanSpace ℂ (Fin dA × Fin dB)) (h0 : IsState phi0) (h1 : IsState phi1)
    (hconceal : traceLeft (pureDensity phi0) = traceLeft (pureDensity phi1)) :
    ∃ U ∈ Matrix.unitaryGroup (Fin dA) ℂ,
      act (Matrix.kronecker U (1 : Matrix (Fin dB) (Fin dB) ℂ)) phi0 = phi1 := by
  sorry

end QAlgorithms.DeWolf
