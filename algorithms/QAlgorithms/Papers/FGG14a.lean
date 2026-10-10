import QAlgorithms.Defs.QAOA

/-!
# Farhi, Goldstone, Gutmann: A quantum approximate optimization algorithm

E. Farhi, J. Goldstone, S. Gutmann, *A quantum approximate optimization algorithm*
(arXiv:1411.4028v1), cited "FGG p.N" (PDF pages).

The QAOA state `|γ, β⟩ = U(B, β_p) U(C, γ_p) ⋯ U(B, β_1) U(C, γ_1) |s⟩` of eq. (6) (p.3), with
`U(C, γ) = e^{−iγC}` (2), `U(B, β) = e^{−iβB}`, `B = Σ_j σ^x_j` (3)–(4) and
`|s⟩ = 2^{−n/2} Σ_z |z⟩` (5), is the frozen `qaoaUnitary f p β θ` applied to
`act (hadamardN n) (zeroKet n)` (round `k` has `θ k = γ_{k+1}` and `β k = β_{k+1}`, the
`C`-phase applied first). The MaxCut objective `C = Σ_⟨jk⟩ ½(1 − σ^z_j σ^z_k)` (11)–(12) is
diagonal with `C(z)` the number of edges whose endpoints get different bits, the frozen
`cutValue G z`; `F_p(γ, β) = ⟨γ, β| C |γ, β⟩` (7) is the frozen `qaoaExpectation`.
-/

namespace QAlgorithms.Papers.FGG14a

/-- FGG p.1 (Abstract) and §V, pp.8–10, eqs. (32)–(35): for `p = 1`, on every connected
3-regular graph `G` on `n` vertices, the best `p = 1` QAOA angles give an expected cut value
`M_1 = max_{γ, β} F_1(γ, β)` that is at least `0.6924` times the maximum cut `max_z C(z)`.
The angles range over the source's intervals `γ ∈ [0, 2π]` (p.2) and `β ∈ [0, π]` (p.2).
The source's value `0.6924` is the (rounded-down) numerical minimum of (35). -/
theorem maxcut_threeRegular_p1 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hconn : G.Connected) (hreg : G.IsRegularOfDegree 3) :
    ∃ γ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ∃ β ∈ Set.Icc (0 : ℝ) Real.pi,
      qaoaExpectation (fun z => (cutValue G z : ℝ)) 1 ![β] ![γ] ≥
        0.6924 * ((Finset.univ.sup fun z : Qubits n => cutValue G z : ℕ) : ℝ) := by
  sorry

end QAlgorithms.Papers.FGG14a
