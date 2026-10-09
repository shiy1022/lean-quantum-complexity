import QAlgorithms.Defs.Fourier

/-!
# de Wolf, Chapter 6: the Hidden Subgroup Problem

R. de Wolf, *Quantum Computing: Lecture Notes*, §6.1–§6.2 (PDF pp. 57–61).

The finite Abelian group is `G = ℤ_{N_1} × ⋯ × ℤ_{N_ℓ}` (the Basis Theorem form of p. 59),
modelled as `(i : Fin ℓ) → ZMod (N i)` with every `N i ≥ 1`. The finite set `S` of values of
`f` carries an (arbitrary) additive group structure so that "compute `f` in superposition",
`|g⟩|0⟩ ↦ |g⟩|f(g)⟩`, is the unitary `xorOracle f : |g, b⟩ ↦ |g, b + f(g)⟩` (any finite set
can be so equipped; only equality of `f`-values enters the HSP promise). The HSP promise
"`f(g) = f(g')` iff `g + H = g' + H`" is `AddHides f H`. Characters are
`χ_g(h) = ∏_i ω_{N_i}^{g_i h_i}` (`abelianChar`), `H^⊥` is identified with its set of labels
`annihilator H = {g | χ_g(h) = 1 ∀ h ∈ H}`, and the QFT of `G` is `qftAbelian N`,
`|k⟩ ↦ |χ_k⟩`. The standard algorithm's state before the final measurement, without the
step-4 measurement of the second register (which does not change the law of the first
register), is `hspStandardState N f`; the outcome law of step 6 is its first-register marginal.
-/

namespace QAlgorithms.DeWolf

/-- de Wolf §6.2.2 (PDF pp. 60–61), the standard algorithm for the Abelian hidden subgroup
problem. Let `G = ℤ_{N_1} × ⋯ × ℤ_{N_ℓ}`, let `S` be a finite set, `H ≤ G` a subgroup and
`f : G → S` constant on each coset of `H` and distinct on distinct cosets. Run the algorithm:
start in `|0⟩|0⟩`, create the uniform superposition over `G` in the first register, compute `f`
in superposition (one query), (measure the second register,) apply the QFT of `G` to the first
register and measure it. Then the output is `g` with probability `|H|/|G|` if `χ_g ∈ H^⊥`
(i.e. `χ_g(h) = 1` for all `h ∈ H`), and with probability `0` otherwise: the algorithm samples
uniformly from the labels of the elements of `H^⊥`. -/
theorem abelianHSP_standardAlgorithm_samples_annihilator {l : ℕ} (N : Fin l → ℕ)
    [∀ i, NeZero (N i)] {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]
    (H : AddSubgroup ((i : Fin l) → ZMod (N i))) (f : ((i : Fin l) → ZMod (N i)) → S)
    (hf : AddHides f H) (g : (i : Fin l) → ZMod (N i)) :
    (g ∈ annihilator H →
      marginalFst (hspStandardState N f) g =
        (Nat.card H : ℝ) / (Fintype.card ((i : Fin l) → ZMod (N i)) : ℝ)) ∧
    (g ∉ annihilator H → marginalFst (hspStandardState N f) g = 0) := by
  sorry

end QAlgorithms.DeWolf
