import QAlgorithms.Defs.Circuit

/-!
# Childs, Chapter 2: Efficient universality of quantum circuits

A. Childs, *Lecture Notes on Quantum Algorithms*, Chapter 2 (PDF pp. 15–17): the
Solovay–Kitaev theorem (Theorem 2.1), subadditivity of errors (Lemma 2.2), and the group
commutator net lemma (Lemma 2.3).

Conventions (§1.2–1.3, PDF pp. 9–10): gates act on one or two qubits; a circuit `U_t ⋯ U_1`
approximates `U` to precision `ϵ` when `‖U − U_t ⋯ U_1‖ ≤ ϵ` in the spectral norm; by §2.2
(PDF p. 16) a global phase is irrelevant, so approximation and universality are up to a global
phase (`ApproxUpToPhase`, `IsUniversal`).
-/

namespace QAlgorithms.Childs

open QAlgorithms

/-- Childs, Theorem 2.1 (Solovay–Kitaev), PDF p. 15. Fix two universal gate sets `A`, `B` of
unitary 1- and 2-qubit gates, both closed under inverses. Then there are constants `C > 0` and
`c` (depending only on `A` and `B`) such that every `t`-gate circuit over `A` on `n` qubits can be
implemented to precision `ϵ` (spectral norm, up to a global phase) by a circuit over `B` on the
same `n` qubits with at most `C · t · (log (2 + t/ϵ))^c` gates, i.e. `t · poly(log (t/ϵ))` gates.

The parenthetical clause of the source (a classical algorithm finds this circuit in time
`t · poly(log t/ϵ)`) is not formalized: the source fixes no classical machine model or encoding
for gates with real or complex entries, and leaves its proof as an exercise (PDF p. 17). -/
theorem solovayKitaev (A B : Set Gate)
    (hA_arity : ∀ g ∈ A, g.arity = 1 ∨ g.arity = 2) (hB_arity : ∀ g ∈ B, g.arity = 1 ∨ g.arity = 2)
    (hA_unit : ∀ g ∈ A, g.IsUnitary) (hB_unit : ∀ g ∈ B, g.IsUnitary)
    (hA_univ : IsUniversal A) (hB_univ : IsUniversal B)
    (hA_inv : ClosedUnderInverse A) (hB_inv : ClosedUnderInverse B) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (n : ℕ) (circ : Circuit A n) (ε : ℝ), 0 < ε →
      ∃ circ' : Circuit B n,
        (circ'.size : ℝ) ≤ C * circ.size * Real.log (2 + circ.size / ε) ^ c ∧
        ApproxUpToPhase circ.unitary circ'.unitary ε := by
  sorry

/-- Childs, Lemma 2.2 (subadditivity of errors), PDF p. 15. If `U_i`, `V_i` are unitary
matrices with `‖U_i − V_i‖ ≤ ϵ` (spectral norm) for all `i ∈ {1, …, t}`, then
`‖U_t ⋯ U_2 U_1 − V_t ⋯ V_2 V_1‖ ≤ t ϵ`. Here the source's `U_i` is `U (i − 1)` and
`orderedProd U = U (t − 1) * ⋯ * U 0`. -/
theorem subadditivity_of_errors {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℕ)
    (U V : Fin t → Matrix.unitaryGroup ι ℂ) (ε : ℝ)
    (h : ∀ i, specNorm ((U i : Matrix ι ι ℂ) - (V i : Matrix ι ι ℂ)) ≤ ε) :
    specNorm (orderedProd (fun i => (U i : Matrix ι ι ℂ)) -
      orderedProd (fun i => (V i : Matrix ι ι ℂ))) ≤ t * ε := by
  sorry

/-- Childs, Lemma 2.3, PDF p. 16. If `Γ ⊆ SU(2)` is an `ϵ²`-net for `S_ϵ = {U ∈ SU(2) :
‖I − U‖ ≤ ϵ}`, then `⟦Γ, Γ⟧ = {U V U⁻¹ V⁻¹ : U, V ∈ Γ}` is an `O(ϵ³)`-net for `S_{ϵ²}`.
The `O(ϵ³)` is with respect to `ϵ → 0` (PDF p. 17), with a constant independent of `Γ` (the
recursion on p. 16 uses one constant `k` at every level): there are `C > 0` and `ϵ₀ > 0` such
that for every `0 < ϵ ≤ ϵ₀` and every such `Γ`, `⟦Γ, Γ⟧` is a `C ϵ³`-net for `S_{ϵ²}`. -/
theorem commutator_net :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ Γ : Set (Matrix.specialUnitaryGroup (Fin 2) ℂ),
        IsNet Γ (su2Ball ε) (ε ^ 2) → IsNet (commutatorSet Γ) (su2Ball (ε ^ 2)) (C * ε ^ 3) := by
  sorry

end QAlgorithms.Childs
