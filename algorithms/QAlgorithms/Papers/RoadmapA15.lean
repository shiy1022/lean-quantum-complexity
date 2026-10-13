import QAlgorithms.Defs.TaylorSimulationPrograms

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.RoadmapA15

open QAlgorithms TaylorSimulation

/-- A gate implementation of every segment, returning the selector implementation's extra
workspace to zero. This is local bookkeeping for the paper's elementary gate accounting. -/
def CompilesSegments {n L K : ℕ} (P : SegmentedProgram n L K)
    (H : Fin L → Matrix.unitaryGroup (Qubits n) ℂ) (w : ℕ)
    (circuits : ℝ → Circuit oneTwoQubitGateSet (1 + (P.labelBits + n) + w)) : Prop :=
  ∀ dt ∈ P.durations, ImplementsWithCleanAncillas (circuits dt).unitary
    ((P.compilation dt).unitary (fun _ => signedOracle H))

/-- Berry, Childs, Cleve, Kothari and Somma, arXiv:1412.4687v1, unnumbered
time-independent simulation bound (PDF p.2), with construction and resource accounting
on pp.3–4, Eqs. (18)–(24). The simulator is chosen from public decomposition coefficients,
dimension, time and precision before the term oracle and the input state. Its output includes
all ancillary outcomes and is compared in trace norm, without a factor of one half.

Source corrections: Eq. (10)'s normalized failure coefficient must depend on the norm of the
nonunitary approximant; Eq. (11)'s exact block identity is used instead. Eq. (16)'s partial
trace of a ket is replaced by the unconditional reduced density operator. The order-register
preparation uses the segment coefficient mass, rather than the printed physical time t.
Trace norm is the interpretation of the unspecified reduced-state norm. The additive 1 in
the ancillary and Pauli gate bounds retains the unary register and scalar/one-term cases. -/
theorem truncatedTaylorHamiltonianSimulation :
    ∃ C c threshold : ℝ, 0 < C ∧ 1 ≤ c ∧ Real.exp (Real.exp 1) < threshold ∧
    ∀ (D L : ℕ), 0 < D → 0 < L →
    ∀ alpha : Fin L → ℝ, (∀ j, 0 < alpha j) →
    ∀ t eps : ℝ, 0 < t → 0 < eps → eps < 1 →
    let mass := ∑ j, alpha j
    let T := mass * t
    let r : ℕ := ⌈T / Real.log 2⌉₊
    ∃ positive : 0 < eps / (c * (r : ℝ)),
    let K := orderForPrecision (eps / (c * (r : ℝ))) positive
    ∃ P : SegmentedProgram (Nat.clog 2 D) L K,
      P.alpha = alpha ∧ P.time = t ∧ IsSourceCompilation P ∧
      0 < r ∧ P.durations.length = r ∧
      factorialTail K ≤ eps / (c * (r : ℝ)) ∧
      (1 + P.labelBits : ℝ) ≤ C * (1 + Nat.clog 2 L) * (K + 1) ∧
      (P.queryCount : ℝ) ≤ C * r * (K + 1) ∧
      (P.gateCount : ℝ) ≤ C * L * r * (K + 1) ∧
      ((1 ≤ T ∧ threshold ≤ T / eps) →
        (K : ℝ) ≤ C * Real.log (T / eps) / Real.log (Real.log (T / eps)) ∧
        (P.queryCount : ℝ) ≤
          C * T * Real.log (T / eps) / Real.log (Real.log (T / eps))) ∧
      ∀ H : Fin L → Matrix.unitaryGroup (Fin D) ℂ,
      (∑ j, (alpha j : ℂ) • (H j : Matrix (Fin D) (Fin D) ℂ)).IsHermitian →
      ∃ padded : Fin L → Matrix.unitaryGroup (Qubits (Nat.clog 2 D)) ℂ,
        (∀ j, (padded j : Matrix (Qubits (Nat.clog 2 D)) (Qubits (Nat.clog 2 D)) ℂ) =
          extendEncodedUnitary (finiteRegisterEmbedding D) (H j : Matrix (Fin D) (Fin D) ℂ)) ∧
        IsAccurate P padded eps ∧
        (∀ dt ∈ P.durations,
          specNorm (truncatedOperator
            (∑ j, (alpha j : ℂ) • (padded j : Matrix (Qubits (Nat.clog 2 D)) (Qubits (Nat.clog 2 D)) ℂ)) dt K -
            NormedSpace.exp (-(Complex.I * (dt : ℂ)) •
              ∑ j, (alpha j : ℂ) • (padded j : Matrix (Qubits (Nat.clog 2 D)) (Qubits (Nat.clog 2 D)) ℂ))) ≤
            eps / (c * (r : ℝ))) ∧
        (∀ psi : EuclideanSpace ℂ (Fin D), IsState psi →
          traceNorm (P.output padded
              (finiteRegisterEmbedding D * pureDensity psi * (finiteRegisterEmbedding D)ᴴ) -
            finiteRegisterEmbedding D *
              conjSuperop (NormedSpace.exp (-(Complex.I * (t : ℂ)) •
                ∑ j, (alpha j : ℂ) • (H j : Matrix (Fin D) (Fin D) ℂ))) (pureDensity psi) *
              (finiteRegisterEmbedding D)ᴴ) ≤ eps) ∧
        (∀ (w : ℕ)
            (selector : Circuit oneTwoQubitGateSet
              (1 + Nat.clog 2 L + Nat.clog 2 D + w)),
          ImplementsWithCleanAncillas selector.unitary (signedOracle padded) →
          ∃ circuits : ℝ → Circuit oneTwoQubitGateSet (1 + (P.labelBits + Nat.clog 2 D) + w),
            CompilesSegments P padded w circuits ∧
            ((P.durations.map fun dt => (circuits dt).size).sum : ℝ) ≤
              C * (L + selector.size) * r * (K + 1)) ∧
        ((∃ ops : Fin L → Fin (Nat.clog 2 D) → Stabilizer.Pauli,
            ∀ j, (padded j : Matrix (Qubits (Nat.clog 2 D)) (Qubits (Nat.clog 2 D)) ℂ) = pauliOps (ops j)) →
          ∃ w : ℕ,
          ∃ circuits : ℝ → Circuit oneTwoQubitGateSet (1 + (P.labelBits + Nat.clog 2 D) + w),
            CompilesSegments P padded w circuits ∧
            (1 + P.labelBits + w : ℝ) ≤ C * (1 + Nat.clog 2 L) * (K + 1) ∧
            ((P.durations.map fun dt => (circuits dt).size).sum : ℝ) ≤
              C * L * (Nat.clog 2 D + 1 + Nat.clog 2 L) * r * (K + 1)) := by sorry

end QAlgorithms.Papers.RoadmapA15
