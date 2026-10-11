import QAlgorithms.Defs.SingleQubitCert

/-!
# M. Gupta, W. He, R. O'Donnell, *Few single-qubit measurements suffice to certify any quantum
state* (arXiv:2506.11355v2)

Cited "GHO p.N" (PDF pages). The algorithm is the frozen `SQCertAlg`: a finite adaptive tree whose
nodes are Definition-15 queries `Π₁ ⊗ ⋯ ⊗ Πₙ ↦ ⟨hyp|Π₁ ⊗ ⋯ ⊗ Πₙ|hyp⟩` (single-qubit projectors,
`Πₖ = Id` allowed), uniform coin flips, single-qubit projective measurements of the one copy of
`ρ_lab` in an adaptively chosen basis `{U|0⟩, U|1⟩}` (Remark 4), and Accept/Reject leaves. The
algorithm sees `|hyp⟩` only through the queries and is fixed before `|hyp⟩` and `ρ_lab` (trap Q2).
-/

namespace QAlgorithms.Papers.GuptaHeODonnell25

open QAlgorithms

/-- GHO Theorem 1 (p.2; proof §§2.2–2.4, pp.4–8). There exists an algorithm that given oracle
access to the classical description of a pure state `|hyp⟩` via the model in Definition 15 (p.8)
and one copy of a mixed state `ρ_lab`, makes only single-qubit measurements to `ρ_lab` and outputs
Accept with probability at least `Fid := ⟨hyp|ρ_lab|hyp⟩` and Reject with probability at least
`(1 − Fid)/n`. Moreover, the algorithm runs in time linear in the number of measurements.

Formalized: there is one family of algorithms `alg n` (`n` the number of qubits) and a constant
`C`, both chosen before `|hyp⟩` and `ρ_lab`, such that for every `n ≥ 1` every execution path of
`alg n` has at most `C · n` query, coin and measurement steps (the source's algorithm makes `n`
single-qubit measurements and runs in time `O(n)`, §2.4, p.8), and for every unit vector `|hyp⟩`
and every density matrix `ρ_lab` on `n` qubits, Accept has probability `≥ ⟨hyp|ρ_lab|hyp⟩` and
Reject has probability `≥ (1 − ⟨hyp|ρ_lab|hyp⟩)/n`. The fidelity is written
`Re Tr(|hyp⟩⟨hyp| ρ_lab) = ⟨hyp|ρ_lab|hyp⟩`. Classical post-processing between steps is not
charged (the continuations are arbitrary functions of the answers). -/
theorem certify_single_qubit_measurements :
    ∃ (alg : (n : ℕ) → SQCertAlg n) (C : ℕ),
      ∀ n : ℕ, 1 ≤ n →
        (alg n).StepsAtMost (C * n) ∧
        ∀ (hyp : EuclideanSpace ℂ (Qubits n)) (ρlab : Matrix (Qubits n) (Qubits n) ℂ),
          IsState hyp → IsDensityMatrix ρlab →
            (alg n).outProb hyp ρlab true ≥ effectProb (pureDensity hyp) ρlab ∧
            (alg n).outProb hyp ρlab false ≥ (1 - effectProb (pureDensity hyp) ρlab) / n := by
  sorry

end QAlgorithms.Papers.GuptaHeODonnell25
