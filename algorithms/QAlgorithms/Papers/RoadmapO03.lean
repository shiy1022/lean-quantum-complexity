import QAlgorithms.Defs.JointLowRankGibbsContracts

noncomputable section

open scoped Matrix ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapO03

open QAlgorithms.LowRankGibbs

/-- Source D.1 register encoding: index j, then the two binary trace answers.
Each factor uses the frozen most-significant-bit convention (PDF p.21, Eq. (D.1)). -/
def traceInputEmbedding (m : ℕ) (F : TraceBinaryFormat) :
    Matrix (Qubits (Nat.clog 2 m + F.width + F.width))
      (Fin m × (Qubits F.width × Qubits F.width)) ℂ :=
  Matrix.of fun z p =>
    if z = Fin.append (Fin.append (natToBits (Nat.clog 2 m) p.1) p.2.1) p.2.2 then 1 else 0

/-- Source D.2 register encoding: j and the four n-valued purification registers.
Each finite label is encoded separately, preserving the tensor factors (PDF p.21, Eq. (D.2)). -/
def prepInputEmbedding (n m : ℕ) :
    Matrix (Qubits (Nat.clog 2 m + Nat.clog 2 n + Nat.clog 2 n + Nat.clog 2 n + Nat.clog 2 n))
      (Fin m × ((Fin n × Fin n) × (Fin n × Fin n))) ℂ :=
  Matrix.of fun z p =>
    if z = Fin.append
        (Fin.append (Fin.append (Fin.append (natToBits (Nat.clog 2 m) p.1)
          (natToBits (Nat.clog 2 n) p.2.1.1)) (natToBits (Nat.clog 2 n) p.2.1.2))
          (natToBits (Nat.clog 2 n) p.2.2.1)) (natToBits (Nat.clog 2 n) p.2.2.2)
    then 1 else 0

/-- A supplied qubit unitary represents the source oracle on its encoded register.
Its action outside the embedding is unrestricted; no known identity sector is supplied. -/
def IsEncodedInput {I : Type} [Fintype I] {a : ℕ}
    (J : Matrix (Qubits a) I ℂ) (O : Matrix I I ℂ)
    (U : Matrix (Qubits a) (Qubits a) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup _ ℂ ∧ U * J = J * O

/-- Qubit widths of D.1 and D.2, encoding each source tensor factor separately.
Source: arXiv:1710.02581v3, PDF p.21, Eqs. (D.1) and (D.2). -/
def inputArities (n m : ℕ) (F : TraceBinaryFormat) : Fin 2 → ℕ :=
  Fin.cases (Nat.clog 2 m + F.width + F.width)
    (fun _ => Nat.clog 2 m + Nat.clog 2 n + Nat.clog 2 n + Nat.clog 2 n + Nat.clog 2 n)

/-- The supplied qubit oracles restrict to D.1 and D.2, respectively.
Finite-register completions and unused-qubit-label completions remain arbitrary.
Source: arXiv:1710.02581v3, PDF p.21, Eqs. (D.1) and (D.2). -/
def IsInputOracles {n m : ℕ} {F : TraceBinaryFormat}
    (Otr : Matrix (Fin m × (Qubits F.width × Qubits F.width))
      (Fin m × (Qubits F.width × Qubits F.width)) ℂ)
    (Oprep : Matrix (Fin m × ((Fin n × Fin n) × (Fin n × Fin n)))
      (Fin m × ((Fin n × Fin n) × (Fin n × Fin n))) ℂ)
    (O : (k : Fin 2) → Matrix (Qubits (inputArities n m F k))
      (Qubits (inputArities n m F k)) ℂ) : Prop :=
  IsEncodedInput (traceInputEmbedding m F) Otr (O 0) ∧
    IsEncodedInput (prepInputEmbedding n m) Oprep (O 1)

/-- Low-rank Gibbs sampling from indexed quantum inputs: arXiv:1710.02581v3,
Appendix D.5, Lemma 12, PDF p.26, using Lemma 11 and Appendix G.3, Theorem 4,
PDF pp.38–40 (also Appendix F.2, p.32). Zero PSD components have arbitrary
normalized purification outputs, ignored at zero sampling weight (p.29 and Lemma 11).
Printed / changed / why: the printed |S| * poly(log n, rK, BK, eps inverse) gate
bound omits address preparation. We include a factor 1 + log m to charge elementary
gates for the index register, and require nonempty S to avoid the printed zero-cost
bound for preparing I/n at empty support. All other conclusions are retained.
Unused qubit labels have arbitrary unitary completions, rather than a known identity.
The output is unconditional, with almost-sure termination and expected charged cost
(PDF p.33). Precision is the unhalved trace norm of Eqs. (F.15)–(F.17), p.34.
The last clause records the corrected corollary for every support bound Phi. -/
theorem lowRankGibbs_sampling :
    ∃ C : ℝ, 0 < C ∧ ∃ q : ℕ,
    ∀ (n m : ℕ), 0 < n → 0 < m →
    ∀ (S : Finset (Fin m)), S.Nonempty →
    ∀ (c : Fin m → ℝ), (∀ j ∈ S, 0 < c j) →
    ∀ (rK : ℕ) (BK eps : ℝ), 0 ≤ BK → 0 < eps →
    ∀ F : TraceBinaryFormat,
    ∃ (N w : ℕ) (P : SamplingProgram (inputArities n m F) N n w),
    ∀ A : PSDInputFamily n m,
      (weightedPlus A S c).rank ≤ rK →
      (weightedMinus A S c).rank ≤ rK →
      (weightedPlus A S c).trace.re + (weightedMinus A S c).trace.re ≤ BK →
    ∀ (Otr : Matrix (Fin m × (Qubits F.width × Qubits F.width))
        (Fin m × (Qubits F.width × Qubits F.width)) ℂ)
      (Oprep : Matrix (Fin m × ((Fin n × Fin n) × (Fin n × Fin n)))
        (Fin m × ((Fin n × Fin n) × (Fin n × Fin n))) ℂ),
      IsTraceInputOracle A F Otr → IsJointPurificationInputOracle A Oprep →
    ∀ O : (k : Fin 2) → Matrix (Qubits (inputArities n m F k))
      (Qubits (inputArities n m F k)) ℂ,
      IsInputOracles Otr Oprep O →
      GibbsSamplingContract P O (weightedHamiltonian A S c) eps ∧
      (∑ j : Fin 3, expectedResources P O j) ≤
        ENNReal.ofReal (C * S.card * (1 + Real.log m) *
          (1 + Real.log n + rK + BK + eps⁻¹) ^ q) ∧
      ∀ Phi : ℕ, S.card ≤ Phi →
        (∑ j : Fin 3, expectedResources P O j) ≤
          ENNReal.ofReal (C * Phi * (1 + Real.log m) *
            (1 + Real.log n + rK + BK + eps⁻¹) ^ q) := by sorry

end QAlgorithms.Papers.RoadmapO03

