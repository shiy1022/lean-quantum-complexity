import QAlgorithms.Defs.Qubitization
import QAlgorithms.Defs.CircuitResources

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.RoadmapA01

/-- Low and Chuang, *Hamiltonian Simulation by Qubitization*, arXiv:1610.06546v3,
PDF p.3, Theorem 1 and Eq. (1); standard-form access and gates: pp.4–5;
successful operator block: pp.14–16, Eqs. (29)–(31).

The circuit is chosen before the black-box unitaries. Its total query count is
Theta of the minimal positive factorial-tail scale, and its additional two-qubit
gate count is O(Q log d). All calls are controlled, with adjoints counted once.
Finite-register embeddings extend the oracles by the identity on the complement.
The first ceil(log2 d)+2 wires are postselected to zero; the other wires hold the
encoded system. Error is spectral norm of this successful block, including any
leakage into unused system basis states. Failure is bounded for every unit input.

The printed tau in Eq. (1) is undefined here; its exact factorial expression uses
|t|. The secondary O(|t|+log(1/eps)) estimate is restricted to small error.
The proof's internal tail accuracy must be rescaled to order eps squared to obtain
the stated final error eps. The +i odd part in Eqs. (32),(34) has the wrong sign
for the headline's -i evolution; the target below retains the headline's sign.
The lower query inequality concerns this procedure, not every simulator of each H.
-/
theorem optimalHamiltonianSimulation :
    ∃ CqueryLower CqueryUpper Cgates Cfailure Cscale eps0 : ℝ,
      0 < CqueryLower ∧ 0 < CqueryUpper ∧ 0 < Cgates ∧ 0 < Cfailure ∧
      0 < Cscale ∧ 0 < eps0 ∧ eps0 < 1 ∧
      ∀ (N d : ℕ) [NeZero N] [NeZero d] (t eps : ℝ)
        (heps : 0 < eps), eps < 1 →
        let Q := factorialQueryScale t eps heps
        (eps ≤ eps0 → (Q : ℝ) ≤ Cscale * (|t| + Real.log (1 / eps))) ∧
        ∃ c : OracleCircuit oneTwoQubitGateSet
            (fun k : Fin 2 => if k = 0 then Nat.clog 2 d + Nat.clog 2 N
              else Nat.clog 2 d)
            ((Nat.clog 2 d + 2) + (Nat.clog 2 N + 0)),
          (∀ k : Fin 2, c.plainQueryCount k = 0) ∧
          CqueryLower * (Q : ℝ) ≤ (c.queryCount 0 + c.queryCount 1 : ℕ) ∧
          (c.queryCount 0 + c.queryCount 1 : ℕ) ≤ CqueryUpper * (Q : ℝ) ∧
          (c.gateCountWhere (fun g => g.arity = 2) : ℝ) ≤
            Cgates * (Q : ℝ) * Real.log d ∧
          ∀ (U : Matrix.unitaryGroup (Fin d × Fin N) ℂ)
            (G : Matrix.unitaryGroup (Fin d) ℂ),
            (standardFormSignal (N := N) (d := d) (U : Matrix (Fin d × Fin N) (Fin d × Fin N) ℂ) (G : Matrix (Fin d) (Fin d) ℂ)).IsHermitian →
            let J := (Matrix.kronecker (finiteRegisterEmbedding d)
              (finiteRegisterEmbedding N)).submatrix
                (qubitsAppendEquiv (Nat.clog 2 d) (Nat.clog 2 N)) id
            let O : (k : Fin 2) →
                Matrix (Qubits (if k = 0 then Nat.clog 2 d + Nat.clog 2 N
                    else Nat.clog 2 d))
                  (Qubits (if k = 0 then Nat.clog 2 d + Nat.clog 2 N
                    else Nat.clog 2 d)) ℂ :=
              fun k => if h : k = 0 then
                by subst k; exact extendEncodedUnitary J (U : Matrix (Fin d × Fin N) (Fin d × Fin N) ℂ)
              else by
                simpa only [if_neg h] using
                  extendEncodedUnitary (finiteRegisterEmbedding d) (G : Matrix (Fin d) (Fin d) ℂ)
            let V := (c.unitary O).submatrix
              (fun p : Qubits (Nat.clog 2 d + 2) × (Qubits (Nat.clog 2 N) × Qubits 0) =>
                Fin.append p.1 (Fin.append p.2.1 p.2.2))
              (fun p : Qubits (Nat.clog 2 d + 2) × (Qubits (Nat.clog 2 N) × Qubits 0) =>
                Fin.append p.1 (Fin.append p.2.1 p.2.2))
            let K := simulationSuccessOperator (Nat.clog 2 d + 2) 0 V
            specNorm (K - finiteRegisterEmbedding N *
              NormedSpace.exp (-(Complex.I * (t : ℂ)) •
                standardFormSignal (N := N) (d := d) (U : Matrix (Fin d × Fin N) (Fin d × Fin N) ℂ) (G : Matrix (Fin d) (Fin d) ℂ))) ≤ eps ∧
            ∀ psi : EuclideanSpace ℂ (Fin N), IsState psi →
              1 - ‖Matrix.toEuclideanLin K psi‖ ^ 2 ≤ Cfailure * eps := by sorry

end QAlgorithms.Papers.RoadmapA01
