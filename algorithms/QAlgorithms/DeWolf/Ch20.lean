import QAlgorithms.Defs.Stabilizer

/-!
# de Wolf, Chapter 20: stabilizer states, Clifford circuits (Gottesman–Knill)

R. de Wolf, *Quantum Computing: Lecture Notes*, §20.1–20.3, PDF pp.185–188.
-/

namespace QAlgorithms.DeWolf

open QAlgorithms.Stabilizer QAlgorithms.Complexity

/-- **Theorem 6 (Gottesman–Knill)**, de Wolf §20.3, PDF p.187 (proof pp.187–188).

"There exists a classical polynomial-time algorithm that, given an n-qubit
measurement-controlled Clifford circuit C and an n-qubit initial basis state |x⟩, samples from
the same final probability distribution over stabilizer states as C. The classical simulator
will output a stabilizer description of the sampled final state."

Following the source's own remark on p.187 ("strictly speaking we'd have to talk about families
of circuits {Cₙ}"), the circuit is a family `F` of measurement-controlled Clifford circuits
(Pauli, H, S, CNOT gates and Pauli measurements `M ∈ {I,X,Y,Z}^{⊗n}`, the next operation computed
from the random bits and the earlier outcomes by a polynomial-time classical controller, at most
polynomially many operations). For every such family there is one randomized classical
polynomial-time sampler `A` (fixed before `n` and `x`) such that, on input `(n, x)`:

1. every possible output is the encoding of a valid stabilizer tableau (`n` pairwise commuting,
   independent Pauli strings with phases `±1`, not generating `−I`);
2. the distribution of the state described by the output, `∏ⱼ (I + Pⱼ)/2`, equals the
   distribution of the circuit's final state `|ψ⟩⟨ψ|` on `|x⟩` (density matrices, so the
   global phase is ignored, de Wolf p.185 footnote 3). -/
theorem gottesmanKnill (F : MCCFamily) :
    ∃ A : RandPolyTimeSampler, ∀ (n : ℕ) (x : Qubits n),
      (∀ s ∈ (A.outDist (encInput n x)).support,
          ∃ T : Tableau n, IsValidTableau T ∧ s = encodeTableau T) ∧
        (A.outDist (encInput n x)).map (fun s => tableauProjector (decodeTableau n s)) =
          F.finalDist n x := by sorry

end QAlgorithms.DeWolf
