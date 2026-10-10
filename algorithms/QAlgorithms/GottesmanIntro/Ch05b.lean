import QAlgorithms.Defs.FTCircuit

/-!
# Gottesman, *An introduction to quantum error correction*, §5.2: decoding with bad extended
rectangles, level reduction, the threshold theorem (Theorems 8, 9, 10)

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N" (PDF pages).

Standing assumptions of the section, carried by the frozen definition layer: one
`[[n, 1, 2t + 1]]` code (p.19) with fault-tolerant gadgets for preparation, measurement, `H`,
`R_{π/8}`, CNOT, wait and error correction (Defs. 2–5, `FTProtocol.IsFaultTolerant`), gadgets of
a common depth so that `C′` is again divided into time steps (Def. 6, `FTProtocol.HasUniformDepth`);
`C` is a Def. 6 circuit with no input, every qubit prepared first and measured last
(`LocCircuit.IsIdealCircuit`); the output of `C′` is its measurement record decoded classically
by the measurement gadgets' decoding (classical computation is perfect, p.17).
-/

namespace QAlgorithms.GottesmanIntro

/-- The number of locations of a full ExRec of type `κ` (Def. 7): the gadget for `κ` plus one
leading EC per input block (none for a preparation) and one trailing EC per output block (none
for a measurement). -/
def exRecSize (P : FTProtocol) (κ : LocKind) : ℕ :=
  (P.gadget κ).size + (κ.leadCount + κ.trailCount) * P.ec.size

/-- Gottesman intro p.41, the constant `A` of eq. (85): the maximum over the types of ExRecs of
the number of sets of exactly `t + 1` locations in the ExRec. -/
def exRecSubsetMax (P : FTProtocol) : ℕ :=
  [LocKind.prep, .had, .tgate, .cnot, .meas, .wait].foldr
    (fun κ acc => max ((exRecSize P κ).choose (P.t + 1)) acc) 0

/-- Gottesman intro p.40, eq. (84): the error bound `p′_i = Σ_R Π_{j∈R} p_j` for location `ℓ` of
`C`, the sum over the sets `R` of exactly `t + 1` locations of `C′` contained in the (full) ExRec
of `ℓ`. -/
noncomputable def levelReducedBound (P : FTProtocol) {N : ℕ} (C : LocCircuit N)
    (p : ℕ × ℕ → ℝ) (ℓ : ℕ × ℕ) : ℝ :=
  ∑ R ∈ (exRecLocs P C ℓ ∅).powersetCard (P.t + 1), ∏ j ∈ R, p j

/-- Gottesman intro p.39, Theorem 8: "Suppose we have a fault-tolerant circuit `C′` for `C`.
Assign good and bad extended rectangles to `C′`, and produce a circuit `C̃` as follows: If the
ExRec for `C_i` is good, include `C_i` unchanged in `C̃`. If the ExRec for `C_i` is bad, replace
`C_i` by the erroneous gate `U′` from eq. (82) … The circuit `C̃` uses ancilla registers to
control the types of `U′` errors. Then the output distribution of `C′` is the same as the output
distribution of `C̃`."

Let `P` be a fault-tolerant protocol, `C` a Def. 6 circuit, `fa` a Pauli fault arrangement on
`C′ = ftCircuit P C`, and `W` a *-decoder for the ideal decoder with syndrome register `Fin σ`.
Let `B` be the set of bad locations of `C` assigned by Def. 10 from the faulty locations of `C′`.
Then there are an initial state `σ0` of the syndrome registers (one per qubit of `C`) and errors
forming a circuit `C̃` (`IsTildeErrors`: at a good location, the ideal operation on the data
followed by some operation `V` on the syndrome registers of its qubits only; at a bad location,
the ideal operation followed by an arbitrary quantum operation `U′` on its qubits and their
syndrome registers) such that the decoded output distribution of the faulty `C′` equals the output
distribution of `C̃`. -/
theorem output_eq_tilde (P : FTProtocol) (hP : P.IsFaultTolerant) (hdepth : P.HasUniformDepth)
    {N : ℕ} (C : LocCircuit N) (hC : C.IsIdealCircuit) (fa : PauliArrangement) {σ : ℕ}
    (W : Matrix (Bool × Fin σ) (Qubits P.n) ℂ) (hW : IsStarDecoder P.dec W) :
    ∃ (σ0 : Matrix (Fin N → Fin σ) (Fin N → Fin σ) ℂ) (err : ErrAssign N (Fin N → Fin σ)),
      IsDensityMatrix σ0 ∧
      IsTildeErrors C (badAssignment P C (faultyLocs (ftCircuit P C) fa)) σ err ∧
      pushDist (ftDecode P C) ((ftCircuit P C).outDist (pauliErr (ftCircuit P C) fa) 1) =
        C.outDist err σ0 := by
  sorry

/-- Gottesman intro p.40, Theorem 9 (Level Reduction): "Suppose we have a fault-tolerant circuit
`C′` for `C`, and suppose `C′` experiences a local stochastic error model with error bounds `p_i`
and probability `p_S` of errors at precisely the set `S` of locations. Then for any particular set
`S` define `C̃_S` as in theorem 8, and define an error model on `C` by replacing `C` with `C̃_S`
with probability `p_S`. This is a local stochastic error model. The error bounds `p′_i` for `C`
are given by `p′_i ≤ Σ_R Π_{i∈R} p_i` (84) … In the special case where `p_i ≤ p` for all `i`, we
have `p′_i ≤ A p^{t+1}` (85)."

Let `P` be a fault-tolerant protocol, `C` a Def. 6 circuit, and `M` a local stochastic error
model (Def. 12: arbitrary chronological quantum errors, possibly entangled through an environment,
at a random set of faulty locations) on `C′ = ftCircuit P C` with bounds `p_i < 1`. Then there is
an error model `M′` on `C` such that
1. faults occur at precisely the set `S′` of locations of `C` with probability
   `Σ_{S : bad(S) = S′} p_S`, `bad(S)` the bad locations of Def. 10;
2. the decoded output distribution of `C′` under `M` equals the output distribution of `C` under
   `M′`;
3. `M′` is local stochastic with the bounds `p′_i` of eq. (84);
4. if `0 ≤ p` and `p_j ≤ p` for every location `j` of `C′`, then `p′_i ≤ A p^{t+1}` for every location `i`
   of `C`, with `A` as in eq. (85). -/
theorem level_reduction (P : FTProtocol) (hP : P.IsFaultTolerant) (hdepth : P.HasUniformDepth)
    {N : ℕ} (C : LocCircuit N) (hC : C.IsIdealCircuit)
    (M : LocalStochasticModel (N * (P.n + P.A))) (p : ℕ × ℕ → ℝ)
    (hp1 : ∀ j ∈ (ftCircuit P C).locs, p j < 1) (hM : IsLocalStochastic (ftCircuit P C) M p) :
    ∃ M' : LocalStochasticModel N,
      (∀ S' : Finset (ℕ × ℕ), M'.prob S' =
        ∑ S ∈ (ftCircuit P C).locs.powerset.filter (fun S => badAssignment P C S = S'),
          M.prob S) ∧
      pushDist (ftDecode P C) (noisyOutDist (ftCircuit P C) M) = noisyOutDist C M' ∧
      IsLocalStochastic C M' (levelReducedBound P C p) ∧
      ∀ p0 : ℝ, 0 ≤ p0 → (∀ j ∈ (ftCircuit P C).locs, p j ≤ p0) →
        ∀ i ∈ C.locs, levelReducedBound P C p i ≤ (exRecSubsetMax P : ℝ) * p0 ^ (P.t + 1) := by
  sorry

/-- Gottesman intro p.41, Theorem 10 (threshold theorem): "There is a threshold error rate `p_T`.
Suppose we have a local stochastic error model with `p_i ≤ p < p_T`. Then for any ideal circuit
`C`, and any `ε > 0`, there exists a fault-tolerant circuit `C′` which, when it undergoes the
error model, produces an output which has statistical distance at most `ε` from the output of
`C`. `C′` has a number of qubits and a number of timesteps which are at most `polylog(|C|/ε)`
times bigger than the number of qubits and timesteps in `C`, where `|C|` is the number of
locations in `C`."

There are a fault-tolerant protocol `P` (an `[[n, 1, 2t + 1]]` code with gadgets of a common
depth) and a threshold `p_T > 0` such that for every `0 ≤ p < p_T` there are constants `K > 0` and
`c` with: for every ideal circuit `C` and every `ε > 0` there is a concatenation level `L` such
that `C′ = C^{(L)}` (the `L`-fold fault-tolerant simulation, p.42) has at most
`K (log₂(2 + |C|/ε))^c` times as many qubits and time steps as `C`, and for every local
stochastic error model on `C′` with bounds `p_i ≤ p` (`p_i < 1`, Def. 12) the decoded output
distribution of `C′` is within total variation distance `ε` of the output distribution of `C`. -/
theorem threshold_theorem :
    ∃ P : FTProtocol, P.IsFaultTolerant ∧ P.HasUniformDepth ∧
      ∃ pT : ℝ, 0 < pT ∧ ∀ p : ℝ, 0 ≤ p → p < pT →
        ∃ (K : ℝ) (c : ℕ), 0 < K ∧
          ∀ (N : ℕ) (C : LocCircuit N), C.IsIdealCircuit → ∀ ε : ℝ, 0 < ε →
            ∃ L : ℕ,
              ((concatCircuit P L C).numQubits : ℝ) ≤
                K * Real.logb 2 (2 + (C.size : ℝ) / ε) ^ c * (C.numQubits : ℝ) ∧
              ((concatCircuit P L C).numSteps : ℝ) ≤
                K * Real.logb 2 (2 + (C.size : ℝ) / ε) ^ c * (C.numSteps : ℝ) ∧
              ∀ (M : LocalStochasticModel (N * (P.n + P.A) ^ L)) (b : ℕ × ℕ → ℝ),
                (∀ ℓ ∈ (concatCircuit P L C).locs, b ℓ < 1) →
                (∀ ℓ ∈ (concatCircuit P L C).locs, b ℓ ≤ p) →
                IsLocalStochastic (concatCircuit P L C) M b →
                tvDist (pushDist (concatDecode P L C) (noisyOutDist (concatCircuit P L C) M))
                  C.idealOutDist ≤ ε := by
  sorry

end QAlgorithms.GottesmanIntro
