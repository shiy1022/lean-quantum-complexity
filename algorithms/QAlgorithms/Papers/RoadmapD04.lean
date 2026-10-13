import QAlgorithms.Defs.FoldedPrange

noncomputable section

open scoped Matrix ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapD04

open FoldedOPI FoldedDQI

/-- The whole folded symbol of Theorem 1, arXiv:2610.02145v2, pp.13–14. -/
abbrev Symbol (P : PublicDomain) := Fin (P.M + 2) → publicField P

/-- Exactly half-size acceptance sets, without restricting their joint conditions (p.14). -/
abbrev HalfAlphabet (P : PublicDomain) :=
  {A : Finset (Symbol P) // 2 * A.card = Fintype.card (Symbol P)}

/-- The instance determined by a tuple of independent half-size sets (pp.14–16). -/
def instanceOfSets (P : PublicDomain) (sets : Fin P.M → HalfAlphabet P) :
    BalancedInstance P.M (Symbol P) :=
  ⟨fun i => (sets i).val, fun i => (sets i).property⟩

/-- One fixed-block XOR oracle in the public binary encoding (eq.2.25, p.13).
The block index is an external parameter, not a coherent register. -/
def blockOracle (P : PublicDomain) (E : PublicFieldData P)
    (width : E.encoding.e * Nat.clog 2 E.encoding.p = 2 * P.u)
    (A : BalancedInstance P.M (Symbol P)) (i : Fin P.M) :
    Matrix (Qubits ((P.M + 2) * (2 * P.u) + 1))
      (Qubits ((P.M + 2) * (2 * P.u) + 1)) ℂ :=
  let h := congrArg (fun w : ℕ => (P.M + 2) * w + 1) width
  (extendEncodedUnitary (blockOracleEmbedding E.encoding (P.M + 2))
    (fixedBlockOracles A.sets i)).submatrix
      (fun z => z ∘ Fin.cast h) (fun z => z ∘ Fin.cast h)

/-- The same compiled circuit with its oracle arity expressed in encoding bits (p.40). -/
def encodedCircuit {R : ℚ} (F : UniformFixedBlockFamily R)
    (P : PublicDomain) (E : PublicFieldData P)
    (width : E.encoding.e * Nat.clog 2 E.encoding.p = 2 * P.u) :
    OracleCircuit htcxGateSet
      (fun _ : Fin P.M => (P.M + 2) * (E.encoding.e * Nat.clog 2 E.encoding.p) + 1)
      (F.qubits P) :=
  cast (congrArg (fun w : ℕ =>
    OracleCircuit htcxGateSet (fun _ : Fin P.M => (P.M + 2) * w + 1) (F.qubits P)) width).symm
    (F.circuit P)

/-- Expected score of the measured coefficient vector for a fixed oracle (eq.3.7, p.16). -/
def quantumScoreMean {R : ℚ} (F : UniformFixedBlockFamily R)
    (P : PublicDomain) (E : PublicFieldData P)
    (width : E.encoding.e * Nat.clog 2 E.encoding.p = 2 * P.u)
    (A : BalancedInstance P.M (Symbol P)) : ℝ :=
  ∑ z : Qubits (F.qubits P),
    prob (act ((F.circuit P).unitary (blockOracle P E width A)) (zeroKet (F.qubits P))) z *
      score P.M_pos E.gamma A (OPI.coefficientOutput E.encoding (publicParameters P 3)
        (List.ofFn fun i => z (F.output P i)))

/-- Joint probability for capped Prange: uniform balanced instance, then independent
algorithm randomness. The total cap is 4M, with zero fallback (pp.19–21). -/
def sampledPrangeProbability (P : PublicDomain) (E : PublicFieldData P)
    (distinct : Function.Injective (fun t : Fin (P.M * (P.M + 2)) => E.gamma ^ t.val))
    (dimensions : publicParameters P 3 ≤ P.M * (P.M + 2)) (event : ℝ → Prop) : ℝ :=
  (Fintype.card (Fin P.M → HalfAlphabet P) : ℝ)⁻¹ *
    ∑ sets : Fin P.M → HalfAlphabet P,
      ((publicPrangeLaw P E distinct dimensions (instanceOfSets P sets)).toOuterMeasure
        {x | event (score P.M_pos E.gamma (instanceOfSets P sets) x)}).toReal

/-- Joint probability for an oracle-independent randomized tree. Arbitrary computation
and finite advice are absorbed into its description (Theorem 1(iii), p.16). -/
def sampledClassicalProbability (P : PublicDomain) (E : PublicFieldData P)
    (A : RandDecisionTree (Fin P.M × Symbol P) Bool
      (Fin (publicParameters P 3) → publicField P)) (event : ℝ → Prop) : ℝ :=
  (Fintype.card (Fin P.M → HalfAlphabet P) : ℝ)⁻¹ *
    ∑ sets : Fin P.M → HalfAlphabet P,
      ((A.map fun tree => tree.eval (fun iz => decide (iz.2 ∈ (sets iz.1).val))).toOuterMeasure
        {x | event (score P.M_pos E.gamma (instanceOfSets P sets) x)}).toReal

/-- Pins DQI to the public GRS syndrome decoder, ell=floor((J-1)/2), top-window
weights, clean ideal workspace and M^(-2) synthesis accuracy (pp.32–40).
Output wires read the coefficient register of that same constructed state.
All properties here are conclusions of the headline, never hypotheses on its input. -/
def IsSourceDQI {R : ℚ} (F : UniformFixedBlockFamily R) (C : PrangeRealization R)
    (P : PublicDomain)
    (width : (C.fieldData P).encoding.e * Nat.clog 2 (C.fieldData P).encoding.p = 2 * P.u) :
    Prop :=
  let E := C.fieldData P
  let ell := publicParameters P 5
  2 * ((P.M + 2) * ell) < publicParameters P 3 + 1 ∧
    (∀ i : Fin P.M, (F.circuit P).queryCount i = 1) ∧
    (∑ i : Fin P.M, (F.circuit P).queryCount i) ≤ P.M ∧
    ∃ (charTwo : E.encoding.p = 2) (hell : ell ≤ P.M)
      (embedding : AlgorithmRegister (publicField P) P.M (P.M + 2)
        (publicParameters P 3) ↪ Qubits (F.qubits P))
      (fits : P.M + (P.M * (P.M + 2) + publicParameters P 3) *
        (E.encoding.e * Nat.clog 2 E.encoding.p) + 1 ≤ F.qubits P)
      (encoding : ∀ q, List.ofFn (embedding q) = algorithmBits E.encoding q ++
        List.replicate (F.qubits P - (P.M + (P.M * (P.M + 2) + publicParameters P 3) *
          (E.encoding.e * Nat.clog 2 E.encoding.p) + 1)) false),
      (∀ q, List.ofFn (fun i => embedding q (F.output P i)) =
        (List.ofFn fun j => OPI.fieldBits E.encoding (q.2.1 j)).flatten) ∧
      ConstructedCircuit P.M_pos ell hell E.gamma (C.distinct P) (C.dimensions P)
        embedding E.encoding charTwo fits encoding (encodedCircuit F P E width)

/-- Theorem 1 (all three clauses), arXiv:2610.02145v2, PDF/printed pp.15–16.
R is the fixed rational limiting rate. PublicDomain supplies every admissibility condition.
The existential families supply effective public representation, uniform polynomial runtime,
fixed-block XOR access, conventional unfolded GRS decoding and capped Prange.
The DQI expectation converges uniformly for each promised oracle. Classical probabilities
average independent uniform half-size sets and independent algorithm randomness.
Lower-bound constants precede sizes, budgets, algorithms and arbitrary finite advice. -/
theorem foldedOPI_oracle_separation (R : ℚ) (hR : 0 < R ∧ R < 1) :
    ∃ (C : PrangeRealization R) (F : UniformFixedBlockFamily R)
      (width : ∀ P, (C.fieldData P).encoding.e * Nat.clog 2 (C.fieldData P).encoding.p = 2 * P.u),
      (∀ P : PublicDomain, P.rate = R → IsSourceDQI F C P (width P)) ∧
      (∀ eps : ℝ, 0 < eps → ∃ M0 : ℕ, ∀ P : PublicDomain,
        P.rate = R → M0 ≤ P.M → ∀ A : BalancedInstance P.M (Symbol P),
          |quantumScoreMean F P (C.fieldData P) (width P) A -
            (1 + Real.sqrt ((R : ℝ) * (2 - (R : ℝ)))) / 2| ≤ eps) ∧
      (∀ eps delta : ℝ, 0 < eps → 0 < delta → ∃ M0 : ℕ, ∀ P : PublicDomain,
        P.rate = R → M0 ≤ P.M →
          sampledPrangeProbability P (C.fieldData P) (C.distinct P) (C.dimensions P)
            (fun s => eps < |s - (1 + (R : ℝ)) / 2|) ≤ delta) ∧
      (∀ eta : ℝ, 0 < eta → eta < 1 - (1 + (R : ℝ)) / 2 →
        ∃ theta c : ℝ, 0 < theta ∧ 0 < c ∧ ∃ M0 : ℕ, 2 ≤ M0 ∧
          ∀ P : PublicDomain, P.rate = R → M0 ≤ P.M →
          ∀ T : ℕ, (T : ℝ) ≤ Real.exp (theta * P.M / Real.log P.M) →
          ∀ A : RandDecisionTree (Fin P.M × Symbol P) Bool
            (Fin (publicParameters P 3) → publicField P),
          RandMakesAtMost A T →
            sampledClassicalProbability P (C.fieldData P) A
              (fun s => (1 + (R : ℝ)) / 2 + eta ≤ s) ≤ Real.exp (-c * P.M)) := by sorry

end QAlgorithms.Papers.RoadmapD04

