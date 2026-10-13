import QAlgorithms.Defs.ClassicalDecoderMachines

/-!
# Quantum Expander Codes: adversarial decoding

Leverrier, Tillich and Zemor, arXiv:1504.00822v1, Theorem 2, PDF p.6
(printed p.5); standing graph conventions on PDF p.4 and the algorithm on pp.7-8.
The self hypergraph product and exact syndrome are computed from the frozen graph definitions.
The local contracts below certify source-valid execution; they add no progress assumptions.
-/

namespace QAlgorithms.Papers.RoadmapE07

open QAlgorithms.ExpanderCodes

attribute [local instance] Classical.propDecidable

/-- A finite execution certificate for Section 3, arXiv:1504.00822v1, PDF pp.7-8.
Each flip belongs to the frozen set of strictly improving opposite-generator subsets.
The ratio comparison is cross-multiplied over positive flip cardinalities; natural
subtraction is used only for strictly decreasing syndrome weights. The source allows
arbitrary ties. The certificate records the choices made by a concrete deterministic machine,
without requiring it to compute the noncomputable enumeration in frozen `chooseFlip`.
The terminal syndrome has no improving flip; zero means success and otherwise failure. -/
def IsMaxRatioTrace {R Q : Type*} [Fintype R] [Fintype Q]
    (H : Matrix R Q (ZMod 2)) (gens : Finset (Finset Q))
    (s : R → ZMod 2) (out : Option (Q → ZMod 2)) : Prop :=
  ∃ (k : ℕ) (flips : Fin k → Finset Q) (states : Fin (k + 1) → R → ZMod 2),
    states 0 = s ∧
    (∀ i : Fin k,
      flips i ∈ improvingFlips H gens (states i.castSucc) ∧
      states i.succ = states i.castSucc + H.mulVec (flipVector (flips i)) ∧
      ∀ F ∈ improvingFlips H gens (states i.castSucc),
        (hammingNorm (states i.castSucc) -
          hammingNorm (states i.castSucc + H.mulVec (flipVector F))) * (flips i).card ≤
        (hammingNorm (states i.castSucc) - hammingNorm (states i.succ)) * F.card) ∧
    improvingFlips H gens (states (Fin.last k)) = ∅ ∧
    out = if states (Fin.last k) = 0 then some (∑ i, flipVector (flips i)) else none

/-- Realization certificate for the two independent decoding procedures, Section 3,
arXiv:1504.00822v1, PDF pp.7-8. Partial successes are kept separately before combining
outputs: if either component fails, the pair decoder fails. Generator supports are matrix
rows, so Equation (6)'s mixed coordinate names are corrected by Equation (1) and PDF p.5's
incidence rules: the HX support is {alpha a : a adjacent beta} union
{b beta : alpha adjacent b}, not the printed {a beta} union {alpha b}. -/
def IsDecoderTrace {nA nB : ℕ} (G : BipartiteData nA nB)
    (s : ((Fin nA × Fin nB) → ZMod 2) × ((Fin nB × Fin nA) → ZMod 2))
    (out : Option (Error ((Fin nA × Fin nA) ⊕ (Fin nB × Fin nB)))) : Prop :=
  ∃ outX outZ,
    IsMaxRatioTrace (checks G).1 (generatorSupports (checks G).2) s.1 outX ∧
    IsMaxRatioTrace (checks G).2 (generatorSupports (checks G).1) s.2 outZ ∧
    out = outX.bind (fun x => outZ.map (fun z => (x, z)))

/- Definition sanity check: zero syndrome terminates with zero correction. -/
example {R Q : Type*} [Fintype R] [Fintype Q]
    (H : Matrix R Q (ZMod 2)) (gens : Finset (Finset Q)) :
    IsMaxRatioTrace H gens 0 (some 0) := by
  refine ⟨0, Fin.elim0, fun _ => 0, rfl, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · simp [improvingFlips]
  · simp

/-- Theorem 2 (arXiv:1504.00822v1, PDF p.6, printed p.5): for fixed positive degrees
and positive left/right expansion constants with deltaA, deltaB < 1/6, a classical machine
implements the maximum-ratio small-set-flip decoder in linear uniform-cost time and corrects
every error whose union-support weight is strictly below
`min (gammaA * nA) (gammaB * nB) / (3 * (1 + degreeB))`.

The machine and runtime constants precede all graph sizes, graphs, syndromes and errors.
Executed instructions count initialization, local searches, candidate maintenance and output;
input length additionally charges loading graph adjacency lists and syndrome. Termination
and realization hold on every syndrome; correctness holds at all admissible sizes.
The deterministic machine fixes its finite choices among maximal-ratio candidates.
No progress, robustness, critical-generator or distance guarantee is a hypothesis.

Source-domain clarification: positive degrees/nonempty parts make explicit the convention
used when Appendix A chooses an edge and Appendix B divides by degrees. Allowing zero
degrees makes the printed claim false. No strict degree inequality is assumed. Equation (6)'s
coordinate correction is recorded in `IsDecoderTrace`. Both clarifications require independent
moderation; the theorem's threshold is unchanged. -/
theorem quantumExpander_adversarial_decoding
    (degreeA degreeB : ℕ) (hdegreeA : 0 < degreeA) (hdegreeB : 0 < degreeB)
    (gammaA deltaA gammaB deltaB : ℝ)
    (hgammaA : 0 < gammaA) (hdeltaA : 0 < deltaA)
    (hgammaB : 0 < gammaB) (hdeltaB : 0 < deltaB)
    (hdeltaA_lt : deltaA < 1 / 6) (hdeltaB_lt : deltaB < 1 / 6) :
    ∃ (decoder : DecoderImplementation) (C : ℝ), 0 < C ∧ ∃ n0 : ℕ,
      ∀ (nA nB : ℕ) (G : BipartiteData nA nB),
        G.degreeA = degreeA → G.degreeB = degreeB →
        LeftRightExpanding G gammaA deltaA gammaB deltaB →
        ∀ s : ((Fin nA × Fin nB) → ZMod 2) × ((Fin nB × Fin nA) → ZMod 2),
          ∃ fuel : ℕ,
            let input := decoderInput G s
            let result := decoderExecution decoder input fuel
            result.halted.isSome ∧
              IsDecoderTrace G s (decoderOutput nA nB result) ∧
              (n0 ≤ nA ^ 2 + nB ^ 2 →
                ((input.length + result.steps : ℕ) : ℝ) ≤ C * ((nA ^ 2 + nB ^ 2 : ℕ) : ℝ)) ∧
              ∀ e : Error ((Fin nA × Fin nA) ⊕ (Fin nB × Fin nB)),
                syndrome G e = s →
                (errorWeight e : ℝ) <
                  min (gammaA * (nA : ℝ)) (gammaB * (nB : ℝ)) /
                    (3 * (1 + (degreeB : ℝ))) →
                DecodingSuccess G e (decoderOutput nA nB result) := by sorry

end QAlgorithms.Papers.RoadmapE07
