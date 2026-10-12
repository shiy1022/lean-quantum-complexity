import QAlgorithms.Defs.GroverSampling

/-!
Theorem 6 of Rall and Fuller, *Amplitude Estimation from Quantum Signal Processing*,
arXiv:2207.08628v3, PDF p.14 (printed p.14), equation (39).

We use the completed two-dimensional Grover space of equations (3)--(6), including
amplitudes 0 and 1. The oracle-assisted basis measurement in the proof of Proposition 3
uses controlled rotations; these are counted in the instrument. Semi-Pellian sampling
uses the distinct opposite-angle oracle of equation (30). Ancillas alone are measured;
the signal is retained. Equality of branch density matrices ignores global phase.
-/

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.RoadmapA25

/-- The exact sampling and retained-state contract in Theorem 6, PDF p.14, equation (39).
The four labels are the known classical input/output labels. The branch trace is its
probability, and a zero-probability branch has the zero density matrix. -/
def SamplesWithRetainedSignal {n : ℕ} (I : GroverSamplingInstrument n)
    (value : ℝ → ℂ) : Prop :=
  ∀ (F : GroverFrame) (input : GroverLabel),
    (∑ label ∈ ({GroverLabel.psi, GroverLabel.psiPerp, GroverLabel.pi,
        GroverLabel.piPerp} : Finset GroverLabel),
      (groverInstrumentBranch I F input (pureDensity (F.state input)) true label).trace.re) =
        ‖value F.amplitude.val‖ ^ 2 ∧
    ∀ (b : Bool) (label : GroverLabel),
      groverInstrumentBranch I F input (pureDensity (F.state input)) b label =
        (((groverInstrumentBranch I F input (pureDensity (F.state input)) b label).trace.re :
          ℝ) : ℂ) • pureDensity (F.state label)

/-- Sampling from a polynomial: Theorem 6, arXiv:2207.08628v3, PDF p.14, equation (39).
For each polynomial, one instrument works for every completed Grover frame and each
known input label. It samples heads with probability |P(a)|² and retains one of the
four states on every branch. The two conjuncts have their respective oracle APIs.
The absolute constant precedes every polynomial, amplitude, basis and input label.
The bound C(deg(P)+1) includes the constant and zero-polynomial cases, and counts the
oracle calls used to implement the final basis measurement. Controlled ordinary
rotations are allowed as the operational convention used in Proposition 3's proof;
no uncontrolled-black-box implementation of controlled access is asserted. -/
theorem polynomialAmplitudeSampling :
    ∃ C : ℕ, 0 < C ∧
      (∀ P : Polynomial ℂ, IsPellian P →
        ∃ (n : ℕ) (I : GroverSamplingInstrument n),
          (∀ input, ∀ step ∈ I.steps input,
            match step with
            | .opposite _ _ _ => False
            | _ => True) ∧
          (∀ input,
            groverInstrumentQueryCount I input false false +
              groverInstrumentQueryCount I input true false +
              groverInstrumentQueryCount I input false true +
              groverInstrumentQueryCount I input true true ≤ C * (P.natDegree + 1)) ∧
          SamplesWithRetainedSignal I (fun a => P.eval (a : ℂ))) ∧
      (∀ P : Polynomial ℝ, IsSemiPellian P →
        ∃ (n : ℕ) (I : GroverSamplingInstrument n),
          (∀ input, ∀ step ∈ I.steps input,
            match step with
            | .rotation _ _ _ => False
            | _ => True) ∧
          (∀ input,
            groverInstrumentQueryCount I input false false +
              groverInstrumentQueryCount I input true false +
              groverInstrumentQueryCount I input false true +
              groverInstrumentQueryCount I input true true ≤ C * (P.natDegree + 1)) ∧
          SamplesWithRetainedSignal I (fun a => ((P.eval a : ℝ) : ℂ))) := by sorry

end QAlgorithms.Papers.RoadmapA25
