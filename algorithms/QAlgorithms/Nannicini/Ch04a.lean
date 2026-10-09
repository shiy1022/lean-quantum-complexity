import QAlgorithms.Defs.AmplitudeEstimation

/-!
# Nannicini, Chapter 4 (part a): amplitude amplification

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages): Theorem 4.6 (p.78–79), Corollary 4.9 (p.79), Corollary 4.10 (p.80), Lemma 4.11
(p.81), Theorem 4.12 (p.82).

Conventions. An `n`-qubit register is indexed by `Qubits n`; the source's `|0⟩` is `zeroKet n`.
The Grover iteration of §4.1.4 (p.77) is `G = S F S† R` with `F = 2|0⟩⟨0| − I = reflAt 0`, the
frozen `ampAmpIterate S R 0`. The marking oracle is `U_f : |j⟩|y⟩ ↦ |j⟩|y ⊕ f(j)⟩` (p.69), the
frozen `xorOracle f`. In §4.2.2 the flag qubit is the first qubit (p.80): an `(n + 1)`-qubit
register is indexed by `Bool × Qubits n`, flag first.
-/

namespace QAlgorithms.Nannicini

/-- Nannicini p.78–79, Theorem 4.6 (Amplitude amplification; Brassard et al. 2002). Let `S` be an
`n`-qubit unitary with `S|0⟩ = √p |ψ_G⟩ + √(1 − p) |ψ_B⟩`, where for a set `M ⊆ {0,1}^n`,
`|ψ_G⟩ = (1/√p) ∑_{j ∈ M} α_j |j⟩`, `|ψ_B⟩ = (1/√(1−p)) ∑_{j ∉ M} α_j |j⟩` and
`p = ∑_{j ∈ M} |α_j|²` (here `α = S|0⟩`), with `0 < p < 1` (§4.1.4, p.77: `θ ∈ (0, π/2)`). Let `R`
be a unitary with `R|ψ_G⟩ = −|ψ_G⟩` and `R|ψ_B⟩ = |ψ_B⟩`. Then the amplitude amplification
algorithm, i.e. `k` Grover iterations `G = S F S† R` applied to `S|0⟩` (p.77), produces a state
whose overlap `|⟨ψ_G|G^k S|0⟩|` with `|ψ_G⟩` is at least `2/3`, using `O(1/√p)` applications of
`S` and `R`: the `2k + 1` applications of `S` or `S†` are at most `C/√p` for a constant `C`
chosen before `n, S, M, R, p`. -/
theorem amplitudeAmplification_overlap :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (S R : Matrix (Qubits n) (Qubits n) ℂ) (M : Finset (Qubits n)),
      S ∈ Matrix.unitaryGroup (Qubits n) ℂ → R ∈ Matrix.unitaryGroup (Qubits n) ℂ →
      0 < probEvent (act S (zeroKet n)) (fun j => j ∈ M) →
      probEvent (act S (zeroKet n)) (fun j => j ∈ M) < 1 →
      act R (ampGoodState (act S (zeroKet n)) M) = -ampGoodState (act S (zeroKet n)) M →
      act R (ampBadState (act S (zeroKet n)) M) = ampBadState (act S (zeroKet n)) M →
      ∃ k : ℕ,
        (2 * (k : ℝ) + 1) ≤ C / Real.sqrt (probEvent (act S (zeroKet n)) (fun j => j ∈ M)) ∧
        2 / 3 ≤ ‖inner ℂ (ampGoodState (act S (zeroKet n)) M)
          (act (ampAmpIterate S R 0 ^ k) (act S (zeroKet n)))‖ := by
  sorry

/-- Nannicini p.79, Corollary 4.9: let `U_f : |j⟩|y⟩ ↦ |j⟩|y ⊕ f(j)⟩` implement a Boolean
function `f : {0,1}^n → {0,1}` and let `M = {j : f(j) = 1}`. If `|M|` is known, an element of `M`
can be determined with `O(√(2^n/|M|))` applications of `U_f`. Formally: there is a constant `C > 0`
such that for all `n` and every known count `1 ≤ t ≤ 2^n` there is a `T`-query algorithm (fixed
input-independent unitaries on the query register and a workspace with basis `Fin w`,
interleaved with `T` applications of `U_f`) and an output map, with `T ≤ C √(2^n/t)`,
which for every `f` with exactly `t` marked elements outputs a marked element with probability at
least `2/3` (the bounded-error convention, Rem. 4.7). -/
theorem search_knownCount :
    ∃ C : ℝ, 0 < C ∧ ∀ n t : ℕ, 1 ≤ t → t ≤ 2 ^ n →
      ∃ (w T : ℕ) (A : QueryAlg (Qubits n) Bool (Fin w) T)
        (out : (Qubits n × Bool) × Fin w → Qubits n),
        (T : ℝ) ≤ C * Real.sqrt ((2 : ℝ) ^ n / (t : ℝ)) ∧
        ∀ f : Qubits n → Bool, (Finset.univ.filter fun j => f j = true).card = t →
          2 / 3 ≤ probEvent (A.finalState (xorOracle f)) fun z => f (out z) = true := by
  sorry

/-- Nannicini p.80, Corollary 4.10: let `M = {j ∈ {0,1}^n : f(j) = 1}` be the set of marked
elements, with `|M|` known. Then all elements of `M` can be determined using `O(√(|M| 2^n))`
applications of `f` (through `U_f : |j⟩|y⟩ ↦ |j⟩|y ⊕ f(j)⟩`). Formally: there is a constant `C > 0`
such that for all `n` and every known count `t` there is a `T`-query algorithm with an output map
to subsets of `{0,1}^n`, with `T ≤ C √(t 2^n)`, which for every `f` with exactly `t` marked
elements outputs the set `M` with probability at least `2/3` (bounded-error convention). -/
theorem findAllMarked_knownCount :
    ∃ C : ℝ, 0 < C ∧ ∀ n t : ℕ,
      ∃ (w T : ℕ) (A : QueryAlg (Qubits n) Bool (Fin w) T)
        (out : (Qubits n × Bool) × Fin w → Finset (Qubits n)),
        (T : ℝ) ≤ C * Real.sqrt ((t : ℝ) * (2 : ℝ) ^ n) ∧
        ∀ f : Qubits n → Bool, (Finset.univ.filter fun j => f j = true).card = t →
          2 / 3 ≤ probEvent (A.finalState (xorOracle f))
            fun z => out z = Finset.univ.filter fun j => f j = true := by
  sorry

/-- Nannicini p.81, Lemma 4.11 (based on Lem. 3.7 of Berry et al. 2014): let `U`, `V` be
unitaries on `n + 1` and `n` qubits (the first qubit of `U`'s register is the flag) and
`θ ∈ (0, π/2)`. Suppose that for every `n`-qubit state `|ψ⟩`,
`U|0⟩|ψ⟩ = sin θ |0⟩V|ψ⟩ + cos θ |1⟩|ϕ(ψ)⟩`. Then for every state `|ψ⟩` the state
`|Ψ⊥⟩ = U†(cos θ |0⟩V|ψ⟩ − sin θ |1⟩|ϕ(ψ)⟩)` is orthogonal to `|Ψ⟩ = |0⟩|ψ⟩` and satisfies
`(|0⟩⟨0| ⊗ I^{⊗n})|Ψ⊥⟩ = 0`. -/
theorem oblivious_perp_state {n : ℕ} (U : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ)
    (V : Matrix (Qubits n) (Qubits n) ℂ) (θ : ℝ)
    (ϕ : EuclideanSpace ℂ (Qubits n) → EuclideanSpace ℂ (Qubits n))
    (hU : U ∈ Matrix.unitaryGroup (Bool × Qubits n) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Qubits n) ℂ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hact : ∀ ψ : EuclideanSpace ℂ (Qubits n), IsState ψ →
      act U (tensorVec (ket false) ψ) =
        (Real.sin θ : ℂ) • tensorVec (ket false) (act V ψ) +
          (Real.cos θ : ℂ) • tensorVec (ket true) (ϕ ψ))
    (ψ : EuclideanSpace ℂ (Qubits n)) (hψ : IsState ψ) :
    let Ψperp := act (star U) ((Real.cos θ : ℂ) • tensorVec (ket false) (act V ψ) -
      (Real.sin θ : ℂ) • tensorVec (ket true) (ϕ ψ))
    inner ℂ (tensorVec (ket false) ψ) Ψperp = 0 ∧
      act (Matrix.kronecker (Matrix.diagonal fun b : Bool => if b then (0 : ℂ) else 1)
        (1 : Matrix (Qubits n) (Qubits n) ℂ)) Ψperp = 0 := by
  sorry

/-- Nannicini p.82, Theorem 4.12 (Oblivious amplitude amplification; Lem. 3.6 of Berry et al.
2014): in the setting of Lemma 4.11 (`U`, `V` unitaries on `n + 1` and `n` qubits, flag qubit
first, `θ ∈ (0, π/2)`, and `U|0⟩|ψ⟩ = sin θ |0⟩V|ψ⟩ + cos θ |1⟩|ϕ(ψ)⟩` for every `n`-qubit state
`|ψ⟩`; the printed "where |ψ⟩ may depend on |ψ⟩" is a typo for `|ϕ⟩`), let
`R = 2|0⟩⟨0| ⊗ I^{⊗n} − I^{⊗(n+1)}` and `G = −U R† U† R`. Then for every state `|ψ⟩` and every
integer `k > 0`, `G^k U|0⟩|ψ⟩ = sin((2k+1)θ) |0⟩V|ψ⟩ + cos((2k+1)θ) |1⟩|ϕ(ψ)⟩`. -/
theorem oblivious_amplitudeAmplification {n : ℕ}
    (U : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ)
    (V : Matrix (Qubits n) (Qubits n) ℂ) (θ : ℝ)
    (ϕ : EuclideanSpace ℂ (Qubits n) → EuclideanSpace ℂ (Qubits n))
    (hU : U ∈ Matrix.unitaryGroup (Bool × Qubits n) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Qubits n) ℂ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hact : ∀ ψ : EuclideanSpace ℂ (Qubits n), IsState ψ →
      act U (tensorVec (ket false) ψ) =
        (Real.sin θ : ℂ) • tensorVec (ket false) (act V ψ) +
          (Real.cos θ : ℂ) • tensorVec (ket true) (ϕ ψ))
    (ψ : EuclideanSpace ℂ (Qubits n)) (hψ : IsState ψ) (k : ℕ) (hk : 0 < k) :
    let R : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ :=
      Matrix.kronecker (reflAt false) (1 : Matrix (Qubits n) (Qubits n) ℂ)
    let G := -(U * star R * star U * R)
    act (G ^ k) (act U (tensorVec (ket false) ψ)) =
      (Real.sin ((2 * (k : ℝ) + 1) * θ) : ℂ) • tensorVec (ket false) (act V ψ) +
        (Real.cos ((2 * (k : ℝ) + 1) * θ) : ℂ) • tensorVec (ket true) (ϕ ψ) := by
  sorry

end QAlgorithms.Nannicini
