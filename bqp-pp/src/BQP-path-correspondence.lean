import «BQP-gate-semantics»
import «BQP-bridge-bijection-reference»
import «BQP-bridge-gate-reference»
import «BQP-bridge-phase-reference»

/-! Instantiate the archived path reindexing proof at the actual circuit gates.
No forward/inverse gate-action hypotheses remain in this interface. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace BQPPaths
open ShiShallow BQPGates

theorem forward_backward_correspondence :
    ∃ (N : ∀ n : ℕ, List (Instr n) → ℕ)
      (A : ∀ n : ℕ, List (Instr n) → Bits n → List Bool → ℂ)
      (P Fwd : ∀ n : ℕ, List (Instr n) → Bits n → List Bool → Bits n)
      (Bk Wit : ∀ n : ℕ, List (Instr n) → Bits n → List Bool → List Bool)
      (Pf : ∀ n : ℕ, List (Instr n) → Bits n → List Bool → ZMod 8),
      (∀ (n : ℕ) (gs : List (Instr n)), N n gs =
        gs.countP (fun g => match g with | .h _ => true | _ => false)) ∧
      (∀ (n : ℕ) (c : Layered n) (ψ : QState n) (y : Bits n),
        runLayered c ψ y = ∑ b : Fin (N n c.flatten) → Bool,
          A n c.flatten y (List.ofFn b) * ψ (P n c.flatten y (List.ofFn b))) ∧
      (∀ (n : ℕ) (gs : List (Instr n)) (z : Bits n) (w : List Bool),
        (Bk n gs z w).length = N n gs) ∧
      (∀ (n : ℕ) (gs : List (Instr n)) (z : Bits n) (w : List Bool),
        P n gs (Fwd n gs z w) (Bk n gs z w) = z) ∧
      (∀ (n : ℕ) (gs : List (Instr n)) (z : Bits n) (w : List Bool),
        w.length = N n gs → Wit n gs (Fwd n gs z w) (Bk n gs z w) = w) ∧
      (∀ (n : ℕ) (gs : List (Instr n)) (y z : Bits n) (bits : List Bool),
        bits.length = N n gs →
          (P n gs y bits = z ↔ ∃! w : List Bool,
            w.length = N n gs ∧ Fwd n gs z w = y ∧ Bk n gs z w = bits)) ∧
      (∀ (n : ℕ) (gs : List (Instr n)) (z : Bits n) (w : List Bool),
        A n gs (Fwd n gs z w) (Bk n gs z w) =
          ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ N n gs * omega ^ (Pf n gs z w).val) := by
  obtain ⟨N, A, P, hN0, hNh, hNg, hA0, hP0, hAh, hPh, hAg, hPg,
    hflat, hsingle, hphase, hrest⟩ := BQPChecked.reference26
  obtain ⟨fw, ph, padj, hfwh, hfws, hfwt, hfwx, hfwc,
    hphh, hphs, hpht, hphx, hphc, hadjh, hadjs, hadjt, hadjx, hadjc,
    hInv, hCoef, hMat, hgateRest⟩ := BQPBridgeReference.gateData
  obtain ⟨Fwd, Bk, Wit, hF0, hFh, hFg, hB0, hBh, hBg, hW0, hWh, hWg,
    hBlen, hWlen, hback, hrecover, hsection, hinject, hbij⟩ :=
    BQPBridgeReference.reindex N P fw hN0 hNh hNg hP0 hPh hPg hfwh hInv
  obtain ⟨Pf, hPf0, hPfh, hPfg, homega, hadd, hPhase⟩ :=
    BQPBridgeReference.phaseAgreement N A P fw ph Fwd Bk
      hN0 hNh hNg hA0 hAh hAg hfwh hphh hCoef hMat
      hF0 hFh hFg hB0 hBh hBg hback
  refine ⟨N, (fun n => A n coefficient predecessor), (fun n => P n predecessor),
    Fwd, Bk, (fun n => Wit n predecessor), Pf, ?_, ?_, hBlen, ?_, ?_, ?_, ?_⟩
  · intro n gs
    induction gs with
    | nil => simpa using hN0 n
    | cons g gs ih =>
        cases g with
        | h i => rw [hNh, ih]; simp
        | s i => rw [hNg n (.s i) gs (by intro j; simp), ih]; simp
        | t i => rw [hNg n (.t i) gs (by intro j; simp), ih]; simp
        | x i => rw [hNg n (.x i) gs (by intro j; simp), ih]; simp
        | cnot i j hij => rw [hNg n (.cnot i j hij) gs (by intro k; simp), ih]; simp
  · intro n c ψ y
    rw [runLayered_flatten]
    exact hflat n coefficient predecessor
      (fun g hg ψ x => apply_non_hadamard g hg ψ x) c.flatten ψ y
  · intro n gs z w
    exact hback n coefficient predecessor
      (fun g hg ψ x => apply_non_hadamard g hg ψ x) gs z w
  · intro n gs z w hw
    exact hrecover n coefficient predecessor
      (fun g hg ψ x => apply_non_hadamard g hg ψ x) gs z w hw
  · intro n gs y z bits hb
    exact hbij n coefficient predecessor
      (fun g hg ψ x => apply_non_hadamard g hg ψ x) gs y z bits hb

  · intro n gs z w
    exact hPhase n coefficient predecessor
      (fun g hg ψ x => apply_non_hadamard g hg ψ x) gs z w

end BQPPaths
