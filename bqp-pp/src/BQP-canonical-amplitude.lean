import «BQP-canonical-paths»
import «BQP-acceptance-pair-counts»

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace BQPPaths
open ShiShallow BQPGates

/-- The actual amplitude uses the explicit executable path functions. -/
theorem canonical_amplitude {n : ℕ} (c : Layered n) (z y : Bits n) :
    runLayered c (fun t => if t = z then 1 else 0) y =
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ hadamardCount c.flatten *
        ∑ w ∈ Finset.univ.filter
          (fun w : Fin (hadamardCount c.flatten) → Bool => forwardRun c.flatten z (List.ofFn w) = y),
          omega ^ (phaseRun c.flatten z (List.ofFn w)).val := by
  classical
  obtain ⟨N, A, P, hN0, hNh, hNg, hA0, hP0, hAh, hPh, hAg, hPg,
    hflat, hsingle, hphase, hrest⟩ := BQPChecked.reference26
  have hN_eq : N = fun m => @hadamardCount m := by
    funext m gs
    induction gs with
    | nil => simpa [hadamardCount] using hN0 m
    | cons g gs ih =>
        cases g with
        | h i => rw [hNh, ih]; simp [hadamardCount]
        | s i => rw [hNg m (.s i) gs (by intro j; simp), ih]; simp [hadamardCount]
        | t i => rw [hNg m (.t i) gs (by intro j; simp), ih]; simp [hadamardCount]
        | x i => rw [hNg m (.x i) gs (by intro j; simp), ih]; simp [hadamardCount]
        | cnot i j hij => rw [hNg m (.cnot i j hij) gs (by intro k; simp), ih]; simp [hadamardCount]
  subst N
  obtain ⟨fw, ph, padj, hfwh, hfws, hfwt, hfwx, hfwc,
    hphh, hphs, hpht, hphx, hphc, hadjh, hadjs, hadjt, hadjx, hadjc,
    hInv, hCoef, hMat, hgateRest⟩ := BQPBridgeReference.gateData
  have hfw : fw = fun m => @forward m := by
    funext m g a v
    cases g with
    | h i => exact hfwh m i a v
    | s i => exact hfws m i a v
    | t i => exact hfwt m i a v
    | x i => exact hfwx m i a v
    | cnot i j hij => exact hfwc m i j hij a v
  have hph : ph = fun m => @phaseStep m := by
    funext m g a v
    cases g with
    | h i => exact hphh m i a v
    | s i => exact hphs m i a v
    | t i => exact hpht m i a v
    | x i => exact hphx m i a v
    | cnot i j hij => exact hphc m i j hij a v
  subst fw
  subst ph
  obtain ⟨Fwd, Bk, Wit, hF0, hFh, hFg, hB0, hBh, hBg, hW0, hWh, hWg,
    hBlen, hWlen, hback, hrecover, hsection, hinject, hbij⟩ :=
    BQPBridgeReference.reindex (fun m => @hadamardCount m) P (fun m => @forward m)
      hN0 hNh hNg hP0 hPh hPg hfwh hInv
  obtain ⟨Pf, hPf0, hPfh, hPfg, homega, hadd, hPhase⟩ :=
    BQPBridgeReference.phaseAgreement (fun m => @hadamardCount m) A P (fun m => @forward m)
      (fun m => @phaseStep m) Fwd Bk
      hN0 hNh hNg hA0 hAh hAg hfwh hphh hCoef hMat
      hF0 hFh hFg hB0 hBh hBg hback
  have hF := forwardRun_unique (Fwd n) (hF0 n) (hFh n) (hFg n)
  have hPf := phaseRun_unique (Pf n) (hPf0 n) (hPfh n) (hPfg n)
  have hsem := fun g hg ψ x => @apply_non_hadamard n g hg ψ x
  rw [runLayered_flatten, hflat n coefficient predecessor hsem]
  have he := reindex_amplitude (hadamardCount c.flatten)
    (A n coefficient predecessor c.flatten) (P n predecessor c.flatten)
    (Fwd n c.flatten z) (Bk n c.flatten z) (Pf n c.flatten z) y z
    (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ hadamardCount c.flatten) omega
    (hBlen n c.flatten z) (hback n coefficient predecessor hsem c.flatten z)
    (by
      intro u v hu hv huv hB
      calc
        u = Wit n predecessor c.flatten (Fwd n c.flatten z u) (Bk n c.flatten z u) :=
          (hrecover n coefficient predecessor hsem c.flatten z u hu).symm
        _ = Wit n predecessor c.flatten (Fwd n c.flatten z v) (Bk n c.flatten z v) := by rw [huv, hB]
        _ = v := hrecover n coefficient predecessor hsem c.flatten z v hv)
    (by
      intro b hb hP
      exact ((hbij n coefficient predecessor hsem c.flatten y z b hb).mp hP).exists)
    (hPhase n coefficient predecessor hsem c.flatten z)
  simpa only [hF, hPf] using he

/-- The concrete residue counts used by the subsequent machine bridge. -/
def circuitCount {n m : ℕ} (c : Layered (n + m)) (x : Bits n)
    (out : Fin (n + m)) (d : ℕ) : ℕ :=
  let z := Fin.append x (fun _ : Fin m => false)
  endpointCount
    (fun w : Fin (hadamardCount c.flatten) → Bool => forwardRun c.flatten z (List.ofFn w))
    (fun w : Fin (hadamardCount c.flatten) → Bool => (phaseRun c.flatten z (List.ofFn w)).val)
    (fun y => y out) d

theorem canonical_acceptance {n m : ℕ} (c : Layered (n + m)) (x : Bits n)
    (out : Fin (n + m)) :
    acceptProb c x out = (1 / 2 : ℝ) ^ hadamardCount c.flatten *
      (((circuitCount c x out 0 : ℝ) - (circuitCount c x out 4 : ℝ)) +
        Real.sqrt 2 * ((circuitCount c x out 1 : ℝ) - (circuitCount c x out 3 : ℝ))) := by
  classical
  refine amplitude_pair_count (hadamardCount c.flatten)
    (fun w : Fin (hadamardCount c.flatten) → Bool =>
      forwardRun c.flatten (Fin.append x (fun _ : Fin m => false)) (List.ofFn w))
    (fun w : Fin (hadamardCount c.flatten) → Bool =>
      (phaseRun c.flatten (Fin.append x (fun _ : Fin m => false)) (List.ofFn w)).val)
    (fun y => y out) (runLayered c (inputState x)) ?_
  intro y
  have hi : inputState (m := m) x =
      fun t => if t = Fin.append x (fun _ : Fin m => false) then (1 : ℂ) else 0 := by
    funext t
    exact inputState_delta x t
  rw [hi]
  exact canonical_amplitude c _ y

end BQPPaths
