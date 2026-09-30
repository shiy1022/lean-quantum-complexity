import «AMPUNI-fanout-run»
import «AMPUNI-fanout-cost»
import «AMPUNI-top-stack-frame»
import «AMPUNI-retained-finite»
import «AMPUNI-fixed-block-payloads»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open ShiShallow ShiClassQMAAmp ShiClassQMAAmpX

namespace ShiTMFanout

open ShiTMLayoutMachine ShiTMCircuitNormalization ShiTMOuterLift Turing Turing.TM2

theorem unary_eq_encNat (n : Nat) : unary n = (ShiBQP.encNat n).map bit := by
  simp [unary, ShiBQP.encNat, bit]

private theorem ampG_left (n w a off : Nat) (h1 : n ≤ off)
    (h2 : off+n ≤ 3*(n+(w+(a+1)))) (j : Fin n) :
    (ampG n w a off h1 h2 (Fin.castAdd n j)).val = j.val := by
  have h := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).2.1
  apply h _ j.val j.isLt
  simp [ampFanEmb, ampFanVal, j.isLt]

theorem ampG2_left (n w a : Nat) (j : Fin n) :
    (ampG2 n w a (Fin.castAdd n j)).val = j.val := by
  exact ampG_left n w a _ _ _ j

theorem ampG3_left (n w a : Nat) (j : Fin n) :
    (ampG3 n w a (Fin.castAdd n j)).val = j.val := by
  exact ampG_left n w a _ _ _ j

theorem ampG2_right (n w a : Nat) (j : Fin n) :
    (ampG2 n w a (Fin.natAdd n j)).val = (n+3*w+a+1)+j.val := by
  obtain ⟨_, _, _, _, _, h5, _, _, _, _, _, _, _, _⟩ :=
    Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)
  apply h5 _ j.val j.isLt
  have hnot : ¬ n+j.val < n := by omega
  simp [ampFanEmb, ampFanVal, hnot]

theorem ampG3_right (n w a : Nat) (j : Fin n) :
    (ampG3 n w a (Fin.natAdd n j)).val = (2*n+3*w+2*a+2)+j.val := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h9, _, _, _, _⟩ :=
    Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)
  apply h9 _ j.val j.isLt
  have hnot : ¬ n+j.val < n := by omega
  simp [ampFanEmb, ampFanVal, hnot]

/-- Exact byte contract for the first fanout block, with its target-base
value made explicit for the finite machine's unary input register. -/
theorem fanout2_bytes (n w a : Nat) :
    unary n ++ recordBytes (n+3*w+a+1) 0 n =
      (stripCircPrefix (ampFan2X n w a)).map bit := by
  rw [ampFan2X_payload, List.map_append, ← unary_eq_encNat, recordBytes_finRange]
  congr 1
  rw [List.map_flatten]
  apply congrArg List.flatten
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  simp [gateBytes, unary_eq_encNat, ampG2_left, ampG2_right, List.map_append, -Fin.natAdd_eq_addNat]

/-- Exact byte contract for the second fanout block. -/
theorem fanout3_bytes (n w a : Nat) :
    unary n ++ recordBytes (2*n+3*w+2*a+2) 0 n =
      (stripCircPrefix (ampFan3X n w a)).map bit := by
  rw [ampFan3X_payload, List.map_append, ← unary_eq_encNat, recordBytes_finRange]
  congr 1
  rw [List.map_flatten]
  apply congrArg List.flatten
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  simp [gateBytes, unary_eq_encNat, ampG3_left, ampG3_right, List.map_append, -Fin.natAdd_eq_addNat]

/-- The finite emitter produces exactly amplifier fanout block 2, preserving
all stacks outside its declared work set. Unary-register preparation is explicit. -/
theorem fanout2_run (n w a : Nat) (v : Sig) (S : ∀ k, List (OuterGam k))
    (hn : S (port 0) = List.replicate n Cell.mark)
    (hj : S (port 1) = [])
    (hb : S (port 2) = List.replicate (n+3*w+a+1) Cell.mark)
    (hs : S scratch = []) :
    ∃ U : ∀ k, List (OuterGam k),
      run^[2*n*n + n*(2*(n+3*w+a+1)+7) + 4]
        (some ⟨some (.copy 0), v, S⟩) = some ⟨some .finished, none, U⟩
      ∧ U (port 0) = []
      ∧ U (port 1) = List.replicate n Cell.mark
      ∧ U (port 2) = List.replicate ((n+3*w+a+1)+n) Cell.mark
      ∧ U scratch = []
      ∧ U output = ((stripCircPrefix (ampFan2X n w a)).map bit).reverse ++ S output
      ∧ ∀ k, Outside k → U k = S k := by
  obtain ⟨U, hr, h0, h1, h2, ht, ho, hf⟩ :=
    fanout_run n (n+3*w+a+1) v S hn hj hb hs
  refine ⟨U, hr, h0, h1, h2, ht, ?_, hf⟩
  rw [← fanout2_bytes]
  exact ho

/-- The finite emitter produces exactly amplifier fanout block 3, preserving
all stacks outside its declared work set. Unary-register preparation is explicit. -/
theorem fanout3_run (n w a : Nat) (v : Sig) (S : ∀ k, List (OuterGam k))
    (hn : S (port 0) = List.replicate n Cell.mark)
    (hj : S (port 1) = [])
    (hb : S (port 2) = List.replicate (2*n+3*w+2*a+2) Cell.mark)
    (hs : S scratch = []) :
    ∃ U : ∀ k, List (OuterGam k),
      run^[2*n*n + n*(2*(2*n+3*w+2*a+2)+7) + 4]
        (some ⟨some (.copy 0), v, S⟩) = some ⟨some .finished, none, U⟩
      ∧ U (port 0) = []
      ∧ U (port 1) = List.replicate n Cell.mark
      ∧ U (port 2) = List.replicate ((2*n+3*w+2*a+2)+n) Cell.mark
      ∧ U scratch = []
      ∧ U output = ((stripCircPrefix (ampFan3X n w a)).map bit).reverse ++ S output
      ∧ ∀ k, Outside k → U k = S k := by
  obtain ⟨U, hr, h0, h1, h2, ht, ho, hf⟩ :=
    fanout_run n (2*n+3*w+2*a+2) v S hn hj hb hs
  refine ⟨U, hr, h0, h1, h2, ht, ?_, hf⟩
  rw [← fanout3_bytes]
  exact ho

open ShiTMRetainedTop

/-- The emitter lifted to the actual top-level stack signature. The four
retained header/archive stacks are never read or written. -/
def topMachine : Label → Stmt TopGam Label Sig :=
  ShiTMTopFrame.machine machine

def topRun : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  ShiTMStackFrame.run topMachine

def topFiniteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := .inl (port 0)
  k₁ := .inl output
  Γ := TopGam
  Λ := Label
  main := .copy 0
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := topMachine

theorem top_run_frame (H : Fin 4 → List Cell) (steps : Nat)
    (c : Option (Cfg OuterGam Label Sig)) :
    topRun^[steps] (c.map (ShiTMTopFrame.cfg H)) =
      (run^[steps] c).map (ShiTMTopFrame.cfg H) := by
  exact ShiTMTopFrame.run_iter_frame machine H steps c

/-- A complete block run inside `TopGam`, retaining the exact arbitrary
contents of all four added stacks, including the archived verifier. -/
theorem fanout_top_run (n b : Nat) (H : Fin 4 → List Cell)
    (v : Sig) (S : ∀ k, List (OuterGam k))
    (hn : S (port 0) = List.replicate n Cell.mark)
    (hj : S (port 1) = []) (hb : S (port 2) = List.replicate b Cell.mark)
    (hs : S scratch = []) :
    ∃ U : ∀ k, List (OuterGam k),
      topRun^[2*n*n+n*(2*b+7)+4]
        (some ⟨some (.copy 0), v, topStacks S H⟩) =
        some ⟨some .finished, none, topStacks U H⟩
      ∧ U (port 0) = []
      ∧ U (port 1) = List.replicate n Cell.mark
      ∧ U (port 2) = List.replicate (b+n) Cell.mark
      ∧ U scratch = []
      ∧ U output = (unary n ++ recordBytes b 0 n).reverse ++ S output
      ∧ ∀ k, Outside k → U k = S k := by
  obtain ⟨U, hr, h0, h1, h2, ht, ho, hf⟩ := fanout_run n b v S hn hj hb hs
  refine ⟨U, ?_, h0, h1, h2, ht, ho, hf⟩
  have h := top_run_frame H (2*n*n+n*(2*b+7)+4)
    (some ⟨some (.copy 0), v, S⟩)
  rw [hr] at h
  simpa [ShiTMTopFrame.cfg, ShiTMTopFrame.extendStacks, topStacks] using h

/-- Each fanout execution is bounded by one common quadratic in the actual
Boolean retained-description length. Register preparation is not included. -/
theorem fanout_costs_le_retained_length (F : ShiClassQMA.QMAFamily) (n : Nat) :
    let L := (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).length
    (2*n*n + n*(2*(n+3*F.wit n+F.anc n+1)+7) + 4 ≤ 19*L*L) ∧
    (2*n*n + n*(2*(2*n+3*F.wit n+2*F.anc n+2)+7) + 4 ≤ 19*L*L) := by
  let L := (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).length
  have hlen : n+F.wit n+F.anc n+1 ≤ L := by
    dsimp [L]
    simp only [ShiClassQMAU.encQMAFamilyAt, ShiBQP.encNat,
      List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  exact ⟨fanout_cost_le n (n+3*F.wit n+F.anc n+1) L
      (by omega) (by omega) (by omega),
    fanout_cost_le n (2*n+3*F.wit n+2*F.anc n+2) L
      (by omega) (by omega) (by omega)⟩

end ShiTMFanout
