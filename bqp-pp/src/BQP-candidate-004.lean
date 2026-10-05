import Definitions.Def_ShiShallow_Core
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiBQP_acceptance_agreement_for_the_route_a_compiled_program

namespace BQPReferenceValidation.Source4
/-
ASM-ACCb.  THE ACCEPTANCE AGREEMENT FOR THE ROUTE-(A) COMPILED PROGRAM.

This is the assembly slice: it glues BRIDGE-Dd (the input-loading sweep and the endpoint
test), BRIDGE-SIMm (the gate sweep, instantiated once at the forward blocks and once at
the adjoint blocks on the reversed gate list), BRIDGE-SIMk (the output-wire test block)
and BRIDGE-Ad (the wrong-length law) into a single statement about
`ev (C n m' gs x out) w` -- conjunct (6) of BRIDGE-SEM, adapted to route (A).

TWO DELIBERATE DEPARTURES FROM THE PROBE'S BRIDGE-SEM.

(i)  DOUBLED, NOT SINGLE-PASS.  `C` emits `U`, the output-wire test, `U†` and the endpoint
     test, so `hc (C …) = N gs + N gs`.  The witness is therefore split `w1 ++ w2`, one
     half per pass, and the wrong-length clause is stated at `N gs + N gs`.

(ii) THE PHASE IS THE CONSTRUCTIVE `ZMod 8` FOLD, not an `∃ e` witness.  `Pf` and `Pa` are
     the forward and adjoint folds built by BRIDGE-SIMi/SIMm/SIMo; nothing here chooses a
     witness, and no primitive-root fact about `ω` is used anywhere.

The initial basis string is carried as a variable `z` pinned pointwise to the padded
classical input, so no seven-line `dite` has to be repeated in every conjunct.

A branch survives exactly when the output wire reads `1` after the forward pass AND the
adjoint pass returns the tape to the input, which is the acceptance criterion the counting
argument needs; on a surviving branch `ev` returns the sum of the two folds.  The last
conjunct is a non-vacuity witness: the `some` branch is inhabited.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiShallow

theorem _root_.BQPReferenceValidation.candidate4 :
    ∀ (sTr : (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool) → ℕ →
          (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool))
      (hc : List ℕ → ℕ) (ev : List ℕ → List Bool → Option ℕ)
      (N : ∀ m : ℕ, List (Instr m) → ℕ) (B BA : ∀ m : ℕ, Instr m → List ℕ)
      (D DA : ∀ m : ℕ, List (Instr m) → List ℕ) (L E : List Bool → List ℕ)
      (T : ∀ n m' : ℕ, Bits n → List Bool)
      (Cp : ∀ n m' : ℕ, List (Instr (n + m')) → Bits n → Fin (n + m') → List ℕ)
      (fw : ∀ m : ℕ, Instr m → Bool → Bits m → Bits m)
      (Phs : ∀ m : ℕ, Instr m → Bool → Bits m → ZMod 8)
      (Fwd : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → Bits m)
      (Pf Pa : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → ZMod 8),
      -- CHECK-1f (II): the one-branch evaluator
      (∀ (Q : List ℕ) (bs : List Bool),
          ev Q bs = (match Q.foldl sTr (0, [], [], false, false, false, bs) with
                     | (p, _, _, _, de, bd, w) =>
                         if de || bd || !w.isEmpty then none else some p.val)) →
      -- PATH-1b: `N` counts the Hadamard gates
      (∀ m : ℕ, N m [] = 0) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)), N m (Instr.h i :: gs) = N m gs + 1) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)), (∀ i, g ≠ Instr.h i) →
          N m (g :: gs) = N m gs) →
      -- BRIDGE-SIMn: the Hadamard count is reversal-invariant
      (∀ (m : ℕ) (gs : List (Instr m)), N m gs.reverse = N m gs) →
      -- BRIDGE-SIMi/SIMm: the forward phase fold
      (∀ (m : ℕ) (z : Bits m) (w : List Bool), Pf m [] z w = 0) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          Pf m (Instr.h i :: gs) z w
            = Phs m (Instr.h i) w.headI z
                + Pf m gs (fw m (Instr.h i) w.headI z) w.tail) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          (∀ i, g ≠ Instr.h i) →
          Pf m (g :: gs) z w = Phs m g false z + Pf m gs (fw m g false z) w) →
      -- BRIDGE-SIMo: the adjoint phase fold, at the empty gate list
      (∀ (m : ℕ) (z : Bits m) (w : List Bool), Pa m [] z w = 0) →
      -- BRIDGE-SIMf/SIMh: the forward state, at the empty gate list
      (∀ (m : ℕ) (z : Bits m) (w : List Bool), Fwd m [] z w = z) →
      -- BRIDGE-SIMn: the forward state ignores witness bits past the ones it consumes
      (∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (w u : List Bool),
          w.length = N m gs → Fwd m gs z (w ++ u) = Fwd m gs z w) →
      -- BRIDGE-SIMm at the FORWARD blocks
      (∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool), N m gs ≤ w.length →
          ∃ ct' : Bool,
            ((gs.map (B m)).flatten).foldl sTr (p, [], List.ofFn z, ct, de, bd, w)
              = (p + Pf m gs z w, [], List.ofFn (Fwd m gs z w), ct', de, bd,
                  w.drop (N m gs))) →
      -- BRIDGE-SIMm at the ADJOINT blocks
      (∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool), N m gs ≤ w.length →
          ∃ ct' : Bool,
            ((gs.map (BA m)).flatten).foldl sTr (p, [], List.ofFn z, ct, de, bd, w)
              = (p + Pa m gs z w, [], List.ofFn (Fwd m gs z w), ct', de, bd,
                  w.drop (N m gs))) →
      -- BRIDGE-SIMk: the output-wire test block, on basis strings
      (∀ (m : ℕ) (out : Fin m) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool),
          (List.replicate (out : ℕ) 1 ++ ([8] ++ List.replicate (out : ℕ) 0)).foldl sTr
              (p, [], List.ofFn z, ct, de, bd, w)
            = (p, [], List.ofFn z, ct, de || !(z out), bd, w)) →
      -- BRIDGE-Dd: INPUT LOADING
      (∀ (l : List Bool) (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
          (L l ++ List.replicate l.length 0).foldl sTr (p, [], [], ct, de, bd, w)
            = (p, [], l, ct, de, bd, w)) →
      -- BRIDGE-Dd: THE ENDPOINT TEST
      (∀ (l e : List Bool), l.length = e.length →
          ∀ (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
            (E l ++ List.replicate l.length 0).foldl sTr (p, [], e, ct, de, bd, w)
              = (p, [], e, ct, de || decide (e ≠ l), bd, w)) →
      -- BRIDGE-C2c: the gate list, forward and reversed
      (∀ m : ℕ, D m [] = []) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)), D m (g :: gs) = B m g ++ D m gs) →
      (∀ m : ℕ, DA m [] = []) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)),
          DA m (g :: gs) = DA m gs ++ BA m g) →
      -- BRIDGE-C2c: the padded input tape
      (∀ (n m' : ℕ) (x : Bits n), T n m' x
          = List.ofFn (fun k : Fin (n + m') =>
              if h : (k : ℕ) < n then x ⟨(k : ℕ), h⟩ else false)) →
      -- BRIDGE-C2c: the whole route-(A) program
      (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m')),
          Cp n m' gs x out
            = L (T n m' x) ++ (List.replicate (n + m') 0 ++ (D (n + m') gs
                ++ ((List.replicate (out : ℕ) 1 ++ ([8] ++ List.replicate (out : ℕ) 0))
                  ++ (DA (n + m') gs
                    ++ (E (T n m' x) ++ List.replicate (n + m') 0)))))) →
      -- BRIDGE-C2c (1): the DOUBLED witness budget
      (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m')),
          hc (Cp n m' gs x out) = N (n + m') gs + N (n + m') gs) →
      -- BRIDGE-C2c (3): every emitted opcode is legal and non-aborting
      (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m'))
          (c : ℕ), c ∈ Cp n m' gs x out → c ≤ 8) →
      -- BRIDGE-SIMe: the tape of a basis string
      (∀ (m : ℕ) (z : Bits m), (List.ofFn z).length = m) →
      -- BRIDGE-Ad (d): every witness of the wrong length is rejected
      (∀ (P : List ℕ) (w : List Bool), (∀ c ∈ P, c % 16 ≤ 9) →
          w.length ≠ hc P → ev P w = none) →
      -- (6) ACCEPTANCE AGREEMENT: on a correctly budgeted witness, split one half per
      -- pass, `ev` fails EXACTLY on the branches the output-wire test or the endpoint
      -- test rejects
      (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m'))
          (z : Bits (n + m')),
          (∀ k : Fin (n + m'), z k = if h : (k : ℕ) < n then x ⟨(k : ℕ), h⟩ else false) →
          ∀ w1 w2 : List Bool, w1.length = N (n + m') gs →
            w2.length = N (n + m') gs →
              (ev (Cp n m' gs x out) (w1 ++ w2) = none
                ↔ ¬(Fwd (n + m') gs z w1 out = true
                      ∧ Fwd (n + m') gs.reverse (Fwd (n + m') gs z w1) w2 = z)))
      -- (5') and on a surviving branch it returns the CONSTRUCTIVE `ZMod 8` fold: the
      -- forward phase of the first pass plus the adjoint phase of the second
      ∧ (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m'))
          (z : Bits (n + m')),
          (∀ k : Fin (n + m'), z k = if h : (k : ℕ) < n then x ⟨(k : ℕ), h⟩ else false) →
          ∀ w1 w2 : List Bool, w1.length = N (n + m') gs →
            w2.length = N (n + m') gs →
              Fwd (n + m') gs z w1 out = true →
                Fwd (n + m') gs.reverse (Fwd (n + m') gs z w1) w2 = z →
                  ev (Cp n m' gs x out) (w1 ++ w2)
                    = some ((Pf (n + m') gs z w1
                        + Pa (n + m') gs.reverse (Fwd (n + m') gs z w1) w2).val))
      -- (7) every witness of the wrong length is rejected, at the DOUBLED budget
      ∧ (∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n) (out : Fin (n + m'))
          (w : List Bool), w.length ≠ N (n + m') gs + N (n + m') gs →
            ev (Cp n m' gs x out) w = none)
      -- NON-VACUITY: the accepting branch is inhabited -- one wire, the empty circuit,
      -- classical input `1`, output wire `0`, empty witness, phase `0`
      ∧ ev (Cp 1 0 [] (fun _ => true) ⟨0, by omega⟩) [] = some 0 := by
  intro sTr hc ev N B BA D DA L E T Cp fw Phs Fwd Pf Pa
  intro hev hN0 hNh hNg hNrev hPf0 hPfh hPfg hPa0 hFwd0 hFwdTr hSwF hSwA hOut hLoad hEnd
  intro hD0 hDc hDA0 hDAc hT hCprog hCbud hCop hofFnLen hWrong
  -- the fold over a concatenation of opcode streams
  have hfold : ∀ (P Q : List ℕ)
      (s : ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool),
      (P ++ Q).foldl sTr s = Q.foldl sTr (P.foldl sTr s) := by
    intro P Q s
    rw [List.foldl_append]
  -- the two compiled gate sweeps, as flattened block maps
  have hDflat : ∀ (m : ℕ) (gs : List (Instr m)), D m gs = (gs.map (B m)).flatten := by
    intro m gs
    induction gs with
    | nil => rw [hD0]; simp
    | cons g gs ih => rw [hDc, ih]; simp
  have hDAflat : ∀ (m : ℕ) (gs : List (Instr m)),
      DA m gs = (gs.reverse.map (BA m)).flatten := by
    intro m gs
    induction gs with
    | nil => rw [hDA0]; simp
    | cons g gs ih => rw [hDAc, ih]; simp
  -- the forward phase fold ignores witness bits past the ones it consumes
  have hPfTr : ∀ (m : ℕ) (gs : List (Instr m)) (z : Bits m) (w u : List Bool),
      w.length = N m gs → Pf m gs z (w ++ u) = Pf m gs z w := by
    intro m gs
    induction gs with
    | nil => intro z w u _; rw [hPf0, hPf0]
    | cons g gs ih =>
      intro z w u hw
      by_cases hg : ∀ i, g ≠ Instr.h i
      · rw [hNg m g gs hg] at hw
        rw [hPfg m g gs z (w ++ u) hg, hPfg m g gs z w hg,
          ih (fw m g false z) w u hw]
      · push_neg at hg
        obtain ⟨i, hi⟩ := hg
        subst hi
        rw [hNh m i gs] at hw
        cases w with
        | nil => exact (Nat.succ_ne_zero (N m gs) hw.symm).elim
        | cons b w' =>
          have hw' : w'.length = N m gs := by simpa using hw
          rw [hPfh m i gs z (b :: w' ++ u), hPfh m i gs z (b :: w')]
          exact congrArg (fun t : ZMod 8 => Phs m (Instr.h i) b z + t)
            (ih (fw m (Instr.h i) b z) w' u hw')
  -- THE RUN OF THE WHOLE PROGRAM
  have hmain : ∀ (n m' : ℕ) (gs : List (Instr (n + m'))) (x : Bits n)
      (out : Fin (n + m')) (z : Bits (n + m')),
      (∀ k : Fin (n + m'), z k = if h : (k : ℕ) < n then x ⟨(k : ℕ), h⟩ else false) →
      ∀ w1 w2 : List Bool, w1.length = N (n + m') gs → w2.length = N (n + m') gs →
        ev (Cp n m' gs x out) (w1 ++ w2)
          = (if (!(Fwd (n + m') gs z w1 out)
                  || decide (List.ofFn (Fwd (n + m') gs.reverse
                      (Fwd (n + m') gs z w1) w2) ≠ List.ofFn z)) = true
             then none
             else some ((Pf (n + m') gs z w1
                 + Pa (n + m') gs.reverse (Fwd (n + m') gs z w1) w2).val)) := by
    intro n m' gs x out z hz w1 w2 h1 h2
    have hTz : T n m' x = List.ofFn z := by
      rw [hT]
      have hfun : (fun k : Fin (n + m') =>
          if h : (k : ℕ) < n then x ⟨(k : ℕ), h⟩ else false) = z := by
        funext k
        rw [hz k]
      rw [hfun]
    have hload : (L (List.ofFn z) ++ List.replicate (n + m') 0).foldl sTr
          ((0 : ZMod 8), [], [], false, false, false, w1 ++ w2)
        = ((0 : ZMod 8), [], List.ofFn z, false, false, false, w1 ++ w2) := by
      have h := hLoad (List.ofFn z) 0 false false false (w1 ++ w2)
      rw [hofFnLen] at h
      exact h
    have hendp : ∀ (y : Bits (n + m')) (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
        (E (List.ofFn z) ++ List.replicate (n + m') 0).foldl sTr
            (p, [], List.ofFn y, ct, de, bd, w)
          = (p, [], List.ofFn y, ct, de || decide (List.ofFn y ≠ List.ofFn z), bd, w) := by
      intro y p ct de bd w
      have h := hEnd (List.ofFn z) (List.ofFn y) (by rw [hofFnLen, hofFnLen])
        p ct de bd w
      rw [hofFnLen] at h
      exact h
    obtain ⟨ct1, hc1⟩ := hSwF (n + m') gs z 0 false false false (w1 ++ w2)
      (by rw [List.length_append]; omega)
    have hdrop1 : (w1 ++ w2).drop (N (n + m') gs) = w2 := by
      rw [← h1]
      exact List.drop_left
    have hPfe : Pf (n + m') gs z (w1 ++ w2) = Pf (n + m') gs z w1 :=
      hPfTr (n + m') gs z w1 w2 h1
    have hFwde : Fwd (n + m') gs z (w1 ++ w2) = Fwd (n + m') gs z w1 :=
      hFwdTr (n + m') gs z w1 w2 h1
    rw [hdrop1, hPfe, hFwde, zero_add] at hc1
    obtain ⟨ct3, hc3⟩ := hSwA (n + m') gs.reverse (Fwd (n + m') gs z w1)
      (Pf (n + m') gs z w1) ct1 (false || !(Fwd (n + m') gs z w1 out)) false w2
      (by rw [hNrev]; omega)
    have hdrop2 : w2.drop (N (n + m') gs.reverse) = [] := by
      rw [hNrev, ← h2]
      exact List.drop_length
    rw [hdrop2] at hc3
    rw [hev, hCprog, hTz,
      ← List.append_assoc (L (List.ofFn z)) (List.replicate (n + m') 0),
      hfold (L (List.ofFn z) ++ List.replicate (n + m') 0), hload, hDflat,
      hfold ((gs.map (B (n + m'))).flatten), hc1,
      hfold (List.replicate (out : ℕ) 1 ++ ([8] ++ List.replicate (out : ℕ) 0)), hOut,
      hDAflat, hfold ((gs.reverse.map (BA (n + m'))).flatten), hc3, hendp]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m' gs x out z hz w1 w2 h1 h2
    rw [hmain n m' gs x out z hz w1 w2 h1 h2]
    constructor
    · intro hn hcon
      obtain ⟨hout, heq⟩ := hcon
      rw [hout, heq] at hn
      simp at hn
    · intro hcon
      cases hb : Fwd (n + m') gs z w1 out with
      | false => simp
      | true =>
        have hne : List.ofFn (Fwd (n + m') gs.reverse (Fwd (n + m') gs z w1) w2)
            ≠ List.ofFn z := fun h => hcon ⟨hb, List.ofFn_inj.mp h⟩
        simp [hne]
  · intro n m' gs x out z hz w1 w2 h1 h2 hout heq
    rw [hmain n m' gs x out z hz w1 w2 h1 h2, hout, heq]
    simp
  · intro n m' gs x out w hw
    refine hWrong (Cp n m' gs x out) w ?_ ?_
    · intro c hcm
      have h8 := hCop n m' gs x out c hcm
      omega
    · rw [hCbud]
      exact hw
  · have hz : ∀ k : Fin (1 + 0), (fun _ : Fin (1 + 0) => true) k
        = if h : (k : ℕ) < 1 then (fun _ : Fin 1 => true) ⟨(k : ℕ), h⟩ else false := by
      intro k
      have hk : (k : ℕ) < 1 := by
        have := k.isLt
        omega
      rw [dif_pos hk]
    have h := hmain 1 0 [] (fun _ => true) ⟨0, by omega⟩ (fun _ => true) hz [] []
      (by simp only [List.length_nil, hN0]) (by simp only [List.length_nil, hN0])
    simp only [List.reverse_nil, hFwd0, hPf0, hPa0] at h
    simpa using h

end BQPReferenceValidation.Source4

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate4
    let target ← getConstInfo ``ShiBQP.acceptance_agreement_for_the_route_a_compiled_program
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.acceptance_agreement_for_the_route_a_compiled_program"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.acceptance_agreement_for_the_route_a_compiled_program"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.acceptance_agreement_for_the_route_a_compiled_program"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate4
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.acceptance_agreement_for_the_route_a_compiled_program; axioms {axioms}"
