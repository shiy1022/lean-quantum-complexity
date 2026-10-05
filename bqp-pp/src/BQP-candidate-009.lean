import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.OfFn
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Theorems.Thm_ShiBQP_doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance

namespace BQPReferenceValidation.Source9
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

/-! ASM-CARD: `C d = N d`.

THE PAIR COUNT OF A CIRCUIT EQUALS THE SINGLE-RUN COUNT OF ITS DOUBLED PROGRAM.

`C d` counts ORDERED PAIRS of forward runs of a circuit `U` on `Nh` witness bits that land on
the SAME output string, pass the output-wire test, and differ in accumulated phase by `d`.
`N d` counts SINGLE runs of the doubled program `Q = U ; out-test ; U† ; endpoint-test` on
`2 * Nh` witness bits whose evaluator reports phase `d`.  The theorem is that the two counts
agree, which is the last combinatorial step of the `BQP ⊆ PP` bridge.

THE STATEMENT IS ALPHABET-GENERIC (gotcha 214): it mentions neither the gate type nor the
basis-string type of the circuit model, only

* an abstract basis-string type `S` and phase group `G`;
* `Fw w` -- the forward endpoint of the run on witness `w`, from the fixed start state;
* `Bkk w` -- the list of input-side bits the Hadamards destroyed along that run;
* `Pf w` -- the accumulated phase of that run;
* `outb` -- the output-wire test; `adj y v` -- the verdict of the adjoint pass started at `y`
  on witness `v` followed by the endpoint test; `Pa y v` -- the phase that pass pays;
* `J` -- the inverse reindexing, which is `Bkk` for the REVERSED gate list;
* `ev` -- the one-branch evaluator of the doubled program, and `val : G → ℕ` the injection
  through which it reports the phase (`ZMod.val`, downstream).

EVERY CIRCUIT FACT IS A HYPOTHESIS, and each is a literal instance of an accepted theorem:

* `hBlen`, `hInj`  -- BRIDGE-SIMh (the length of the destroyed-bit list; injectivity of the
  reindexing `w ↦ (Fw w, Bkk w)`).
* `hRev`           -- BRIDGE-SIMn, last conjunct: running the REVERSED gate list from the
  forward endpoint on the REVERSED destroyed-bit list returns to the start state.
* `hJlen`, `hJ`    -- BRIDGE-SIMn, last conjunct AGAIN, instantiated at `gs.reverse` and
  simplified by `gs.reverse.reverse = gs`; this is what makes the correspondence SURJECTIVE.
* `hPh`            -- BRIDGE-SIMo, last conjunct: the adjoint pass pays the NEGATED phase.
* `hEv`            -- the acceptance/phase law of the doubled program on a split witness
  `u ++ v`; that is the companion assembly slice.

THE PHASE IS THE CONSTRUCTIVE FOLD, NOT AN EXISTENTIAL EXPONENT (gotcha 281).  `Pf` and `Pa`
land in an abstract additive group `G`, instantiated at `ZMod 8` by BRIDGE-SIMi's fold; the
pair's phase datum is the GROUP DIFFERENCE `Pf u - Pf t`, not `(e₁ % 8 + 8 - e₂ % 8) % 8`.
Nothing here needs `ω ↦ ω ^ k` to be injective, and no choice principle is used.

THE PROOF is the `w = w₁ ++ w₂` split followed by one bijection.  `Fin.appendEquiv` turns the
count over `Fin (Nh + Nh) → Bool` into a count over pairs; on pairs the map is
  `(u, t) ↦ (u, (Bkk t).reverse)`,
i.e. the second forward run is replayed BACKWARDS as the adjoint pass.  Its inverse is
`(u, v) ↦ (u, J (Fw u) v)`.  `hRev` makes the map land in the accepted set, `hPh` turns the
adjoint phase into `- Pf t` so that the doubled run's phase `Pf u + Pa (Fw u) v` is exactly
the pair's difference `Pf u - Pf t`, `hInj` gives one round trip and `hJ` the other.

NON-VACUITY IS A CONJUNCT, NOT A CLAIM IN PROSE (gotcha 277).  Eight hypotheses is enough
rope to hang oneself: the second conjunct exhibits a CONCRETE instance -- one wire, one
Hadamard, `S = Bool`, `G = ZMod 8`, start state `false`, `Nh = 1`, `d = 0` -- satisfying
every hypothesis, and records that BOTH counts are `1`, not `0`.  So the hypothesis set is
consistent AND the conclusion is not the trivial `0 = 0`.  The instance is the genuine
`⟨0| H Π H |0⟩ = 1/2` circuit of CHECK-1f conjunct (VI). -/

open Finset

private def asmToFn (n : ℕ) (w : List Bool) : Fin n → Bool := fun i => w.getD i.val false

private lemma asm_toFn_ofFn {n : ℕ} (b : Fin n → Bool) : asmToFn n (List.ofFn b) = b := by
  funext i
  have hlen : (i : ℕ) < (List.ofFn b).length := by simp
  have h1 : (List.ofFn b).getD (i : ℕ) false = (List.ofFn b)[(i : ℕ)]'hlen :=
    (List.getElem_eq_getD false).symm
  rw [asmToFn, h1]
  simp

private lemma asm_ofFn_toFn {n : ℕ} (w : List Bool) (h : w.length = n) :
    List.ofFn (asmToFn n w) = w := by
  subst h
  have hfun : asmToFn w.length w = fun i : Fin w.length => w[(i : ℕ)] := by
    funext i
    exact (List.getElem_eq_getD false).symm
  rw [hfun]
  exact List.ofFn_getElem

theorem _root_.BQPReferenceValidation.candidate9 :
    (∀ (S : Type) [DecidableEq S] (G : Type) [AddCommGroup G] [DecidableEq G]
      (Nh : ℕ)
      (Fw : List Bool → S)
      (Bkk : List Bool → List Bool)
      (Pf : List Bool → G)
      (outb : S → Bool)
      (adj : S → List Bool → Bool)
      (Pa : S → List Bool → G)
      (J : S → List Bool → List Bool)
      (val : G → ℕ)
      (ev : List Bool → Option ℕ)
      (d : G),
      -- the evaluator reports the phase through an injection
      Function.Injective val →
      -- BRIDGE-SIMh: one destroyed bit per Hadamard
      (∀ w : List Bool, (Bkk w).length = Nh) →
      -- BRIDGE-SIMn: the reversed run on the reversed destroyed-bit list returns to the start
      (∀ w : List Bool, w.length = Nh → adj (Fw w) (Bkk w).reverse = true) →
      -- BRIDGE-SIMo: the adjoint pass pays the negated phase
      (∀ w : List Bool, w.length = Nh → Pa (Fw w) (Bkk w).reverse + Pf w = 0) →
      -- BRIDGE-SIMh: the reindexing `w ↦ (Fw w, Bkk w)` is injective
      (∀ w1 w2 : List Bool, w1.length = Nh → w2.length = Nh →
          Fw w1 = Fw w2 → Bkk w1 = Bkk w2 → w1 = w2) →
      -- BRIDGE-SIMn at the REVERSED gate list: the reindexing is onto the surviving pass
      (∀ (y : S) (v : List Bool), (J y v).length = Nh) →
      (∀ (y : S) (v : List Bool), v.length = Nh → adj y v = true →
          Fw (J y v) = y ∧ Bkk (J y v) = v.reverse) →
      -- the doubled program on a split witness: it accepts exactly the surviving branches,
      -- and reports the sum of the two passes' phases
      (∀ u v : List Bool, u.length = Nh → v.length = Nh →
          ev (u ++ v)
            = (if outb (Fw u) = true ∧ adj (Fw u) v = true
                then some (val (Pf u + Pa (Fw u) v)) else none)) →
      -- `C d = N d`
      (Finset.univ.filter (fun q : (Fin Nh → Bool) × (Fin Nh → Bool) =>
          outb (Fw (List.ofFn q.1)) = true
            ∧ Fw (List.ofFn q.1) = Fw (List.ofFn q.2)
            ∧ Pf (List.ofFn q.1) - Pf (List.ofFn q.2) = d)).card
        = (Finset.univ.filter (fun b : Fin (Nh + Nh) → Bool =>
            ev (List.ofFn b) = some (val d))).card)
    -- NON-VACUITY: one wire, one Hadamard, `Nh = 1`, `d = 0` -- every hypothesis holds and
    -- BOTH counts are `1`
    ∧ (∃ (Fw : List Bool → Bool) (Bkk : List Bool → List Bool) (Pf : List Bool → ZMod 8)
        (outb : Bool → Bool) (adj : Bool → List Bool → Bool)
        (Pa : Bool → List Bool → ZMod 8) (J : Bool → List Bool → List Bool)
        (ev : List Bool → Option ℕ),
        Function.Injective (ZMod.val : ZMod 8 → ℕ)
        ∧ (∀ w : List Bool, (Bkk w).length = 1)
        ∧ (∀ w : List Bool, w.length = 1 → adj (Fw w) (Bkk w).reverse = true)
        ∧ (∀ w : List Bool, w.length = 1 → Pa (Fw w) (Bkk w).reverse + Pf w = 0)
        ∧ (∀ w1 w2 : List Bool, w1.length = 1 → w2.length = 1 →
            Fw w1 = Fw w2 → Bkk w1 = Bkk w2 → w1 = w2)
        ∧ (∀ (y : Bool) (v : List Bool), (J y v).length = 1)
        ∧ (∀ (y : Bool) (v : List Bool), v.length = 1 → adj y v = true →
            Fw (J y v) = y ∧ Bkk (J y v) = v.reverse)
        ∧ (∀ u v : List Bool, u.length = 1 → v.length = 1 →
            ev (u ++ v)
              = (if outb (Fw u) = true ∧ adj (Fw u) v = true
                  then some (ZMod.val (Pf u + Pa (Fw u) v)) else none))
        ∧ (Finset.univ.filter (fun q : (Fin 1 → Bool) × (Fin 1 → Bool) =>
            outb (Fw (List.ofFn q.1)) = true
              ∧ Fw (List.ofFn q.1) = Fw (List.ofFn q.2)
              ∧ Pf (List.ofFn q.1) - Pf (List.ofFn q.2) = (0 : ZMod 8))).card = 1
        ∧ (Finset.univ.filter (fun b : Fin (1 + 1) → Bool =>
            ev (List.ofFn b) = some (ZMod.val (0 : ZMod 8)))).card = 1) := by
  constructor
  intro S _ G _ _ Nh Fw Bkk Pf outb adj Pa J val ev d
  intro hval hBlen hRev hPh hInj hJlen hJ hEv
  -- lengths of the two kinds of witness list
  have hlenOfFn : ∀ b : Fin Nh → Bool, (List.ofFn b).length = Nh := by
    intro b; simp
  have hlenRev : ∀ w : List Bool, (Bkk w).reverse.length = Nh := by
    intro w; simpa using hBlen w
  -- STEP 1: the `w = w₁ ++ w₂` split, via `Fin.appendEquiv`
  have step1 : (Finset.univ.filter (fun p : (Fin Nh → Bool) × (Fin Nh → Bool) =>
        ev (List.ofFn p.1 ++ List.ofFn p.2) = some (val d))).card
      = (Finset.univ.filter (fun b : Fin (Nh + Nh) → Bool =>
          ev (List.ofFn b) = some (val d))).card := by
    refine Finset.card_equiv (Fin.appendEquiv Nh Nh) ?_
    intro p
    have happ : ∀ r : (Fin Nh → Bool) × (Fin Nh → Bool),
        (Fin.appendEquiv Nh Nh) r = Fin.append r.1 r.2 := by
      intro r; funext a; exact Fin.appendEquiv_apply Nh Nh r a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, happ, List.ofFn_fin_append]
  rw [← step1]
  -- STEP 2: on pairs, replay the second forward run backwards as the adjoint pass
  refine Finset.card_nbij'
    (fun q : (Fin Nh → Bool) × (Fin Nh → Bool) =>
      (q.1, asmToFn Nh (Bkk (List.ofFn q.2)).reverse))
    (fun p : (Fin Nh → Bool) × (Fin Nh → Bool) =>
      (p.1, asmToFn Nh (J (Fw (List.ofFn p.1)) (List.ofFn p.2))))
    ?_ ?_ ?_ ?_
  · -- MapsTo: a matched pair becomes an accepting run of the doubled program
    intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    obtain ⟨hout, hsame, hdiff⟩ := hq
    have hofn : List.ofFn (asmToFn Nh (Bkk (List.ofFn q.2)).reverse)
        = (Bkk (List.ofFn q.2)).reverse := asm_ofFn_toFn _ (hlenRev _)
    rw [hofn, hEv _ _ (hlenOfFn _) (hlenRev _)]
    have hadj : adj (Fw (List.ofFn q.1)) (Bkk (List.ofFn q.2)).reverse = true := by
      rw [hsame]; exact hRev _ (hlenOfFn _)
    rw [if_pos ⟨hout, hadj⟩]
    have hneg : Pa (Fw (List.ofFn q.2)) (Bkk (List.ofFn q.2)).reverse
        = - Pf (List.ofFn q.2) := by
      exact eq_neg_of_add_eq_zero_left (hPh (List.ofFn q.2) (hlenOfFn _))
    rw [hsame, hneg, ← sub_eq_add_neg, hdiff]
  · -- MapsTo, the other way
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [hEv _ _ (hlenOfFn _) (hlenOfFn _)] at hp
    by_cases hc : outb (Fw (List.ofFn p.1)) = true
        ∧ adj (Fw (List.ofFn p.1)) (List.ofFn p.2) = true
    · rw [if_pos hc] at hp
      obtain ⟨hout, hadj⟩ := hc
      have hphase : Pf (List.ofFn p.1) + Pa (Fw (List.ofFn p.1)) (List.ofFn p.2) = d :=
        hval (Option.some.inj hp)
      obtain ⟨hFwJ, hBkJ⟩ := hJ (Fw (List.ofFn p.1)) (List.ofFn p.2) (hlenOfFn _) hadj
      have hofn : List.ofFn (asmToFn Nh (J (Fw (List.ofFn p.1)) (List.ofFn p.2)))
          = J (Fw (List.ofFn p.1)) (List.ofFn p.2) := asm_ofFn_toFn _ (hJlen _ _)
      rw [hofn]
      refine ⟨hout, hFwJ.symm, ?_⟩
      have hrr : (Bkk (J (Fw (List.ofFn p.1)) (List.ofFn p.2))).reverse = List.ofFn p.2 := by
        rw [hBkJ, List.reverse_reverse]
      have hneg := hPh (J (Fw (List.ofFn p.1)) (List.ofFn p.2)) (hJlen _ _)
      rw [hFwJ, hrr] at hneg
      have : Pa (Fw (List.ofFn p.1)) (List.ofFn p.2)
          = - Pf (J (Fw (List.ofFn p.1)) (List.ofFn p.2)) :=
        eq_neg_of_add_eq_zero_left hneg
      rw [this, ← sub_eq_add_neg] at hphase
      exact hphase
    · rw [if_neg hc] at hp
      exact absurd hp (by simp)
  · -- LeftInvOn
    intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨hout, hsame, hdiff⟩ := hq
    have hofn : List.ofFn (asmToFn Nh (Bkk (List.ofFn q.2)).reverse)
        = (Bkk (List.ofFn q.2)).reverse := asm_ofFn_toFn _ (hlenRev _)
    have hadj : adj (Fw (List.ofFn q.1)) (Bkk (List.ofFn q.2)).reverse = true := by
      rw [hsame]; exact hRev _ (hlenOfFn _)
    obtain ⟨hFwJ, hBkJ⟩ :=
      hJ (Fw (List.ofFn q.1)) (Bkk (List.ofFn q.2)).reverse (hlenRev _) hadj
    have hkey : J (Fw (List.ofFn q.1)) (Bkk (List.ofFn q.2)).reverse = List.ofFn q.2 := by
      refine hInj _ _ (hJlen _ _) (hlenOfFn _) ?_ ?_
      · rw [hFwJ, hsame]
      · rw [hBkJ, List.reverse_reverse]
    have hgoal : (q.1, asmToFn Nh (J (Fw (List.ofFn q.1))
        (List.ofFn (asmToFn Nh (Bkk (List.ofFn q.2)).reverse)))) = q := by
      rw [hofn, hkey, asm_toFn_ofFn]
    exact hgoal
  · -- RightInvOn
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [hEv _ _ (hlenOfFn _) (hlenOfFn _)] at hp
    by_cases hc : outb (Fw (List.ofFn p.1)) = true
        ∧ adj (Fw (List.ofFn p.1)) (List.ofFn p.2) = true
    · obtain ⟨hout, hadj⟩ := hc
      obtain ⟨hFwJ, hBkJ⟩ := hJ (Fw (List.ofFn p.1)) (List.ofFn p.2) (hlenOfFn _) hadj
      have hofn : List.ofFn (asmToFn Nh (J (Fw (List.ofFn p.1)) (List.ofFn p.2)))
          = J (Fw (List.ofFn p.1)) (List.ofFn p.2) := asm_ofFn_toFn _ (hJlen _ _)
      have hgoal : (p.1, asmToFn Nh (Bkk (List.ofFn
          (asmToFn Nh (J (Fw (List.ofFn p.1)) (List.ofFn p.2))))).reverse) = p := by
        rw [hofn, hBkJ, List.reverse_reverse, asm_toFn_ofFn]
      exact hgoal
    · rw [if_neg hc] at hp
      exact absurd hp (by simp)
  -- NON-VACUITY: the one-Hadamard circuit
  refine ⟨fun u => u.headI, fun _ => [false], fun _ => 0, fun s => s,
    fun _ v => !v.headI, fun _ _ => 0, fun y _ => [y],
    fun w => if w.headI = true ∧ w.tail.headI = false then some 0 else none,
    by decide, fun w => rfl, ?_, ?_, ?_, fun y v => rfl, ?_, ?_, by decide, by decide⟩
  · intro w _
    rfl
  · intro w _
    simp
  · intro w1 w2 h1 h2 hfw _
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h1
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp h2
    simpa using hfw
  · intro y v hv hadj
    refine ⟨rfl, ?_⟩
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hv
    cases b
    · rfl
    · simp at hadj
  · intro u v hu hv
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hu
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hv
    cases a <;> cases b <;> decide

end BQPReferenceValidation.Source9

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate9
    let target ← getConstInfo ``ShiBQP.doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate9
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance; axioms {axioms}"
