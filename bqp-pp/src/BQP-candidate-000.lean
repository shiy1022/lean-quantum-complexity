import Definitions.Def_PvsNP
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_PvsNP_combined_checker_is_polynomial_time_via_the_lossless_pairing

namespace BQPReferenceValidation.Source0

set_option autoImplicit false
set_option maxHeartbeats 1600000

open PvsNP Turing

/-! ### The lossless tagged-to-plain pairing and its decoder -/

private def prSym : Bool ⊕ Bool → List Bool :=
  Sum.elim (fun b => [false, b]) (fun b => [true, b])

private lemma prSym_inl (b : Bool) : prSym (Sum.inl b) = [false, b] := rfl

private lemma prSym_inr (b : Bool) : prSym (Sum.inr b) = [true, b] := rfl

private def prF (p : PvsNP.Str × PvsNP.Str) : PvsNP.Str :=
  (PvsNP.encodePair p).flatMap prSym

private def upF : List Bool → PvsNP.Str × PvsNP.Str
  | [] => ([], [])
  | [_] => ([], [])
  | t :: b :: rest =>
      if t then ((upF rest).1, b :: (upF rest).2)
      else (b :: (upF rest).1, (upF rest).2)

private lemma upF_nil : upF ([] : List Bool) = ([], []) := by
  simp [upF]

private lemma upF_false (b : Bool) (r : List Bool) :
    upF (false :: b :: r) = (b :: (upF r).1, (upF r).2) := by
  simp [upF]

private lemma upF_true (b : Bool) (r : List Bool) :
    upF (true :: b :: r) = ((upF r).1, b :: (upF r).2) := by
  simp [upF]

private lemma fmMapInl (x : PvsNP.Str) :
    (x.map Sum.inl).flatMap prSym = x.flatMap (fun b => [false, b]) := by
  induction x with
  | nil => simp
  | cons b t ih => simp [List.flatMap_cons, prSym_inl, prSym_inr, ih]

private lemma fmMapInr (y : PvsNP.Str) :
    (y.map Sum.inr).flatMap prSym = y.flatMap (fun b => [true, b]) := by
  induction y with
  | nil => simp
  | cons b t ih => simp [List.flatMap_cons, prSym_inl, prSym_inr, ih]

private lemma prEq (x y : PvsNP.Str) :
    prF (x, y) = x.flatMap (fun b => [false, b]) ++ y.flatMap (fun b => [true, b]) := by
  show ((x.map Sum.inl ++ y.map Sum.inr).flatMap prSym) = _
  rw [List.flatMap_append, fmMapInl, fmMapInr]

private lemma upLeft (x : PvsNP.Str) : ∀ z : List Bool,
    upF (x.flatMap (fun b => [false, b]) ++ z) = (x ++ (upF z).1, (upF z).2) := by
  induction x with
  | nil => intro z; simp
  | cons b t ih =>
      intro z
      have e : (b :: t).flatMap (fun c => [false, c]) ++ z
          = false :: b :: (t.flatMap (fun c => [false, c]) ++ z) := by simp
      rw [e, upF_false, ih]
      simp

private lemma upRight (y : PvsNP.Str) : ∀ z : List Bool,
    upF (y.flatMap (fun b => [true, b]) ++ z) = ((upF z).1, y ++ (upF z).2) := by
  induction y with
  | nil => intro z; simp
  | cons b t ih =>
      intro z
      have e : (b :: t).flatMap (fun c => [true, c]) ++ z
          = true :: b :: (t.flatMap (fun c => [true, c]) ++ z) := by simp
      rw [e, upF_true, ih]
      simp

private lemma upPr (p : PvsNP.Str × PvsNP.Str) : upF (prF p) = p := by
  obtain ⟨x, y⟩ := p
  have h1 : prF (x, y)
      = x.flatMap (fun b => [false, b]) ++ (y.flatMap (fun b => [true, b]) ++ []) := by
    rw [prEq]; simp
  rw [h1, upLeft, upRight, upF_nil]
  simp

private lemma fmPrLen (l : List (Bool ⊕ Bool)) :
    (l.flatMap prSym).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons c t ih =>
      have hc : (prSym c).length = 2 := by cases c <;> simp [prSym_inl, prSym_inr]
      simp only [List.flatMap_cons, List.length_append, List.length_cons, hc, ih]
      omega

private lemma fmLenLe {Go : Type} (φ : Bool ⊕ Bool → List Go) (M : ℕ)
    (hM : ∀ c, (φ c).length ≤ M) (l : List (Bool ⊕ Bool)) :
    (l.flatMap φ).length ≤ M * l.length := by
  induction l with
  | nil => simp
  | cons c t ih =>
      have h1 : (φ c).length ≤ M := hM c
      have h2 : M * (t.length + 1) = M * t.length + M := by ring
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega

/-!
### `PolyTimeChecker` content of a combined checker `Rf`, hypothesis-style

The two hypotheses `hT1`, `hB7` are conjunct (1) of the ACCEPTED
`PvsNP.tagged_transducers_untaggers_and_projections` and conjunct (7) of the ACCEPTED
`PvsNP.polyTime_composition_and_alphabet_transport`; `hB5` is conjunct (5) of the latter.
Nothing about `Rf` is assumed beyond a defining equation.
-/

theorem _root_.BQPReferenceValidation.candidate0
    (hT1 : ∀ (Go : Type) [Inhabited Go] [Fintype Go] (φ : Bool ⊕ Bool → List Go) (M : ℕ),
        (∀ c, (φ c).length ≤ M) →
        ∀ (β : Type) (eb : β → List Go) (f : PvsNP.Str × PvsNP.Str → β),
          (∀ p, eb (f p) = (PvsNP.encodePair p).flatMap φ) →
          ∃ c : Turing.TM2ComputableInPolyTime PvsNP.encodePair eb f,
            c.time = Polynomial.C (M + 1) * Polynomial.X + Polynomial.C 3)
    (hB5 : ∀ (χ : PvsNP.Str → Bool) (g : PvsNP.Str → PvsNP.Str),
        PvsNP.PolyTimeDecider χ → PvsNP.PolyTimeComputable g →
        PvsNP.PolyTimeDecider (fun w : PvsNP.Str => χ (g w)))
    (hB7 : ∀ (u : PvsNP.Str × PvsNP.Str → PvsNP.Str) (χ : PvsNP.Str → Bool)
        (q : Polynomial ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair
          (id : PvsNP.Str → PvsNP.Str) u) →
        PvsNP.PolyTimeDecider χ →
        (∀ p : PvsNP.Str × PvsNP.Str,
          (u p).length ≤ q.eval (PvsNP.encodePair p).length) →
        PvsNP.PolyTimeChecker (fun p : PvsNP.Str × PvsNP.Str => χ (u p))) :
    ∃ (pr : PvsNP.Str × PvsNP.Str → PvsNP.Str)
      (up : PvsNP.Str → PvsNP.Str × PvsNP.Str),
    -- (0) `pr` IS the lossless pairing of TRANSDUCE-2 conjunct (5)
    (∀ p : PvsNP.Str × PvsNP.Str, pr p = (PvsNP.encodePair p).flatMap
        (Sum.elim (fun b => [false, b]) (fun b => [true, b])))
    -- (1) it loses nothing: `up` decodes it
  ∧ (∀ p : PvsNP.Str × PvsNP.Str, up (pr p) = p)
    -- (2) hence it is injective
  ∧ (∀ p q : PvsNP.Str × PvsNP.Str, pr p = pr q → p = q)
    -- (3) and exactly doubles length, so the composition bound holds at `q = C 2 * X`
  ∧ (∀ p : PvsNP.Str × PvsNP.Str, (pr p).length = 2 * (PvsNP.encodePair p).length)
    -- (4) THE GENERAL BRIDGE.  Any bounded-fan-out symbolwise re-encoding of the tagged
    -- pair into a plain string, followed by ANY polynomial-time plain-string decision
    -- procedure, is a polynomial-time checking relation.  No length hypothesis is left
    -- for the consumer: it is discharged here at `q = C M * X`.
  ∧ (∀ (φ : Bool ⊕ Bool → List Bool) (M : ℕ), (∀ c, (φ c).length ≤ M) →
        ∀ (χ : PvsNP.Str → Bool) (Rf : PvsNP.Str × PvsNP.Str → Bool),
          PvsNP.PolyTimeDecider χ →
          (∀ p : PvsNP.Str × PvsNP.Str, Rf p = χ ((PvsNP.encodePair p).flatMap φ)) →
          PvsNP.PolyTimeChecker Rf)
    -- (5) THE INSTANCE AT THE LOSSLESS PAIRING
  ∧ (∀ (χ : PvsNP.Str → Bool) (Rf : PvsNP.Str × PvsNP.Str → Bool),
        PvsNP.PolyTimeDecider χ →
        (∀ p : PvsNP.Str × PvsNP.Str, Rf p = χ (pr p)) →
        PvsNP.PolyTimeChecker Rf)
    -- (6) (5)'s SHAPE HYPOTHESIS IS NO RESTRICTION: every relation whatever factors
    -- through `pr`, so the only real content of (5) is `PolyTimeDecider χ`.
  ∧ (∀ Rf : PvsNP.Str × PvsNP.Str → Bool,
        ∃ χ : PvsNP.Str → Bool, ∀ p : PvsNP.Str × PvsNP.Str, Rf p = χ (pr p))
    -- (7) THE ROUTER FORM: the decision procedure may be preceded by any polynomial-time
    -- plain-string function `g`.  This is the form a DISPATCHING `Rf` takes.
  ∧ (∀ (Rf : PvsNP.Str × PvsNP.Str → Bool) (chi : PvsNP.Str → Bool)
        (g : PvsNP.Str → PvsNP.Str),
        PvsNP.PolyTimeDecider chi → PvsNP.PolyTimeComputable g →
        (∀ p : PvsNP.Str × PvsNP.Str, Rf p = chi (g (pr p))) →
        PvsNP.PolyTimeChecker Rf)
    -- (8) FINITELY-MANY-ARM DISPATCH, with the semantic read-off: a selector `sel` reads a
    -- number off the paired string and `arm` chooses the argument handed to `chi`.
  ∧ (∀ (Rf : PvsNP.Str × PvsNP.Str → Bool) (chi : PvsNP.Str → Bool)
        (sel : PvsNP.Str → ℕ) (arm : ℕ → PvsNP.Str → PvsNP.Str)
        (g : PvsNP.Str → PvsNP.Str),
        PvsNP.PolyTimeDecider chi → PvsNP.PolyTimeComputable g →
        (∀ w : PvsNP.Str, g w = arm (sel w) w) →
        (∀ p : PvsNP.Str × PvsNP.Str, Rf p = chi (g (pr p))) →
        PvsNP.PolyTimeChecker Rf
          ∧ ∀ p : PvsNP.Str × PvsNP.Str, Rf p = chi (arm (sel (pr p)) (pr p)))
    -- (9) THE TWO-ARM INTEGER-COMPARISON DISPATCH in the shape the campaign needs: on the
    -- cases selected by `selB` the combined checker IS the component `chi ∘ cut`, and on
    -- the remaining cases it is the constant gadget `chi w0`.
  ∧ (∀ (Rf : PvsNP.Str × PvsNP.Str → Bool) (chi : PvsNP.Str → Bool)
        (selB : PvsNP.Str → Bool) (cut : PvsNP.Str → PvsNP.Str) (w0 : PvsNP.Str)
        (g : PvsNP.Str → PvsNP.Str),
        PvsNP.PolyTimeDecider chi → PvsNP.PolyTimeComputable g →
        (∀ w : PvsNP.Str, g w = if selB w then cut w else w0) →
        (∀ p : PvsNP.Str × PvsNP.Str, Rf p = chi (g (pr p))) →
        PvsNP.PolyTimeChecker Rf
          ∧ (∀ p : PvsNP.Str × PvsNP.Str, selB (pr p) = true → Rf p = chi (cut (pr p)))
          ∧ (∀ p : PvsNP.Str × PvsNP.Str, selB (pr p) = false → Rf p = chi w0))
    -- (10) NON-VACUITY: the pairing and its decoder at a concrete pair, matching the value
    -- recorded in TRANSDUCE-2 conjunct (5).
  ∧ pr ([true], [false]) = [false, true, true, false]
  ∧ up [false, true, true, false] = ([true], [false]) := by
  have bridge : ∀ (φ : Bool ⊕ Bool → List Bool) (M : ℕ), (∀ c, (φ c).length ≤ M) →
      ∀ (χ : PvsNP.Str → Bool) (Rf : PvsNP.Str × PvsNP.Str → Bool),
        PvsNP.PolyTimeDecider χ →
        (∀ p : PvsNP.Str × PvsNP.Str, Rf p = χ ((PvsNP.encodePair p).flatMap φ)) →
        PvsNP.PolyTimeChecker Rf := by
    intro φ M hM χ Rf hχ hRf
    obtain ⟨c, -⟩ := hT1 Bool φ M hM PvsNP.Str (id : PvsNP.Str → PvsNP.Str)
      (fun p => (PvsNP.encodePair p).flatMap φ) (fun p => rfl)
    have hlen : ∀ p : PvsNP.Str × PvsNP.Str,
        ((PvsNP.encodePair p).flatMap φ).length
          ≤ (Polynomial.C M * Polynomial.X : Polynomial ℕ).eval
              (PvsNP.encodePair p).length := by
      intro p
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      exact fmLenLe φ M hM (PvsNP.encodePair p)
    have key := hB7 (fun p => (PvsNP.encodePair p).flatMap φ) χ
      (Polynomial.C M * Polynomial.X) ⟨c⟩ hχ hlen
    have e : Rf = fun p : PvsNP.Str × PvsNP.Str => χ ((PvsNP.encodePair p).flatMap φ) :=
      funext hRf
    rw [e]
    exact key
  have hsym : ∀ c : Bool ⊕ Bool, (prSym c).length ≤ 2 := by
    intro c; cases c <;> simp [prSym_inl, prSym_inr]
  have pairInst : ∀ (χ : PvsNP.Str → Bool) (Rf : PvsNP.Str × PvsNP.Str → Bool),
      PvsNP.PolyTimeDecider χ →
      (∀ p : PvsNP.Str × PvsNP.Str, Rf p = χ (prF p)) →
      PvsNP.PolyTimeChecker Rf := by
    intro χ Rf hχ hRf
    exact bridge prSym 2 hsym χ Rf hχ hRf
  have router : ∀ (Rf : PvsNP.Str × PvsNP.Str → Bool) (chi : PvsNP.Str → Bool)
      (g : PvsNP.Str → PvsNP.Str),
      PvsNP.PolyTimeDecider chi → PvsNP.PolyTimeComputable g →
      (∀ p : PvsNP.Str × PvsNP.Str, Rf p = chi (g (prF p))) →
      PvsNP.PolyTimeChecker Rf := by
    intro Rf chi g hchi hg hRf
    exact pairInst (fun w : PvsNP.Str => chi (g w)) Rf (hB5 chi g hchi hg) hRf
  refine ⟨prF, upF, fun p => rfl, upPr, ?_, ?_, bridge, pairInst, ?_, router, ?_, ?_,
    rfl, ?_⟩
  · intro p q h
    have hp : upF (prF p) = p := upPr p
    rw [h, upPr] at hp
    exact hp.symm
  · intro p
    show ((PvsNP.encodePair p).flatMap prSym).length = 2 * (PvsNP.encodePair p).length
    exact fmPrLen (PvsNP.encodePair p)
  · intro Rf
    refine ⟨fun w => Rf (upF w), ?_⟩
    intro p
    show Rf p = Rf (upF (prF p))
    rw [upPr]
  · intro Rf chi sel arm g hchi hg harm hRf
    refine ⟨router Rf chi g hchi hg hRf, ?_⟩
    intro p
    rw [hRf p, harm (prF p)]
  · intro Rf chi selB cut w0 g hchi hg harm hRf
    refine ⟨router Rf chi g hchi hg hRf, ?_, ?_⟩
    · intro p hp
      rw [hRf p, harm (prF p)]
      simp [hp]
    · intro p hp
      rw [hRf p, harm (prF p)]
      simp [hp]
  · simp [upF]

end BQPReferenceValidation.Source0

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate0
    let target ← getConstInfo ``PvsNP.combined_checker_is_polynomial_time_via_the_lossless_pairing
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: PvsNP.combined_checker_is_polynomial_time_via_the_lossless_pairing"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: PvsNP.combined_checker_is_polynomial_time_via_the_lossless_pairing"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: PvsNP.combined_checker_is_polynomial_time_via_the_lossless_pairing"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate0
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED PvsNP.combined_checker_is_polynomial_time_via_the_lossless_pairing; axioms {axioms}"
