import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Flatten
import Theorems.Thm_ShiBQP_string_level_compiler_output_budget_for_any_parser_pair

namespace BQPReferenceValidation.Source20
/-
PAIRDECd.  THE STRING-LEVEL COMPILER'S OUTPUT BUDGET, ∀-GENERIC IN THE PARSER PAIR.

WHAT THIS REPAIRS.  `COMPILE-STRd` (7) -- the output-length budget that the
`PolyTimeComputable` bridge needs in order to eliminate the output length from a machine's
affine step bound -- is stated over the `unpack` and `pl` that are EXISTENTIALLY BOUND IN THE
SAME `∃` as the conjunct itself.  Its sibling conjuncts (1) and (3) do pin the two budgets
those functions must obey, but a consumer holding its OWN concrete parser cannot reach (7):
instantiating an existential at one's own witness is not a thing one can do.  This is the same
defect as `COMPMACHe` (15), and the same fix applies -- the one `COMPMACHf` (9) already uses:
∀-quantify the functions and take the budgets as explicit hypotheses.

CONJUNCT (1) IS `COMPILE-STRd` (7) VERBATIM, with `unpack` and `pl` universally quantified and
`COMPILE-STRd` (1) and (3) -- the field budget and the gate-parser budget -- as hypotheses.
Those two are the only properties of the parser the bound uses; everything else in the bound is
already generic in `enc`, `L`, `E` and the two renderers.  A consumer discharges the two budget
hypotheses for its own parser and gets `|output| ≤ 56 * (|s| + |x| + 1)` on the nose.

CONJUNCT (2) IS NON-VACUITY: a concrete fuelled parser pair obeying both budget hypotheses,
with a computed value that is not the trivial one, so (1) is not satisfied only by degenerate
parsers.  Nothing here imports any `Definitions/Def_*` (gotcha 332).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

private def unpackD : List Bool → List ℕ
  | [] => []
  | false :: r => 0 :: unpackD r
  | true :: r => match unpackD r with
                 | [] => []
                 | k :: ks => (k + 1) :: ks

private def arityD (t : ℕ) : ℕ := if t = 4 then 2 else 1

private def pgD : ℕ → List ℕ → List (List ℕ) × List ℕ
  | 0, ts => ([], ts)
  | _ + 1, [] => ([], [])
  | k + 1, t :: ts =>
      if arityD t ≤ ts.length then
        ((t :: ts.take (arityD t)) :: (pgD k (ts.drop (arityD t))).1,
          (pgD k (ts.drop (arityD t))).2)
      else ([], [])

private def plD : ℕ → List ℕ → List (List ℕ) × List ℕ
  | 0, ts => ([], ts)
  | _ + 1, [] => ([], [])
  | k + 1, l :: ts => ((pgD l ts).1 ++ (plD k (pgD l ts).2).1, (plD k (pgD l ts).2).2)

private lemma unpack_budget (s : List Bool) :
    (unpackD s).sum + (unpackD s).length ≤ s.length := by
  induction s with
  | nil => simp [unpackD]
  | cons b r ih =>
      cases b with
      | false => simp only [unpackD, List.sum_cons, List.length_cons]; omega
      | true =>
          show (match unpackD r with
                | [] => ([] : List ℕ)
                | k :: ks => (k + 1) :: ks).sum
              + (match unpackD r with
                 | [] => ([] : List ℕ)
                 | k :: ks => (k + 1) :: ks).length ≤ r.length + 1
          cases hu : unpackD r with
          | nil => simp
          | cons k ks =>
              rw [hu] at ih
              simp only [List.sum_cons, List.length_cons] at ih ⊢
              omega

private lemma sum_take_drop (a : ℕ) (l : List ℕ) :
    (l.take a).sum + (l.drop a).sum = l.sum := by
  rw [← List.sum_append, List.take_append_drop]

private lemma len_take_drop (a : ℕ) (l : List ℕ) :
    (l.take a).length + (l.drop a).length = l.length := by
  rw [← List.length_append, List.take_append_drop]

private lemma pg_budget (k : ℕ) (ts : List ℕ) :
    ((pgD k ts).1.map List.sum).sum + ((pgD k ts).1.map List.length).sum
        + ((pgD k ts).2).sum + ((pgD k ts).2).length ≤ ts.sum + ts.length := by
  induction k generalizing ts with
  | zero => simp [pgD]
  | succ k ih =>
      cases ts with
      | nil => simp [pgD]
      | cons t rest =>
          rw [pgD]
          by_cases hc : arityD t ≤ rest.length
          · rw [if_pos hc]
            have h1 := ih (rest.drop (arityD t))
            have h2 := sum_take_drop (arityD t) rest
            have h3 := len_take_drop (arityD t) rest
            simp only [List.map_cons, List.sum_cons, List.length_cons]
            have h4 : (rest.take (arityD t)).sum ≤ rest.sum := by omega
            omega
          · rw [if_neg hc]; simp

private lemma pl_budget (k : ℕ) (ts : List ℕ) :
    ((plD k ts).1.map List.sum).sum + ((plD k ts).1.map List.length).sum
      ≤ ts.sum + ts.length := by
  induction k generalizing ts with
  | zero => simp [plD]
  | succ k ih =>
      cases ts with
      | nil => simp [plD]
      | cons l rest =>
          rw [plD]
          have h1 := pg_budget l rest
          have h2 := ih (pgD l rest).2
          simp only [List.map_append, List.sum_append, List.length_cons, List.sum_cons]
          omega

private lemma render_len (r : List ℕ → List ℕ)
    (hr : ∀ d : List ℕ, (r d).length ≤ 2 * (d.sum + d.length)) (gs : List (List ℕ)) :
    ((gs.map r).flatten).length
      ≤ 2 * ((gs.map List.sum).sum + (gs.map List.length).sum) := by
  induction gs with
  | nil => simp
  | cons d ds ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.sum_cons]
      have := hr d
      omega

theorem _root_.BQPReferenceValidation.candidate20 :
    -- (1) `COMPILE-STRd` (7), ∀-QUANTIFIED IN THE PARSER PAIR under its own conjuncts (1) and
    -- (3) as explicit hypotheses.  Those two budgets are the only properties of `unpack` and
    -- `pl` the bound uses, so any consumer's concrete parser reaches the conclusion.
    (∀ (unpack : List Bool → List ℕ) (pl : ℕ → List ℕ → List (List ℕ) × List ℕ)
        (enc : List ℕ → List Bool) (L E : List Bool → List ℕ)
        (r rA : List ℕ → List ℕ) (s x : List Bool) (anc out nl : ℕ) (rest : List ℕ),
      (∀ w : List Bool, (unpack w).sum + (unpack w).length ≤ w.length) →
      (∀ (k : ℕ) (ts : List ℕ),
        ((pl k ts).1.map List.sum).sum + ((pl k ts).1.map List.length).sum
          ≤ ts.sum + ts.length) →
      (∀ P : List ℕ, (enc P).length = 4 * P.length) →
      (∀ l : List Bool, (L l).length ≤ 2 * l.length) →
      (∀ l : List Bool, (E l).length ≤ 4 * l.length) →
      (∀ d : List ℕ, (r d).length ≤ 2 * (d.sum + d.length)) →
      (∀ d : List ℕ, (rA d).length ≤ 2 * (d.sum + d.length)) →
      unpack s = anc :: out :: nl :: rest →
      (enc (L (x ++ List.replicate (anc + 1) false)
          ++ (List.replicate (x.length + (anc + 1)) 0
          ++ ((((pl nl rest).1).map r).flatten
          ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
          ++ (((((pl nl rest).1).reverse).map rA).flatten
          ++ (E (x ++ List.replicate (anc + 1) false)
            ++ List.replicate (x.length + (anc + 1)) 0))))))).length
        ≤ 56 * (s.length + x.length + 1))
    -- (2) NON-VACUITY: a concrete fuelled parser pair meeting both budget hypotheses, with a
    -- computed value that is not the degenerate one.
    ∧ (∃ (unpack : List Bool → List ℕ) (pl : ℕ → List ℕ → List (List ℕ) × List ℕ),
        (∀ w : List Bool, (unpack w).sum + (unpack w).length ≤ w.length)
      ∧ (∀ (k : ℕ) (ts : List ℕ),
          ((pl k ts).1.map List.sum).sum + ((pl k ts).1.map List.length).sum
            ≤ ts.sum + ts.length)
      ∧ unpack [true, true, false, true, false] = [2, 1]
      ∧ (unpack [true, true, false, true, false]).sum
          + (unpack [true, true, false, true, false]).length = 5) := by
  refine ⟨?_, ⟨unpackD, plD, unpack_budget, pl_budget, by decide, by decide⟩⟩
  intro unpack pl enc L E r rA s x anc out nl rest hunp hplb henc hL hE hr hrA hs
  rw [henc]
  have hb := hunp s
  rw [hs] at hb
  simp only [List.sum_cons, List.length_cons] at hb
  have hpl := hplb nl rest
  have hfwd := render_len r hr (pl nl rest).1
  have hadj := render_len rA hrA ((pl nl rest).1).reverse
  have hrev1 : (((pl nl rest).1).reverse.map List.sum).sum
      = ((pl nl rest).1.map List.sum).sum := by
    simp
  have hrev2 : (((pl nl rest).1).reverse.map List.length).sum
      = ((pl nl rest).1.map List.length).sum := by
    simp
  rw [hrev1, hrev2] at hadj
  have hLw := hL (x ++ List.replicate (anc + 1) false)
  have hEw := hE (x ++ List.replicate (anc + 1) false)
  simp only [List.length_append, List.length_replicate] at hLw hEw
  simp only [List.length_append, List.length_cons, List.length_replicate,
    List.length_nil]
  omega

end BQPReferenceValidation.Source20

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate20
    let target ← getConstInfo ``ShiBQP.string_level_compiler_output_budget_for_any_parser_pair
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.string_level_compiler_output_budget_for_any_parser_pair"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.string_level_compiler_output_budget_for_any_parser_pair"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.string_level_compiler_output_budget_for_any_parser_pair"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate20
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.string_level_compiler_output_budget_for_any_parser_pair; axioms {axioms}"
