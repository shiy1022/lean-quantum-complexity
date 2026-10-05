import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_ShiTM_initList_haltList_laws
import Theorems.Thm_ShiTM_outputsInTime_of_run_to_halt

namespace BQPReferenceValidation.Source39
/-
HALT-1 : the `initList` -> `haltList` bridge (halting-convention obligation).

From a relative run "`initList tm inp` reaches label `lfin` with stacks `S` in exactly `N`
steps", where `tm.m lfin = halt`, `S tm.k₁ = out` and every other stack of `S` is empty,
we produce the ABSOLUTE certificate `Turing.TM2OutputsInTime tm inp (some out) (N + 1)`
(wrapped in `Nonempty`, since `TM2OutputsInTime` is TYPE-valued).

Three obligations, in the order the definitions impose them:
* `haltList` has label `Option.none`, so one further `step` -- the execution of the
  `halt` statement -- is required; hence the `N + 1`.
* `haltList`'s `stk` field is a `dite`-defined function, so the match is a `funext`
  with a case split on `k = tm.k₁`.
* `haltList`'s `var` field is `tm.initialState`, which is why that value is demanded of
  the reached configuration.

Part (b) is the composite joint: any split run (N steps to an arbitrary intermediate
configuration `c1`, then M steps from `c1` to the halt-ready configuration) also yields
the absolute certificate, in `M + N + 1` steps. This is the shape that consumes the
ACCEPTED `ShiTM.drain_stacks_and_reset_state` conclusion verbatim (see the note at the
bottom of this file).
-/

set_option autoImplicit false

open Turing StateTransition

/-! ### The `dite`/`Eq.mpr` obligation on `haltList`'s stack field -/

/-- The output stack of `haltList tm out` is `out`. This is the positive branch of the
`dite` in the definition of `haltList`, whose `Eq.mpr` cast is reduced by proof
irrelevance (`dif_pos rfl`). -/
private theorem shiHl_halt_stk_pos (tm : Turing.FinTM2) (out : List (tm.Γ tm.k₁)) :
    (Turing.haltList tm out).stk tm.k₁ = out := by
  first
    | exact dif_pos rfl
    | (simp only [Turing.haltList]; rw [dif_pos rfl])
    | exact (ShiTM.initList_haltList_laws tm [] out).2.2.2.2.2.2.1

/-- Every non-output stack of `haltList tm out` is empty: the negative branch of the
`dite`, where no cast is present at all. -/
private theorem shiHl_halt_stk_neg (tm : Turing.FinTM2) (out : List (tm.Γ tm.k₁))
    (k : tm.K) (h : k ≠ tm.k₁) :
    (Turing.haltList tm out).stk k = [] := by
  first
    | exact dif_neg h
    | (simp only [Turing.haltList]; rw [dif_neg h])
    | exact (ShiTM.initList_haltList_laws tm [] out).2.2.2.2.2.2.2 k h

/-- The `funext` obligation: a stack assignment whose `tm.k₁` component is `out` and
whose every other component is `[]` IS the stack field of `haltList tm out`. -/
private theorem shiHl_stk_funext (tm : Turing.FinTM2) (out : List (tm.Γ tm.k₁))
    (S : ∀ k, List (tm.Γ k)) (hout : S tm.k₁ = out)
    (hempty : ∀ k, k ≠ tm.k₁ → S k = []) :
    S = (Turing.haltList tm out).stk := by
  funext k
  by_cases h : k = tm.k₁
  · subst h
    rw [shiHl_halt_stk_pos tm out]
    exact hout
  · rw [shiHl_halt_stk_neg tm out k h]
    exact hempty k h

/-- Consequently the whole configuration matches: `haltList` is pinned down by
label `none`, variable `tm.initialState` and the stack data above (structure eta). -/
private theorem shiHl_cfg_eq (tm : Turing.FinTM2) (out : List (tm.Γ tm.k₁))
    (S : ∀ k, List (tm.Γ k)) (hout : S tm.k₁ = out)
    (hempty : ∀ k, k ≠ tm.k₁ → S k = []) :
    ({ l := Option.none, var := tm.initialState, stk := S } :
        Turing.TM2.Cfg tm.Γ tm.Λ tm.σ)
      = Turing.haltList tm out := by
  rw [shiHl_stk_funext tm out S hout hempty]
  all_goals rfl

/-! ### Executing the `halt` statement: the one extra step -/

/-- One `TM2.step` out of a label whose program is `halt` erases the label (and touches
nothing else). This is the step that `haltList`'s `l = Option.none` forces. -/
private theorem shiHl_step_of_halt (tm : Turing.FinTM2) (l : tm.Λ)
    (hhalt : tm.m l = Turing.TM2.Stmt.halt) (v : tm.σ) (S : ∀ k, List (tm.Γ k)) :
    Turing.TM2.step tm.m
        ({ l := Option.some l, var := v, stk := S } : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ)
      = Option.some
          ({ l := Option.none, var := v, stk := S } :
            Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  have hred : Turing.TM2.step tm.m
      ({ l := Option.some l, var := v, stk := S } : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ)
      = Option.some (Turing.TM2.stepAux (tm.m l) v S) := rfl
  rw [hred, hhalt]
  all_goals rfl

/-! ### The bridge -/

/-- The bridge, as a private core so that both halves of `BQPReferenceValidation.candidate39` can use it. -/
private theorem shiHl_core (tm : Turing.FinTM2) (lfin : tm.Λ)
    (hhalt : tm.m lfin = Turing.TM2.Stmt.halt)
    (inp : List (tm.Γ tm.k₀)) (out : List (tm.Γ tm.k₁)) (N : ℕ)
    (S : ∀ k, List (tm.Γ k))
    (hrun : (fun cf : Option (Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) =>
          cf.bind (Turing.TM2.step tm.m))^[N]
        (Option.some (Turing.initList tm inp))
      = Option.some { l := Option.some lfin, var := tm.initialState, stk := S })
    (hout : S tm.k₁ = out)
    (hempty : ∀ k, k ≠ tm.k₁ → S k = []) :
    Nonempty (Turing.TM2OutputsInTime tm inp (Option.some out) (N + 1)) := by
  have hsucc : (fun cf : Option (Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) =>
        cf.bind (Turing.TM2.step tm.m))^[N + 1]
      (Option.some (Turing.initList tm inp))
      = (Option.some { l := Option.some lfin, var := tm.initialState, stk := S } :
            Option (Turing.TM2.Cfg tm.Γ tm.Λ tm.σ)).bind (Turing.TM2.step tm.m) := by
    rw [Function.iterate_succ_apply', hrun]
    all_goals rfl
  have hb : (Option.some { l := Option.some lfin, var := tm.initialState, stk := S } :
        Option (Turing.TM2.Cfg tm.Γ tm.Λ tm.σ)).bind (Turing.TM2.step tm.m)
      = Turing.TM2.step tm.m
          ({ l := Option.some lfin, var := tm.initialState, stk := S } :
            Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) := rfl
  have hkey : (fun cf : Option (Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) =>
        cf.bind (Turing.TM2.step tm.m))^[N + 1]
      (Option.some (Turing.initList tm inp))
      = Option.some (Turing.haltList tm out) := by
    rw [hsucc, hb, shiHl_step_of_halt tm lfin hhalt tm.initialState S,
      shiHl_cfg_eq tm out S hout hempty]
    all_goals rfl
  exact ⟨⟨⟨N + 1, hkey⟩, le_refl _⟩⟩

/-! ### The public statement -/

/--
HALT-1. The halting-convention bridge for a bundled TM2, in two forms.

Part (a) (the bridge proper): if `initList tm inp` reaches, in exactly `N` steps, the
configuration with label `lfin`, variable `tm.initialState` and stacks `S`, where
`tm.m lfin = halt`, `S tm.k₁ = out` and all other stacks of `S` are empty, then
`Turing.TM2OutputsInTime tm inp (some out) (N + 1)` is inhabited. The `+ 1` is the
execution of the `halt` statement, which is what turns the label into `Option.none`.

Part (b) (the composite joint): the same conclusion from a run split into two phases,
`N` steps to an arbitrary intermediate configuration `c1` and then `M` steps from `c1`
to the halt-ready configuration, with bound `M + N + 1`. Instantiating `c1` with the
entry configuration of a drain/reset phase and the second phase with the conclusion of
the ACCEPTED `ShiTM.drain_stacks_and_reset_state` gives: any run reaching any label with
known scratch contents, followed by drain+reset+halt, yields `TM2OutputsInTime`.
-/
theorem _root_.BQPReferenceValidation.candidate39 (tm : Turing.FinTM2) (inp : List (tm.Γ tm.k₀))
    (out : List (tm.Γ tm.k₁)) :
    (∀ (lfin : tm.Λ) (S : ∀ k, List (tm.Γ k)) (N : ℕ),
        tm.m lfin = Turing.TM2.Stmt.halt →
        (fun cf : Option (Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) =>
              cf.bind (Turing.TM2.step tm.m))^[N]
            (Option.some (Turing.initList tm inp))
          = Option.some { l := Option.some lfin, var := tm.initialState, stk := S } →
        S tm.k₁ = out →
        (∀ k, k ≠ tm.k₁ → S k = []) →
        Nonempty (Turing.TM2OutputsInTime tm inp (Option.some out) (N + 1)))
      ∧ (∀ (lfin : tm.Λ) (c1 : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ)
          (T : ∀ k, List (tm.Γ k)) (N M : ℕ),
        tm.m lfin = Turing.TM2.Stmt.halt →
        (fun cf : Option (Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) =>
              cf.bind (Turing.TM2.step tm.m))^[N]
            (Option.some (Turing.initList tm inp))
          = Option.some c1 →
        (fun cf : Option (Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) =>
              cf.bind (Turing.TM2.step tm.m))^[M] (Option.some c1)
          = Option.some { l := Option.some lfin, var := tm.initialState, stk := T } →
        T tm.k₁ = out →
        (∀ k, k ≠ tm.k₁ → T k = []) →
        Nonempty (Turing.TM2OutputsInTime tm inp (Option.some out) (M + N + 1))) := by
  refine ⟨fun lfin S N hhalt hrun hout hempty => ?_, ?_⟩
  · exact shiHl_core tm lfin hhalt inp out N S hrun hout hempty
  · intro lfin c1 T N M hhalt hrun1 hrun2 hout hempty
    have hjoin : (fun cf : Option (Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) =>
          cf.bind (Turing.TM2.step tm.m))^[M + N]
        (Option.some (Turing.initList tm inp))
        = Option.some { l := Option.some lfin, var := tm.initialState, stk := T } := by
      rw [Function.iterate_add_apply, hrun1, hrun2]
      all_goals rfl
    exact shiHl_core tm lfin hhalt inp out (M + N) T hjoin hout hempty

/-
### Note on composing with `ShiTM.drain_stacks_and_reset_state` (ACCEPTED)

That result's second block concludes, for `cnt = (Σ_{j ∈ ks} len j) + ks.length + 1`,

  (fun cf => cf.bind (Turing.TM2.step M))^[cnt]
      (some { l := some (lbl ks), var := v2, stk := S2 })
    = some { l := some lfin2, var := target2, stk := T2 }

with `T2 j = []` for `j ∈ ks` and `T2 j = S2 j` for `j ∉ ks`. That equation has exactly
the shape of part (b)'s second hypothesis, with `M := tm.m`, `c1 := { l := some (lbl ks),
var := v2, stk := S2 }`, `M := cnt`, `lfin := lfin2`, `T := T2`. Part (b) therefore
consumes it directly, provided the drain phase is instantiated so that:
  * `target2 = tm.initialState`   (`haltList`'s `var` field),
  * `tm.m lfin2 = Turing.TM2.Stmt.halt`  (so that the last step erases the label),
  * `tm.k₁ ∉ ks` and `S2 tm.k₁ = out`   (giving `T2 tm.k₁ = out` from `hT2o`),
  * every `k ≠ tm.k₁` lies in `ks`      (giving `T2 k = []` from `hT2e`),
  * `ks` is `Nodup` -- which is what the drain lemma's suffix hypothesis
    `hfresh : ∀ j u, (j :: u) <:+ ks → j ∉ u` says.
The resulting bound is `cnt + N + 1`. No import of the drain statement is needed for
part (b): it is the joint, stated so that the drain conclusion plugs in as a hypothesis.
-/

-- Diagnostic for the compile operator (uncomment to check no `the empty-proof axiom` crept in via the
-- `first`-fallbacks in `shiHl_halt_stk_pos` / `shiHl_halt_stk_neg`):
-- #print axioms BQPReferenceValidation.candidate39

end BQPReferenceValidation.Source39

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate39
    let target ← getConstInfo ``ShiTM.outputsInTime_of_run_to_halt
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiTM.outputsInTime_of_run_to_halt"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiTM.outputsInTime_of_run_to_halt"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiTM.outputsInTime_of_run_to_halt"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate39
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiTM.outputsInTime_of_run_to_halt; axioms {axioms}"
