import Definitions.Def_PvsNP
import Definitions.Def_ShiTM2_Composite
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_PvsNP_polyTimeComputable_comp
import Theorems.Thm_ShiBQP_polyBound_three_phase_compose
import Theorems.Thm_ShiTM_comp_outputsInTime
import Theorems.Thm_ShiTM_exists_stepAux_stack_growth_bound
import Theorems.Thm_ShiTM_outputLength_le_of_outputsInTime

namespace BQPReferenceValidation.Source1

set_option autoImplicit false
set_option maxHeartbeats 1000000

open PvsNP

-- `Turing.FinTM2` is a plain structure: its `Fintype` fields are instance-implicit but are not
-- registered globally.  (`Turing.FinTM2.decidableEqK` IS a global instance, so `kDecidableEq`
-- must NOT be added here: doing so would change which `DecidableEq tm.K` term instance search
-- returns, and `Thm_ShiTM_outputLength_le_of_outputsInTime` states its stack-growth hypothesis
-- using the global one.)
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin

/-- Weakening the step bound of a `Turing.TM2OutputsInTime`.  Mathlib has
`TM2OutputsInTime.toTM2Outputs` (forget the bound entirely) but not monotonicity in the bound.
`Turing.TM2OutputsInTime` is a `def` for the `Type`-valued structure
`StateTransition.EvalsToInTime`, so the hypothesis has to be ascribed before its fields resolve;
and the result is data, hence `def` rather than `theorem`. -/
private def shiPoly_outputsInTime_mono {tm : Turing.FinTM2}
    {l : List (tm.Γ tm.k₀)} {l' : Option (List (tm.Γ tm.k₁))} {m m' : ℕ}
    (hle : m ≤ m') (h : Turing.TM2OutputsInTime tm l l' m) :
    Turing.TM2OutputsInTime tm l l' m' := by
  have h' : StateTransition.EvalsToInTime tm.step (Turing.initList tm l)
      ((Option.map (Turing.haltList tm)) l') m := h
  first
  | exact { steps := h'.steps, evals_in_steps := h'.evals_in_steps,
            steps_le_m := le_trans h'.steps_le_m hle }
  | exact ⟨h'.toEvalsTo, le_trans h'.steps_le_m hle⟩
  | exact ⟨h'.steps, h'.evals_in_steps, le_trans h'.steps_le_m hle⟩

/-- **Composition of polynomial-time computable string functions.**

The machine is `ShiTM2.comp C₁.tm C₂.tm tr dflt` with
`tr = fun x => C₂.inputAlphabet.symm (C₁.outputAlphabet x)` (decode a `tm₁` output symbol to
`Bool`, re-encode it as a `tm₂` input symbol) and `dflt = C₂.inputAlphabet.symm false` (the dummy
symbol forced by the totality of `Turing.TM2.Stmt.push`; harmless because `Bool` is inhabited).

The single time polynomial `q` is obtained BEFORE `a` is introduced: `time` is one field of
`Turing.TM2ComputableInPolyTime`, so it must be uniform in the input. -/
theorem _root_.BQPReferenceValidation.candidate1 (f g : Str → Str)
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (g ∘ f) := by
  -- `PolyTimeComputable` is a `def` for a `Nonempty`; ascribe before destructuring.  The goal is
  -- a `Prop`, so eliminating `Nonempty`/`Exists` here is legal.
  have hf' : Nonempty (Turing.TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) f) := hf
  have hg' : Nonempty (Turing.TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) g) := hg
  obtain ⟨C₁⟩ := hf'
  obtain ⟨C₂⟩ := hg'
  -- `DecidableEq (CompK ..)` cannot be synthesised: `tm.kDecidableEq` is a field, not an instance
  -- on `CompK`'s summands in the needed shape.  Supply the definitional one.
  letI instDK : DecidableEq (ShiTM2.CompK C₁.tm C₂.tm) := ShiTM2.compKDecEq C₁.tm C₂.tm
  -- Per-step stack growth constant for the first machine.
  obtain ⟨c, hc⟩ := ShiTM.exists_stepAux_stack_growth_bound C₁.tm.m
  -- The time polynomial, chosen ONCE, outside `∀ a`.
  obtain ⟨q, hq⟩ := ShiBQP.polyBound_three_phase_compose C₁.time C₂.time c 2
  -- `tr ∘ C₁.outputAlphabet.invFun = C₂.inputAlphabet.invFun`: decode-then-encode.
  have hfun : ((fun x => C₂.inputAlphabet.symm (C₁.outputAlphabet x)) ∘
        (C₁.outputAlphabet.invFun : Bool → C₁.tm.Γ C₁.tm.k₁))
      = (C₂.inputAlphabet.invFun : Bool → C₂.tm.Γ C₂.tm.k₀) := by
    funext b
    first
    | (simp; done)
    | (simp only [Function.comp_apply, Equiv.invFun_as_coe, Equiv.apply_symm_apply]; done)
    | (simp [Equiv.invFun_as_coe, Equiv.apply_symm_apply, Equiv.symm_apply_apply]; done)
  -- The key rewrite: `tm₁`'s output tape, translated, IS `tm₂`'s input tape.
  have hmap : ∀ a : Str,
      List.map (fun x => C₂.inputAlphabet.symm (C₁.outputAlphabet x))
          (List.map (C₁.outputAlphabet.invFun) (f a))
        = List.map (C₂.inputAlphabet.invFun) (f a) := by
    intro a
    first
    | (rw [List.map_map, hfun]; done)
    | (simp only [List.map_map, hfun]; done)
    | (rw [List.map_map]; exact congrFun (congrArg List.map hfun) (f a))
  -- Phase 1 output length bound feeding the polynomial bound.
  have hbound : ∀ a : Str,
      Polynomial.eval a.length C₁.time
          + (2 * (List.map (C₁.outputAlphabet.invFun) (f a)).length + 2)
          + Polynomial.eval (f a).length C₂.time
        ≤ Polynomial.eval a.length q := by
    intro a
    have hlen := ShiTM.outputLength_le_of_outputsInTime c hc
      (List.map (C₁.inputAlphabet.invFun) a) (List.map (C₁.outputAlphabet.invFun) (f a))
      (Polynomial.eval a.length C₁.time) (C₁.outputsFun a)
    first
    | simp only [List.length_map] at hlen
    | rw [List.length_map, List.length_map] at hlen
    first
    | simp only [List.length_map]
    | rw [List.length_map]
    exact hq a.length (f a).length hlen
  -- `C₂.outputsFun (f a)`, transported along `hmap`, is the second hypothesis of the composition
  -- theorem.  Stated as a `∀`-indexed family of DATA, so no `obtain` is used on it.
  have h₂ : ∀ a : Str, Turing.TM2OutputsInTime C₂.tm
      (List.map (fun x => C₂.inputAlphabet.symm (C₁.outputAlphabet x))
        (List.map (C₁.outputAlphabet.invFun) (f a)))
      (Option.some (List.map (C₂.outputAlphabet.invFun) (g (f a))))
      (Polynomial.eval (f a).length C₂.time) := by
    intro a
    first
    | (rw [hmap a]; exact C₂.outputsFun (f a))
    | exact (hmap a).symm ▸ C₂.outputsFun (f a)
    | exact (hmap a) ▸ C₂.outputsFun (f a)
  -- Assemble.  `compInputAlphabet : (comp ..).Γ (comp ..).k₀ ≃ tm₁.Γ tm₁.k₀`, so `.trans`
  -- with `C₁.inputAlphabet : tm₁.Γ tm₁.k₀ ≃ Bool` lands in `Bool`; dually on the output side.
  refine ⟨{ tm := ShiTM2.comp C₁.tm C₂.tm
              (fun x => C₂.inputAlphabet.symm (C₁.outputAlphabet x))
              (C₂.inputAlphabet.symm false)
            inputAlphabet := (ShiTM2.compInputAlphabet C₁.tm C₂.tm
              (fun x => C₂.inputAlphabet.symm (C₁.outputAlphabet x))
              (C₂.inputAlphabet.symm false)).trans C₁.inputAlphabet
            outputAlphabet := (ShiTM2.compOutputAlphabet C₁.tm C₂.tm
              (fun x => C₂.inputAlphabet.symm (C₁.outputAlphabet x))
              (C₂.inputAlphabet.symm false)).trans C₂.outputAlphabet
            time := q
            outputsFun := ?_ }⟩
  intro a
  -- `comp_outputsInTime` delivers a `Nonempty`; the field needs data, so use `Nonempty.some`
  -- (noncomputable, but the ambient goal is a `Prop`).
  exact shiPoly_outputsInTime_mono (hbound a)
    (ShiTM.comp_outputsInTime C₁.tm C₂.tm
      (fun x => C₂.inputAlphabet.symm (C₁.outputAlphabet x))
      (C₂.inputAlphabet.symm false)
      (List.map (C₁.inputAlphabet.invFun) a)
      (List.map (C₁.outputAlphabet.invFun) (f a))
      (List.map (C₂.outputAlphabet.invFun) (g (f a)))
      (Polynomial.eval a.length C₁.time) (Polynomial.eval (f a).length C₂.time)
      (C₁.outputsFun a) (h₂ a)).some

end BQPReferenceValidation.Source1

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate1
    let target ← getConstInfo ``PvsNP.polyTimeComputable_comp
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: PvsNP.polyTimeComputable_comp"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: PvsNP.polyTimeComputable_comp"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: PvsNP.polyTimeComputable_comp"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate1
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED PvsNP.polyTimeComputable_comp; axioms {axioms}"
