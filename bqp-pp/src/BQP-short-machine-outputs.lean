import «BQP-short-machine-prefix»
import «BQP-counting-threshold»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPShortMachine
open Turing Turing.TM2

 theorem second_right (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ b d : Bool)
    (v : State tm) (s : List (tm.Γ tm.k₀)) :
    ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂)
      (some (inputCfg tm (second tm b) v (ea.symm (.inr d) :: s))) =
    some (inputCfg tm (drain tm (if b then c₂ else c₁))
      (v.1, some (ea.symm (.inr d))) s) := by
  simp [ShiTMSubroutine.run, step, inputCfg, second, program, stepAux]

 theorem second_nil (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ b : Bool) (v : State tm) :
    ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂)
      (some (inputCfg tm (second tm b) v [])) =
    some (inputCfg tm (drain tm (if b then c₂ else c₁)) (v.1, none) []) := by
  simp [ShiTMSubroutine.run, step, inputCfg, second, program, stepAux]

/-- Combine a proved finite dispatch with the exact draining run. -/
def outputs_after_drain (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ b : Bool)
    (inp rest : List (tm.Γ tm.k₀)) (v : State tm) (n t : ℕ)
    (hp : (ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂))^[n]
      (some (initList (machine tm ea eb c₀ c₁ c₂) inp)) =
      some (inputCfg tm (drain tm b) v rest))
    (ht : rest.length + 1 + n ≤ t) :
    TM2OutputsInTime (machine tm ea eb c₀ c₁ c₂) inp (some [eb.symm b]) t := by
  refine { steps := rest.length + 1 + n, steps_le_m := ht, evals_in_steps := ?_ }
  change (ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂))^[rest.length + 1 + n] _ = _
  exact (Function.iterate_add_apply (ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂))
    (rest.length + 1) n _).trans
      ((congrArg ((ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂))^[rest.length + 1]) hp).trans
        (drain_run tm ea eb c₀ c₁ c₂ b rest v))

/-- Empty and one-bit instances are decided in linear time in the witness,
with the complete clean-output contract required by Mathlib. -/
def short_outputs (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ : Bool)
    (x w : List Bool) (hx : x.length ≤ 1) :
    TM2OutputsInTime (machine tm ea eb c₀ c₁ c₂)
      ((PvsNP.encodePair (x,w)).map ea.symm)
      (some [eb.symm (BQPCounting.shortChecker c₀ c₁ c₂ (fun _ => false) (x,w))])
      (w.length + 3) := by
  cases x with
  | nil =>
    cases w with
    | nil =>
      exact outputs_after_drain tm ea eb c₀ c₁ c₂ c₀ [] [] (tm.initialState, none)
        1 3 (start_nil tm ea eb c₀ c₁ c₂ _) (by simp)
    | cons d w =>
      apply outputs_after_drain tm ea eb c₀ c₁ c₂ c₀ _
        ((w.map Sum.inr).map ea.symm) (tm.initialState, some (ea.symm (.inr d))) 1
      · have hs := start_cons tm ea eb c₀ c₁ c₂ (tm.initialState, none)
          (ea.symm (.inr d)) ((w.map Sum.inr).map ea.symm)
        simp only [Equiv.apply_symm_apply] at hs
        exact hs
      · simp
  | cons b x =>
    have he : x = [] := by simpa using hx
    subst x
    have hv : BQPCounting.shortChecker c₀ c₁ c₂ (fun _ => false) ([b],w) =
        (if b then c₂ else c₁) := by cases b <;> rfl
    rw [hv]
    cases w with
    | nil =>
      apply outputs_after_drain tm ea eb c₀ c₁ c₂ (if b then c₂ else c₁) _ []
        (tm.initialState, none) 2
      · have hs := start_cons tm ea eb c₀ c₁ c₂ (tm.initialState, none)
          (ea.symm (.inl b)) []
        simp only [Equiv.apply_symm_apply] at hs
        exact (congrArg (ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂)) hs).trans
          (second_nil tm ea eb c₀ c₁ c₂ b _)
      · simp
    | cons d w =>
      apply outputs_after_drain tm ea eb c₀ c₁ c₂ (if b then c₂ else c₁) _
        ((w.map Sum.inr).map ea.symm) (tm.initialState, some (ea.symm (.inr d))) 2
      · have hs := start_cons tm ea eb c₀ c₁ c₂ (tm.initialState, none)
          (ea.symm (.inl b)) (ea.symm (.inr d) :: (w.map Sum.inr).map ea.symm)
        simp only [Equiv.apply_symm_apply] at hs
        exact (congrArg (ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂)) hs).trans
          (second_right tm ea eb c₀ c₁ c₂ b d _ _)
      · simp

/-- On every longer instance, preserve the original computation and add exactly
 two dispatch steps to its run. -/
def long_outputs (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ b d : Bool)
    (s : List (tm.Γ tm.k₀)) (out : List (tm.Γ tm.k₁)) (t : ℕ)
    (h : TM2OutputsInTime tm (ea.symm (.inl b) :: ea.symm (.inl d) :: s)
      (some out) t) :
    TM2OutputsInTime (machine tm ea eb c₀ c₁ c₂)
      (ea.symm (.inl b) :: ea.symm (.inl d) :: s) (some out) (t + 2) := by
  let hd := delegated_outputs tm ea eb c₀ c₁ c₂ _ out t h
  refine {
    steps := h.steps + 2
    steps_le_m := Nat.add_le_add_right h.steps_le_m 2
    evals_in_steps := ?_ }
  change (ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂))^[h.steps + 2] _ = _
  exact (Function.iterate_add_apply (ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂))
    h.steps 2 _).trans
      ((congrArg ((ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂))^[h.steps])
        (long_prefix tm ea eb c₀ c₁ c₂ b d s)).trans hd.evals_in_steps)

/-- The finite short-instance patch is polynomial-time by the actual dispatcher
machine, without assumed Boolean closure operations. -/
theorem shortChecker_polyTime (c₀ c₁ c₂ : Bool) (R : PvsNP.Str × PvsNP.Str → Bool)
    (hR : PvsNP.PolyTimeChecker R) :
    PvsNP.PolyTimeChecker (BQPCounting.shortChecker c₀ c₁ c₂ R) := by
  obtain ⟨M⟩ := hR
  refine ⟨{
    tm := machine M.tm M.inputAlphabet M.outputAlphabet c₀ c₁ c₂
    inputAlphabet := M.inputAlphabet
    outputAlphabet := M.outputAlphabet
    time := M.time + Polynomial.X + Polynomial.C 3
    outputsFun := ?_ }⟩
  intro p
  rcases p with ⟨x,w⟩
  by_cases hx : x.length ≤ 1
  · let h := short_outputs M.tm M.inputAlphabet M.outputAlphabet c₀ c₁ c₂ x w hx
    have he : BQPCounting.shortChecker c₀ c₁ c₂ R (x,w) =
        BQPCounting.shortChecker c₀ c₁ c₂ (fun _ => false) (x,w) := by
      cases x with
      | nil => rfl
      | cons b xs =>
        have hxs : xs = [] := by simpa using hx
        subst xs
        cases b <;> rfl
    simp only [Computability.encodeBool, List.map_cons, List.map_nil, he]
    exact { h with
      steps_le_m := by
        have hb := h.steps_le_m
        simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
          PvsNP.encodePair, List.length_append, List.length_map]
        omega }
  · cases x with
    | nil => simp at hx
    | cons b xs =>
      cases xs with
      | nil => simp at hx
      | cons d xs =>
        have h := long_outputs M.tm M.inputAlphabet M.outputAlphabet c₀ c₁ c₂ b d
          ((PvsNP.encodePair (xs,w)).map M.inputAlphabet.symm)
          ((Computability.encodeBool (R (b::d::xs,w))).map M.outputAlphabet.symm)
          (M.time.eval (PvsNP.encodePair (b::d::xs,w)).length) (M.outputsFun (b::d::xs,w))
        have he : BQPCounting.shortChecker c₀ c₁ c₂ R (b::d::xs,w) = R (b::d::xs,w) := by
          cases b <;> rfl
        simp only [he]
        exact { h with
          steps_le_m := by
            have hb := h.steps_le_m
            simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
            omega }

end BQPShortMachine
