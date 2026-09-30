import «AMPUNI-output-entry-nested-lift»
import «AMPUNI-output-entry-stack-split»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOuterLift

/-- Every run through the lifted nested circuit parser frames all four retained
header stacks, independently of its length or final parser label. -/
theorem nested_run_preserves_header (l : OuterLabel) (v w : Sig)
    (q : Option Label) (S V : ∀ k, List (TopGam k))
    (steps : Nat)
    (hrun : run^[steps]
      (some { l := some (parserLabel (.inl l)), var := v, stk := S }) =
        some { l := q, var := w, stk := V }) (j : Fin 4) :
    V (.inr j) = S (.inr j) := by
  let B := liftStacks (baseStacks S) (counterStacks S)
  let H := headerStacks S
  let c : Cfg OuterGam OuterLabel Sig :=
    { l := some l, var := v, stk := B }
  have hstart : liftNestedCfg H c =
      { l := some (parserLabel (.inl l)), var := v, stk := S } := by
    simp only [liftNestedCfg, c, ShiTMRetainedTop.liftCfg,
      liftCfg, Option.map_some, H, B]
    congr 1
    exact stack_split S
  have hLift := nested_run_lift H steps (some c)
  have hrepr : run^[steps]
      (some { l := some (parserLabel (.inl l)), var := v, stk := S }) =
        (nestedRun^[steps] (some c)).map (liftNestedCfg H) := by
    simpa [hstart] using hLift
  rw [hrun] at hrepr
  cases hres : nestedRun^[steps] (some c) with
  | none => simp [hres] at hrepr
  | some d =>
      simp only [hres, Option.map_some] at hrepr
      have hv := Option.some.inj hrepr
      have hs := congrArg
        (fun x : Cfg TopGam Label Sig => x.stk (.inr j)) hv
      simpa [liftNestedCfg, ShiTMRetainedTop.liftCfg,
        ShiTMOutputEntry.liftCfg,
        topStacks, H, headerStacks] using hs

end ShiTMOutputEntry
