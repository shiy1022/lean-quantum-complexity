/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Polynomial time implies polynomial space for one machine run (plan task S04).
-/
import Space.ReachableAlphabet
import Definitions.Def_PvsNP

set_option autoImplicit false

/-!
# From a time certificate to a bound on every reachable configuration

A machine has a uniform per-step stack-growth constant `D` (`ShiTMStackGrowth.finite_growth`).
If it halts with an output within `m` steps, then every configuration up to the halt has space
at most `input length + m * D`, and every later iterate is `none`
(`spaceBoundedOn_of_outputs`). So the bound holds for **all** reachable configurations, with no
caller-supplied space hypothesis.

Corollary sanity check: the corrected class contains `PvsNP.P`.
-/

namespace ShiSpace

open Turing

/-- The uniform per-step growth constant of a bundled machine. -/
theorem exists_growth (tm : FinTM2) :
    ∃ D : ℕ, ∀ l v S, ShiTMStackGrowth.size (TM2.stepAux (tm.m l) v S).stk ≤
      ShiTMStackGrowth.size S + D :=
  ShiTMStackGrowth.finite_growth tm.m

/-- A run that outputs within `m` steps keeps every reachable configuration within
`xs.length + m * D`. -/
theorem spaceBoundedOn_of_outputsInTime (tm : FinTM2) (D : ℕ)
    (hD : ∀ l v S, ShiTMStackGrowth.size (TM2.stepAux (tm.m l) v S).stk ≤
      ShiTMStackGrowth.size S + D)
    {xs : List (tm.Γ tm.k₀)} {ys : List (tm.Γ tm.k₁)} {m : ℕ}
    (h : TM2OutputsInTime tm xs (some ys) m) :
    SpaceBoundedOn tm xs (xs.length + m * D) := by
  apply spaceBoundedOn_of_outputs h.toTM2Outputs
  intro t ht e he
  have hsz := ShiTMStackGrowth.run_size_le tm.m D hD t _ e he
  unfold cfgSpace
  have hc := cfgSpace_initList tm xs
  unfold cfgSpace at hc
  rw [hc] at hsz
  have hsteps : h.toTM2Outputs.steps ≤ m := h.steps_le_m
  have : t * D ≤ m * D := Nat.mul_le_mul_right D (le_trans ht hsteps)
  omega

/-- **Certificate-to-space.** Every polynomial-time bundled computation is polynomial-space on
every input, with an explicit polynomial `X + C D * time`. -/
theorem polySpace_of_polyTime {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f : α → β} (c : TM2ComputableInPolyTime ea eb f) :
    ∃ p : Polynomial ℕ, ∀ a : α,
      SpaceBoundedOn c.tm ((ea a).map c.inputAlphabet.invFun) (p.eval (ea a).length) := by
  obtain ⟨D, hD⟩ := exists_growth c.tm
  refine ⟨Polynomial.X + Polynomial.C D * c.time, fun a => ?_⟩
  have h := spaceBoundedOn_of_outputsInTime c.tm D hD (c.outputsFun a)
  refine h.mono ?_
  simp only [List.length_map, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_C]
  rw [Nat.mul_comm]

/-- The checker form used by `PP`: a polynomial bound in the tagged-pair input length
`x.1.length + x.2.length`. -/
theorem checker_polySpace {R : PvsNP.Str × PvsNP.Str → Bool}
    (c : TM2ComputableInPolyTime PvsNP.encodePair Computability.encodeBool R) :
    ∃ p : Polynomial ℕ, ∀ x : PvsNP.Str × PvsNP.Str,
      SpaceBoundedOn c.tm ((PvsNP.encodePair x).map c.inputAlphabet.invFun)
        (p.eval (x.1.length + x.2.length)) := by
  obtain ⟨p, hp⟩ := polySpace_of_polyTime c
  refine ⟨p, fun x => ?_⟩
  have h := hp x
  simpa [PvsNP.encodePair] using h

/-- Sanity check of the corrected model: polynomial time is contained in it. -/
theorem P_subset_PSPACE : PvsNP.P ⊆ PSPACE := by
  rintro L ⟨χ, ⟨c⟩, hL⟩
  obtain ⟨p, hp⟩ := polySpace_of_polyTime c
  exact ⟨χ, ⟨c.toTM2ComputableInTime.toTM2Computable, p, fun x => hp x⟩, hL⟩

end ShiSpace
