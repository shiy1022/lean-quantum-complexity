/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Counting classes relativised to an abstract efficiency predicate -- DEFINITIONS ONLY.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiClassPP

set_option autoImplicit false

/-!
# `PPof` and `BPPof`: counting classes relativised to an abstract efficiency notion

`Def_ShiClassPP.PP` and `.BPP` are built on `PvsNP.PolyTimeChecker`. At this Mathlib revision,
deriving `PolyTimeChecker (fun p => !(R p))` from `PolyTimeChecker R` needs the composition of
a poly-time-computability witness with output negation, and the only such principle available,
`TM2ComputableInPolyTime.comp` (`Mathlib/Computability/TuringMachine/Computable.lean:284`), is a
`proof_wanted` -- an admitted, unproved stub. Consequently NO closure property of `PP`/`BPP`
routed through that lemma is derivable at present.

This bundle sidesteps the gap the way `ShiClass.InClass` sidesteps the missing uniformity
predicate for `BQP`: it takes the efficiency notion `Eff` as a PARAMETER rather than fixing it,
and names the closure properties `Eff` would need, so downstream theorems can be stated and
proved conditionally today. `countAccept` is NOT redefined; it is reused from `ShiClassPP`.

## The bridge to the published classes

`PPof PvsNP.PolyTimeChecker` is definitionally `ShiClassPP.PP`, and `BPPof
PvsNP.PolyTimeChecker` is definitionally `ShiClassPP.BPP` -- the bodies are verbatim copies with
`Eff R` instantiated to `PolyTimeChecker R`. So these are a STRICT GENERALISATION of the
published classes, not a competing second definition: any theorem about `PPof Eff` specialises
to the one already-published `ShiClassPP.PP`. Recorded here as documentation only; formalising
it is a follow-up theorem submission, since this file contains no theorems.

## HONEST LIMITATIONS

1. **`Eff` is a bare, uninterpreted parameter with NO computability content.** Instantiating
   `Eff := fun _ => True` makes `PPof Eff` and `BPPof Eff` enormous and proves nothing about the
   real `PP`/`BPP`.
2. **Only the `PvsNP.PolyTimeChecker` instantiation recovers the real classes**, by the
   definitional equality above. Every other instantiation is a different class of unknown size.
3. **`EffClosedNeg` and `EffClosedAnd` are exactly what the unproved `proof_wanted`
   `TM2ComputableInPolyTime.comp` would supply at `Eff := PolyTimeChecker`.** They are named
   hypotheses, NOT proved to hold of `PolyTimeChecker`, and cannot be until that stub is
   discharged upstream.
4. **This is standard relative-to-an-efficiency-notion practice and proves NO absolute
   containment, separation, or closure result.** Everything here is scaffolding.
5. **Every limitation of `ShiClassPP` carries over unchanged**, since `countAccept`/`gap` are
   reused verbatim: the majority condition is not shown GapP-equivalent, the randomness length
   `x.length ^ k` is one specific polynomial shape, thresholds are hard-coded with no
   amplification result, and `countAccept` ranges only over strings of exactly length `m`.
6. **Nothing quantum appears anywhere in this file.**
7. DEFINITIONS ONLY: no theorem or lemma is written here.
-/

namespace ShiClassRel

open PvsNP ShiClassPP

/-- **`PPof Eff`**: strict-majority counting acceptance, exactly as `ShiClassPP.PP` but with an
abstract efficiency predicate in place of `PolyTimeChecker`. At `Eff := PvsNP.PolyTimeChecker`
this is definitionally `ShiClassPP.PP`. -/
def PPof (Eff : (Str × Str → Bool) → Prop) : Set (Language Bool) :=
  {L | ∃ (R : Str × Str → Bool) (k : ℕ), Eff R ∧
        ∀ x : Str, x ∈ L ↔ 2 * countAccept R x (x.length ^ k) > 2 ^ (x.length ^ k)}

/-- **`BPPof Eff`**: bounded two-sided error, exactly as `ShiClassPP.BPP` but with an abstract
efficiency predicate. At `Eff := PvsNP.PolyTimeChecker` this is definitionally
`ShiClassPP.BPP`. -/
def BPPof (Eff : (Str × Str → Bool) → Prop) : Set (Language Bool) :=
  {L | ∃ (R : Str × Str → Bool) (k : ℕ), Eff R ∧
        ∀ x : Str,
          (x ∈ L → 3 * countAccept R x (x.length ^ k) ≥ 2 * 2 ^ (x.length ^ k)) ∧
          (x ∉ L → 3 * countAccept R x (x.length ^ k) ≤ 2 ^ (x.length ^ k))}

/-- `Eff` is closed under complementing the checker's output -- exactly what composing a
`PolyTimeChecker` witness with output negation would supply, were the Mathlib `proof_wanted`
`TM2ComputableInPolyTime.comp` proved. A bare hypothesis name; NOT shown to hold of
`PolyTimeChecker`. -/
def EffClosedNeg (Eff : (Str × Str → Bool) → Prop) : Prop :=
  ∀ R : Str × Str → Bool, Eff R → Eff (fun p => !(R p))

/-- `Eff` is closed under pairing two checkers with Boolean AND. Motivated by the
intersection-style arguments relating `PPof` and `BPPof`. A bare hypothesis name; NOT shown to
hold of `PolyTimeChecker`. -/
def EffClosedAnd (Eff : (Str × Str → Bool) → Prop) : Prop :=
  ∀ R₁ R₂ : Str × Str → Bool, Eff R₁ → Eff R₂ → Eff (fun p => R₁ p && R₂ p)

end ShiClassRel
