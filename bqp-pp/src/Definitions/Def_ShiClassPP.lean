/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

The counting classes PP and BPP -- DEFINITIONS ONLY.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_PvsNP

set_option autoImplicit false

/-!
# The counting classes `PP` and `BPP`

Both are built on `PvsNP.PolyTimeChecker`, exactly as `PvsNP.NP` is, and both share a single
counting scaffold `countAccept` -- which is why they are bundled together rather than submitted
separately.

A checking relation `R : Str × Str → Bool` is paired with a natural `k` playing the role of
"the number of random bits is `x.length ^ k`", following the bare-`k` convention `NP` uses for
witness length (not a `Polynomial ℕ`). For a string `x` and a bit budget `m`,
`countAccept R x m` counts, over all `b : Fin m → Bool`, how many make
`R (x, List.ofFn b) = true`. Since `Fin m → Bool` is a `Fintype` with decidable equality this is
a `Finset.card` and is fully computable; no `Classical` axiom is used. Every threshold is
multiplied through by its denominator, so NO DIVISION and no rationals or reals appear anywhere.

## HONEST LIMITATIONS -- read before citing this as `PP`/`BPP`

1. **Purely classical.** No quantum content anywhere, and no relation to `ShiBQP.BQP` or any
   quantum class is stated or proved.
2. **`PP`'s majority condition is NOT shown equivalent to a GapP condition.** `gap` (the signed
   accept-minus-reject count) is defined because it is clean, but `x ∈ L ↔ 0 < gap R x m` is not
   proved equivalent to the `2 * countAccept > 2 ^ m` clause actually used, even though the two
   are mathematically the same.
3. **The randomness length is a specific, not the most general, choice.** `x.length ^ k` for a
   bare `k : ℕ` mirrors `NP`'s convention; it is one polynomial shape, not an arbitrary
   polynomial or an arbitrary poly-time-computable bound.
4. **No inclusions or closure properties are proved.** `BPP ⊆ PP`, `PvsNP.P ⊆ BPP`, and closure
   of either class under complement are all standard and all ABSENT here.
5. **`countAccept` ranges only over strings of the exact length `m`** -- it filters
   `Fin m → Bool`, i.e. exactly the `2 ^ m` strings of that length, with uniform weight. It does
   not range over shorter strings or a non-uniform distribution. The supporting fact
   `(List.ofFn b).length = m` (`List.length_ofFn`) is true but is NOT invoked here.
6. **Thresholds are hard-coded** -- strict majority for `PP`, `2/3` and `1/3` for `BPP` -- with
   no amplification result showing insensitivity to those constants.
7. DEFINITIONS ONLY: no theorem or lemma is written in this file.
-/

namespace ShiClassPP

open PvsNP

/-- The counting scaffold shared by `PP` and `BPP`: how many of the `2 ^ m` strings of length
`m` (each `List.ofFn b` for `b : Fin m → Bool`) make `R (x, ·)` accept. Fully computable. -/
def countAccept (R : Str × Str → Bool) (x : Str) (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun b : Fin m → Bool => R (x, List.ofFn b) = true)).card

/-- The signed accept-minus-reject count, a GapP-style quantity. Positive exactly when accepts
strictly outnumber rejects. NOT shown equivalent to the majority condition used in `PP`. -/
def gap (R : Str × Str → Bool) (x : Str) (m : ℕ) : ℤ :=
  2 * (countAccept R x m : ℤ) - 2 ^ m

/-- **`PP`**: strict-majority counting acceptance. `x ∈ L` exactly when strictly more than half
of the `2 ^ m` length-`m` strings make `R` accept, with `m = x.length ^ k`. The `1/2` threshold
is cleared by multiplying through by `2`, keeping everything in `ℕ`. -/
def PP : Set (Language Bool) :=
  {L | ∃ (R : Str × Str → Bool) (k : ℕ), PolyTimeChecker R ∧
        ∀ x : Str, x ∈ L ↔ 2 * countAccept R x (x.length ^ k) > 2 ^ (x.length ^ k)}

/-- **`BPP`**: bounded two-sided error. Membership forces at least a `2/3` fraction of length-`m`
strings to accept, non-membership at most `1/3`, with `m = x.length ^ k`. Both thresholds are
cleared by multiplying through by `3`, keeping everything in `ℕ`. -/
def BPP : Set (Language Bool) :=
  {L | ∃ (R : Str × Str → Bool) (k : ℕ), PolyTimeChecker R ∧
        ∀ x : Str,
          (x ∈ L → 3 * countAccept R x (x.length ^ k) ≥ 2 * 2 ^ (x.length ^ k)) ∧
          (x ∉ L → 3 * countAccept R x (x.length ^ k) ≤ 2 ^ (x.length ^ k))}

end ShiClassPP
