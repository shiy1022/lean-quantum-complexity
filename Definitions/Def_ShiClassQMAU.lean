/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Definitions.Def_ShiClassQMA

set_option autoImplicit false

/-!
# `QMA(c, s)` with uniformity that carries the witness length

`ShiClassQMA.QMA` states uniformity as `ShiBQP.Uniform F.toFamily`, and
`ShiClassQMA.QMAFamily.toFamily` sets `anc := fun n => F.wit n + F.anc n`.  The
witness/ancilla boundary is therefore folded away before the encoding is formed, and
`ShiBQP.encFamilyAt` only ever sees the sum.  That boundary is not recoverable: two families
agreeing on `wit n + anc n`, on the circuit and on the output wire have identical encodings
while quantifying over different witness registers.

Consequences, both of which motivate this file.  First, `ShiBQP.Uniform F.toFamily` does not
make `F.wit` computable -- `wit` may be an arbitrary function bounded by a polynomial, since
`ShiBQP.PolyBounded` bounds `wit n + anc n` without determining either summand.  Second, any
construction whose wire layout depends on `wit` separately -- every three-copy amplifier
layout does -- is then not uniform, so uniformity cannot be propagated through it.

The definitions below follow the literature instead, where a `QMA` verifier is specified by a
polynomial-time *generated* circuit family and the generating machine emits the whole
description, register sizes included (Kitaev-Shen-Vyalyi, *Classical and Quantum
Computation*, Section 14.2; Watrous, *Quantum Computational Complexity*).  `encQMAFamilyAt`
emits `wit`, `anc`, the output wire and the circuit as four separate fields, and
`UniformQMA` asks for a polynomial-time function producing exactly that.  `QMAU` is
parameterised by its completeness and soundness thresholds, as `QMA(c, s)` is in the
literature, so that statements relating two different threshold pairs -- amplification, for
instance -- are expressible at all.
-/

namespace ShiClassQMAU

/-- The verifier's full description at input length `n`: the witness count, the ancilla
count, the output wire and the circuit, each emitted as its own length-prefixed field.

Contrast `ShiBQP.encFamilyAt`, which is formed from `F.toFamily` and so records only the
sum `F.wit n + F.anc n`. -/
def encQMAFamilyAt (F : ShiClassQMA.QMAFamily) (n : ℕ) : PvsNP.Str :=
  ShiBQP.encNat (F.wit n) ++ ShiBQP.encNat (F.anc n)
    ++ ShiBQP.encNat ((F.out n : ℕ)) ++ ShiBQP.encCirc (F.circ n)

/-- **Polynomial-time uniformity for a `QMAFamily`**, in the literature's sense: some
polynomial-time computable string function sends `1^n` to the family's full description at
length `n`, witness length included.

This implies `ShiBQP.Uniform F.toFamily` but is strictly stronger: it additionally makes
`F.wit` and `F.anc` separately recoverable from `n`. -/
def UniformQMA (F : ShiClassQMA.QMAFamily) : Prop :=
  ∃ f : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable f ∧
    ∀ n : ℕ, f (ShiBQP.unary n) = encQMAFamilyAt F n

/-- **`QMA(c, s)`**: languages such that some `UniformQMA`, polynomially bounded, well formed
`QMAFamily` accepts every member with SOME normalised witness at probability at least `c`,
and rejects every non-member under EVERY normalised witness at probability at most `s`.

Parameterised by the thresholds, so that `QMA(2/3, 1/3)` and `QMA(20/27, 7/27)` are instances
of one notion and amplification statements are expressible.  `ShiClassQMA.QMA` is the
`c = 2/3`, `s = 1/3` case with the weaker folded uniformity. -/
def QMAU (c s : ℝ) : Set (Language Bool) :=
  {L | ∃ F : ShiClassQMA.QMAFamily,
        UniformQMA F ∧ ShiBQP.WellFormed F.toFamily ∧ ShiBQP.PolyBounded F.toFamily ∧
        ∀ w : PvsNP.Str,
          (w ∈ L → ∃ ψ : ShiShallow.QState (F.wit w.length), ShiClassQMA.Normalized ψ ∧
              c ≤ F.acceptWith (ShiBQP.toBits w) ψ) ∧
          (w ∉ L → ∀ ψ : ShiShallow.QState (F.wit w.length), ShiClassQMA.Normalized ψ →
              F.acceptWith (ShiBQP.toBits w) ψ ≤ s)}

end ShiClassQMAU
