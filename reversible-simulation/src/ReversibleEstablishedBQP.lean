/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Uniform quantum circuit families and the class BQP -- DEFINITIONS ONLY.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import ReversibleEstablishedFamilyCore
import ReversibleEstablishedClassicalCore

set_option autoImplicit false

/-!
# Uniform quantum circuit families and `BQP`

This bundle finally supplies the UNIFORMITY condition that `ShiClass_Core` deliberately left as
an abstract parameter, by reusing the classical polynomial-time notion from the published
`PvsNP` bundle (Cook's Millennium-Prize formulation, machine model `Turing.FinTM2`,
polynomial-time computability `Turing.TM2ComputableInPolyTime`).

Because `PvsNP` fixes the alphabet `Σ = Bool` and languages as `Language Bool = Set (List Bool)`,
`BQP` is defined here over THE SAME language type as `PvsNP.P` and `PvsNP.NP`. That is the point
of reusing that bundle rather than inventing a private machine model: statements relating `BQP`
to `P`, `NP` or `E` are at least well typed.

## The definitions

* `encNat`, `encStr`, `encInstr`, `encLayer`, `encCirc`, `encFamilyAt` -- a serialisation of a
  circuit family's data at input length `n` into a binary string. Each natural is written in
  unary terminated by `false`.

  CAREFUL: length-prefixing alone does NOT make a nested encoding unambiguous, and the generic
  helper `encStr` is NOT injective -- for instance `encStr [[true], [false]]` and
  `encStr [[true, false], []]` are both `[true, true, false, true, false]`. The composite
  encodings are unambiguous for a different reason: an instruction code begins with a tag that
  determines its arity, so instruction codes are prefix-free and a length prefix then says how
  many to consume. That reason is NOT formalised -- no injectivity lemma is proved here.
* `Uniform F` -- there is a polynomial-time computable `f : Str → Str` sending the unary string
  `1^n` to `encFamilyAt F n`. This is CLASSICAL poly-time uniformity in Cook's sense, borrowed
  wholesale from `PvsNP.PolyTimeComputable`.
* `PolyBounded F` -- one polynomial bounds both the depth of `F.circ n` and the ancilla count
  `F.anc n`. Bounding BOTH matters: depth alone would permit exponential width, which is not
  `BQP`. Together they bound circuit size, since size is at most depth times width.
* `toBits` -- reads a binary string `w` as an input of length `w.length`.
* `BQP` -- languages decided by a uniform, polynomially bounded family with error thresholds
  `1/3` and `2/3`.

## HONEST LIMITATIONS -- read before citing this as `BQP`

1. **Gate set.** The underlying circuits use only `H, S, T, X, CNOT` (from `ShiShallow_Core`).
   Clifford+T is universal for quantum computation, but NO UNIVERSALITY THEOREM IS PROVED OR
   IMPORTED here, and no Solovay-Kitaev approximation result either. So strictly this is `BQP`
   *relative to that gate set*: nothing here rules out that a different gate set gives a
   different class. Any claim that this is the standard `BQP` rests on universality, which is
   not formalised.
2. **Size bound is indirect.** `PolyBounded` bounds depth and ancillas, hence size, rather than
   bounding gate count directly. The implication "poly depth and poly width give poly size" is
   true and is proved elsewhere in this development (`size_le_depth_mul_width`), but it is not
   restated here, so this bundle does not itself establish that the families are poly-size.
3. **Measurement model.** Acceptance is the probability that ONE designated output wire reads
   `1` after the circuit runs on the input padded with zero ancillas. There is no intermediate
   measurement, no adaptivity, and no mixed-state or channel formalism anywhere.
4. **Thresholds are hard-coded** at `1/3` and `2/3`. No amplification result is available, so
   nothing here shows the class is insensitive to that choice.
5. **`Uniform` is weaker than textbook poly-time uniformity.** It says a poly-time machine
   PRINTS `encFamilyAt F n`. Genuine uniformity also requires the circuit to be RECOVERABLE
   from that string, i.e. that the encoding be decodable. No decoder and no injectivity lemma
   exists here, so the strength of `Uniform` rests on an unproved property of the encoding.
   Closing this needs an injectivity or decode theorem, which is deliberately left to a
   separate submission.
6. **No relation to `P`, `NP` or `E` is proved.** The language types agree, which makes such
   statements well typed; none of them is asserted. Nor is `BQP` shown to be NONEMPTY -- no
   witness family, not even a trivial one, is exhibited.
7. The gate set and the acceptance semantics come from `ShiShallow_Core`, reached TRANSITIVELY
   through `Def_ShiClass_Core` rather than imported directly; nothing about them is established
   in this file. In particular nothing here bounds `Family.accept` to `[0,1]`, so the `1/3` and
   `2/3` thresholds are only as meaningful as that external fact.
8. DEFINITIONS ONLY: no theorem is written in this file.
-/

namespace ShiBQP

open ShiShallow ShiClass

/-- A natural number written in unary and terminated by `false`, so that concatenations of these
codes are unambiguous. -/
def encNat (k : ℕ) : PvsNP.Str := List.replicate k true ++ [false]

/-- A list of binary strings, length-prefixed and concatenated. -/
def encStr (ls : List PvsNP.Str) : PvsNP.Str := encNat ls.length ++ ls.flatten

/-- A single instruction, as a constructor tag followed by its wire arguments. -/
def encInstr {m : ℕ} : Instr m → PvsNP.Str
  | .h i => encNat 0 ++ encNat (i : ℕ)
  | .s i => encNat 1 ++ encNat (i : ℕ)
  | .t i => encNat 2 ++ encNat (i : ℕ)
  | .x i => encNat 3 ++ encNat (i : ℕ)
  -- the third `cnot` field is the proof `i ≠ j`, a `Prop`, so discarding it loses no data
  | .cnot i j _ => encNat 4 ++ encNat (i : ℕ) ++ encNat (j : ℕ)

/-- A layer: the instruction codes, length-prefixed. -/
def encLayer {m : ℕ} (l : List (Instr m)) : PvsNP.Str := encStr (l.map encInstr)

/-- A layered circuit: the layer codes, length-prefixed. -/
def encCirc {m : ℕ} (c : Layered m) : PvsNP.Str := encStr (c.map encLayer)

/-- The ancilla count, the output wire and the circuit at input length `n`.

Note this is not literally all the data: neither `n` nor the wire count `n + (anc n + 1)` is
written into the string. Both are recoverable in context -- a decoder reads `1^n` as its own
input -- but that convention is unstated in the code. -/
def encFamilyAt (F : Family) (n : ℕ) : PvsNP.Str :=
  encNat (F.anc n) ++ encNat ((F.out n : ℕ)) ++ encCirc (F.circ n)

/-- The unary encoding `1^n` of an input length. -/
def unary (n : ℕ) : PvsNP.Str := List.replicate n true

/-- **Classical polynomial-time uniformity**, in Cook's sense as formalised by `PvsNP`: some
polynomial-time computable string function sends `1^n` to the code of the family's data at
length `n`. -/
def Uniform (F : Family) : Prop :=
  ∃ f : PvsNP.Str → PvsNP.Str,
    PvsNP.PolyTimeComputable f ∧ ∀ n : ℕ, f (unary n) = encFamilyAt F n

/-- Every layer of every circuit is well formed: its gates act on pairwise disjoint wires.

This is NOT decoration. `Layered m` is a list of lists of instructions with no built-in
constraint, so without this a single "layer" may contain arbitrarily many gates and a
depth bound would not bound the gate count at all. -/
def WellFormed (F : Family) : Prop := ∀ (n : ℕ), ∀ l ∈ F.circ n, LayerOk l

/-- One polynomial bounds the depth AND the ancilla count at every input length.

Both are needed: a depth bound alone would allow exponentially many wires. Together with
`WellFormed` they also bound the GATE COUNT, since a well-formed layer has at most as many
gates as there are wires -- but that implication is a theorem elsewhere in this development
(`length_le_width_of_layerOk`, `size_le_depth_mul_width`) and is NOT proved or imported here. -/
def PolyBounded (F : Family) : Prop :=
  ∃ q : Polynomial ℕ, (∀ n : ℕ, depth (F.circ n) ≤ q.eval n) ∧ (∀ n : ℕ, F.anc n ≤ q.eval n)

/-- Read a binary string as a computational-basis input of its own length. -/
def toBits (w : PvsNP.Str) : Bits w.length := fun i => w.get i

/-- **`BQP`**: languages of binary strings decided, with error thresholds `1/3` and `2/3`, by a
classically poly-time-uniform family of polynomially bounded quantum circuits over the gate set
`H, S, T, X, CNOT`. Defined over `Language Bool`, the same type as `PvsNP.P` and `PvsNP.NP`.

See the module docstring for the limitations -- in particular that no universality theorem
justifies calling this gate-set-independent. -/
def BQP : Set (Language Bool) :=
  {L | ∃ F : Family, Uniform F ∧ WellFormed F ∧ PolyBounded F ∧
        ∀ w : PvsNP.Str,
          (w ∈ L → (2 : ℝ) / 3 ≤ F.accept w.length (toBits w)) ∧
          (w ∉ L → F.accept w.length (toBits w) ≤ (1 : ℝ) / 3)}

end ShiBQP
