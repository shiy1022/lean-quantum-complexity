/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Quantum witnesses and the class QMA -- DEFINITIONS ONLY.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiBQP_Core

set_option autoImplicit false

/-!
# Witness-carrying circuit families and `QMA`

A `BQP` verifier gets only the classical input `x`, padded with zero ancillas. A `QMA` verifier
additionally gets an arbitrary WITNESS quantum state on a designated block of wires. This
bundle adds that block, the input state that plants a witness on it, the resulting acceptance
probability, and the class itself.

`QMAFamily` adds a `wit : ℕ → ℕ` field, splitting the non-input wires into a WITNESS sub-block
of size `wit n` followed by the usual `anc n + 1` ancilla/output block, so the wire count at
length `n` is `n + (wit n + (anc n + 1))`. Because `Nat.add` recurses on its second argument,
`wit n + (anc n + 1)` is DEFINITIONALLY `(wit n + anc n) + 1`, so `toFamily` repackages a
`QMAFamily` as a plain `ShiClass.Family` with ancilla count `wit n + anc n` and the SAME
`circ`/`out`, with no cast. That is what lets `ShiBQP.Uniform`, `WellFormed` and `PolyBounded`
be reused UNCHANGED on `F.toFamily`.

## HONEST LIMITATIONS -- read before citing this as `QMA`

1. **Normalisation is load-bearing and is imposed on BOTH quantifiers.** `ψ : QState (wit n)` is
   an arbitrary function to `ℂ`, not a unit vector. Acceptance is quadratic in `ψ`, so without
   `Normalized ψ` the existential side is satisfiable by simply scaling `ψ` up, trivialising
   membership; and dropping it on the universal side would make non-membership impossible to
   witness truthfully, since a large unnormalised `ψ` can force acceptance above `1/3` on any
   circuit. Both quantifiers are restricted to `Normalized ψ`, and that restriction is the
   entire content keeping this definition non-vacuous.
2. **Gate set, thresholds, size bound and measurement model are exactly as limited as in
   `Def_ShiBQP_Core`**, which this reuses verbatim on `F.toFamily`: gate set `H, S, T, X, CNOT`
   with NO universality theorem imported; thresholds hard-coded at `1/3` and `2/3` with no
   amplification result; depth-and-ancilla bounded rather than gate count; acceptance is a
   single output-wire measurement with no intermediate measurement, adaptivity, or mixed-state
   formalism.
3. **The witness-length polynomial bound is DERIVABLE but NOT PROVED here.**
   `PolyBounded F.toFamily` bounds `F.wit n + F.anc n`, hence bounds `F.wit n`; but this file
   contains no theorems, so a caller relying on "the witness length is polynomially bounded"
   must establish that one-line inequality separately.
4. **No relation to `BQP`, `QCMA`, `PP`, `PSPACE` or `NP` is proved or stated**, and no
   amplification or gap-robustness result. In particular `BQP ⊆ QMA` is NOT shown, although a
   `wit ≡ 0` family would be well typed as a candidate.
5. **The witness block is a single unstructured `QState`** -- a raw amplitude vector, not a
   density operator. There is no multi-use witness, no purity/mixedness distinction, and no
   bound relating `Normalized ψ` to any operator norm.
6. DEFINITIONS ONLY: no theorem or lemma is written in this file. Every derivable fact above
   must be a SEPARATE theorem submission.
-/

namespace ShiClassQMA

open ShiShallow ShiClass

/-- A verifier family with an extra witness-wire-count field `wit`. At input length `n` it acts
on `n + (wit n + (anc n + 1))` wires: `n` input, then `wit n` witness, then `anc n + 1`
ancilla/output. -/
structure QMAFamily where
  /-- Ancilla count beyond the mandatory output wire, as in `ShiClass.Family`. -/
  anc : ℕ → ℕ
  /-- Witness-wire count at input length `n`. -/
  wit : ℕ → ℕ
  /-- The circuit at input length `n`. -/
  circ : (n : ℕ) → Layered (n + (wit n + (anc n + 1)))
  /-- The designated output wire at input length `n`. -/
  out : (n : ℕ) → Fin (n + (wit n + (anc n + 1)))

/-- The underlying `ShiClass.Family`, folding the witness block into the ancilla count. -/
def QMAFamily.toFamily (F : QMAFamily) : ShiClass.Family where
  anc := fun n => F.wit n + F.anc n
  circ := F.circ
  out := F.out

/-- The witness input state: a variation on `ShiShallow.inputState`. Its amplitude at basis
string `y` is `ψ` evaluated at the witness sub-block of `y` when the input block reads `x` and
the ancilla block is all-zero, and `0` otherwise. -/
def witnessInputState {n : ℕ} (F : QMAFamily) (x : Bits n) (ψ : QState (F.wit n)) :
    QState (n + (F.wit n + (F.anc n + 1))) :=
  fun y =>
    if (∀ i : Fin n, y (Fin.castAdd (F.wit n + (F.anc n + 1)) i) = x i) ∧
       (∀ l : Fin (F.anc n + 1), y (Fin.natAdd n (Fin.natAdd (F.wit n) l)) = false)
    then ψ (fun j : Fin (F.wit n) => y (Fin.natAdd n (Fin.castAdd (F.anc n + 1) j)))
    else 0

/-- A `QState` is normalised when its total probability is `1`. Restricting witnesses to this
is what keeps `QMA` non-vacuous; see limitation 1. -/
def Normalized {k : ℕ} (ψ : QState k) : Prop := ∑ z : Bits k, ‖ψ z‖ ^ 2 = 1

/-- Acceptance probability of `F` on input `x` GIVEN witness `ψ`. Mirrors
`ShiShallow.acceptProb` over the witness-carrying input state. -/
noncomputable def QMAFamily.acceptWith {n : ℕ} (F : QMAFamily) (x : Bits n)
    (ψ : QState (F.wit n)) : ℝ :=
  ∑ y : Bits (n + (F.wit n + (F.anc n + 1))),
    if y (F.out n) then ‖runLayered (F.circ n) (witnessInputState F x ψ) y‖ ^ 2 else 0

/-- **`QMA`**: languages such that some classically poly-time-uniform, polynomially bounded
`QMAFamily` accepts every member with SOME normalised witness at probability `≥ 2/3`, and
rejects every non-member under EVERY normalised witness at probability `≤ 1/3`. Defined over
`Language Bool`, matching `ShiBQP.BQP`'s type so comparisons are well typed. -/
def QMA : Set (Language Bool) :=
  {L | ∃ F : QMAFamily,
        ShiBQP.Uniform F.toFamily ∧ ShiBQP.WellFormed F.toFamily ∧
          ShiBQP.PolyBounded F.toFamily ∧
        ∀ w : PvsNP.Str,
          (w ∈ L → ∃ ψ : QState (F.wit w.length), Normalized ψ ∧
              (2 : ℝ) / 3 ≤ F.acceptWith (ShiBQP.toBits w) ψ) ∧
          (w ∉ L → ∀ ψ : QState (F.wit w.length), Normalized ψ →
              F.acceptWith (ShiBQP.toBits w) ψ ≤ (1 : ℝ) / 3)}

end ShiClassQMA
