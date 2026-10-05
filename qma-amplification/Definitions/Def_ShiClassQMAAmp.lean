/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

The explicit threefold majority amplifier on `ShiClassQMA.QMAFamily` -- DEFINITIONS ONLY.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiClassQMA
import Definitions.Def_ShiEmbed_Core
import Theorems.Thm_ShiShallow_exists_layout_bijection
import Theorems.Thm_ShiShallow_exists_fanout_embedded_pullback
import Theorems.Thm_ShiShallow_exists_majority_readout_at_wires_layerOk_depth

set_option autoImplicit false

/-!
# The threefold amplifier as an EXPLICIT construction

`ShiClassQMA.exists_threefold_amplifier_structure_at_output_wires` proves
`∃ T : QMAFamily → QMAFamily, …`, and the `T` it builds is pinned only up to the
EXISTENTIALLY QUANTIFIED readout and fan-out blocks: the payload characterises them
BEHAVIOURALLY (`runLayered rd ψ = ⟨majority-xor⟩`, `∀ l ∈ rd, LayerOk l`, `depth rd = 111`,
and the fan-out action laws), and many syntactically different circuits satisfy those
characterisations.

That is fatal for one specific downstream purpose. `ShiBQP.encCirc` encodes SYNTAX: the
encoding of a family is a function of the actual instruction list, not of its input-output
behaviour. So a downstream statement about the amplified family's ENCODING -- in particular
uniformity, "there is a poly-time machine emitting the amplified verifier" -- cannot even be
WRITTEN against a behaviourally-specified `T`, because no string is determined. The explicit
construction does exist inside the proof of the theorem above, but there every component is
`private`, hence unimportable, and a `private` name cannot be referred to from any other
module.

This bundle re-exports that construction as PUBLIC definitions, so the syntax is nameable
once and for all. Nothing here is a theorem: the properties of `ampFamily` (its `wit`/`anc`
arithmetic, `depth (ampFamily F).circ n = 3 * depth (F.circ n) + 113`, `LayerOk`,
`WellFormed`, `PolyBounded`, soundness and completeness) are deliberately NOT stated here and
are to be proved separately, about `ampFamily`, by the same arguments that
`ShiClassQMA.exists_threefold_amplifier_structure_at_output_wires` uses -- which is why every
body below is kept term-for-term identical to its counterpart in that proof, up to the
renaming described next.

## Provenance and renaming

The construction, and every property proved of it, is that of
`ShiClassQMA.exists_threefold_amplifier_structure_at_output_wires`. Its private components
are renamed here by dropping the `shiT_` / `shiT3_` prefixes and adding a uniform `amp`
prefix:

| there            | here          |
| ---------------- | ------------- |
| `shiT_emb`       | `ampEmb`      |
| `shiT_fanVal`    | `ampFanVal`   |
| `shiT_fanEmb`    | `ampFanEmb`   |
| `shiT_sig`       | `ampSig`      |
| `shiT_scr`       | `ampScr`      |
| `shiT_e`         | `ampE`        |
| `shiT_read`      | `ampRead`     |
| `shiT_g`         | `ampG`        |
| `shiT3_g2`       | `ampG2`       |
| `shiT3_g3`       | `ampG3`       |
| `shiT3_p`        | `ampP`        |
| `shiT3_q`        | `ampQ`        |
| `shiT3_fan2`     | `ampFan2`     |
| `shiT3_fan3`     | `ampFan3`     |
| `shiT_circ`      | `ampCirc`     |
| `shiT_T`         | `ampFamily`   |

Three of the private components there (`shiT_readEx`, `shiT3_fanEx2`, `shiT3_fanEx3`) are
declarations whose TYPE is a proposition -- they name the existential statements that
`Classical.choose` is applied to. A top-level declaration inhabiting a `Prop` is a theorem
whatever keyword introduces it, so they are NOT re-exported; their bodies are inlined into
`ampRead`, `ampFan2` and `ampFan3` instead. That costs a downstream consumer nothing: to use
`Classical.choose_spec` it restates the existential (the very statements written out inline
below) and the resulting `Classical.choose` term is definitionally the definition here,
because the distinctness and injectivity arguments are proofs of propositions and so are
definitionally irrelevant.

## The construction

* `ampSig n w a` is the layout permutation of the amplified register, `Classical.choose` of
  `ShiShallow.exists_layout_bijection n w a`. It is NONCOMPUTABLE and must stay that way:
  its thirteen clauses pin it on EVERY wire of the register, so every index occurring in the
  amplified family's encoding is fixed by a clause and downstream proofs rewrite with the
  clauses rather than evaluating the choice.
* `ampE n w a off h` is copy `off`'s wire embedding: position `off + v` of the concatenated
  three-copy register, transported through the layout.
* `ampScr n w a` is the scratch wire -- the layout image of concatenated position
  `3 * (n + (w + (a + 1)))` -- and it is the amplified family's output wire.
* `ampG`/`ampG2`/`ampG3` are the fan-out wire maps (copy 1's input block to copy 2's and
  copy 3's), and `ampFan2`/`ampFan3` the corresponding one-layer fan-out circuits built
  DIRECTLY on the amplified register via `ShiShallow.exists_fanout_embedded_pullback`, so
  that their ACTION on an arbitrary ambient state is available.
* `ampRead` is the 111-layer majority readout, stated at the three copies' OWN output wires
  `ampE … (F.out n)` rather than at any numeral: `QMAFamily.out` is a free structure field,
  so a numeral readout would vote the wrong wires.
* `ampP`/`ampQ` are the ancilla addresses of copy 2's and copy 3's input blocks,
  `a + 1 + j` and `n + 2 * a + 2 + j`, matching clauses 6 and 10 of the layout.
* `ampCirc` concatenates the two fan-outs, the three embedded copies of `F.circ n`, and the
  readout; `ampFamily` packages it with `wit := 3 * F.wit n`,
  `anc := 2 * n + 3 * F.anc n + 3` and `out := ampScr`.
-/

namespace ShiClassQMAAmp

open ShiShallow ShiClassQMA

/-- Copy `off`'s wire addresses inside the concatenated three-copy register. -/
def ampEmb (M off : ℕ) (hoff : off + M ≤ 3 * M) (v : Fin M) : Fin (3 * M + 1) :=
  ⟨off + v.val, by have := v.isLt; omega⟩

/-- Fan-out addresses: first half is copy 1's input block, second half the block at `off`. -/
def ampFanVal (n off k : ℕ) : ℕ := if k < n then k else off + (k - n)

/-- The fan-out source-and-target register embedded into the concatenated register. -/
def ampFanEmb (n M off : ℕ) (h1 : n ≤ off) (h2 : off + n ≤ 3 * M)
    (v : Fin (n + n)) : Fin (3 * M + 1) :=
  ⟨ampFanVal n off v.val, by
    have hv := v.isLt
    simp only [ampFanVal]
    split_ifs <;> omega⟩

/-- The layout permutation of the amplified register. NONCOMPUTABLE by design: the thirteen
clauses of `ShiShallow.exists_layout_bijection` pin it on every wire. -/
noncomputable def ampSig (n w a : ℕ) :
    Fin (3 * (n + (w + (a + 1))) + 1) → Fin (n + (3 * w + ((2 * n + 3 * a + 3) + 1))) :=
  Classical.choose (ShiShallow.exists_layout_bijection n w a)

/-- The scratch wire, which is the amplified family's output wire. Its layout clause gives
`(ampScr n w a).val = 3 * n + 3 * w + 3 * a + 3`. -/
noncomputable def ampScr (n w a : ℕ) :
    Fin (n + (3 * w + ((2 * n + 3 * a + 3) + 1))) :=
  ampSig n w a ⟨3 * (n + (w + (a + 1))), by omega⟩

/-- Copy `off`'s wire map into the amplified register. -/
noncomputable def ampE (n w a off : ℕ)
    (h : off + (n + (w + (a + 1))) ≤ 3 * (n + (w + (a + 1)))) :
    Fin (n + (w + (a + 1))) → Fin (n + (3 * w + ((2 * n + 3 * a + 3) + 1))) :=
  ampSig n w a ∘ ampEmb (n + (w + (a + 1))) off h

/-- The 111-layer majority readout onto the scratch wire, voting the three copies' images of
`v`. Downstream, `v` is instantiated at `F.out n`, so the vote is on the copies' OWN output
wires for an arbitrary `QMAFamily.out` field. The existential this chooses from is
`ShiShallow.exists_majority_readout_at_wires_layerOk_depth` at the four wires below. -/
noncomputable def ampRead (n w a : ℕ) (v : Fin (n + (w + (a + 1)))) :
    Layered (n + (3 * w + ((2 * n + 3 * a + 3) + 1))) :=
  Classical.choose
    (ShiShallow.exists_majority_readout_at_wires_layerOk_depth
      (ampE n w a 0 (by omega) v)
      (ampE n w a (n + (w + (a + 1))) (by omega) v)
      (ampE n w a (2 * (n + (w + (a + 1)))) (by omega) v)
      (ampScr n w a)
      (by
        intro he
        have hv := v.isLt
        have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
        have h2 : ampEmb (n + (w + (a + 1))) 0 (by omega) v
            = ampEmb (n + (w + (a + 1))) (n + (w + (a + 1))) (by omega) v := hb.injective he
        have h3 : 0 + v.val = (n + (w + (a + 1))) + v.val := congrArg Fin.val h2
        omega)
      (by
        intro he
        have hv := v.isLt
        have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
        have h2 : ampEmb (n + (w + (a + 1))) 0 (by omega) v
            = ampEmb (n + (w + (a + 1))) (2 * (n + (w + (a + 1)))) (by omega) v :=
          hb.injective he
        have h3 : 0 + v.val = 2 * (n + (w + (a + 1))) + v.val := congrArg Fin.val h2
        omega)
      (by
        intro he
        have hv := v.isLt
        have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
        have h2 : ampEmb (n + (w + (a + 1))) (n + (w + (a + 1))) (by omega) v
            = ampEmb (n + (w + (a + 1))) (2 * (n + (w + (a + 1)))) (by omega) v :=
          hb.injective he
        have h3 : (n + (w + (a + 1))) + v.val = 2 * (n + (w + (a + 1))) + v.val :=
          congrArg Fin.val h2
        omega)
      (by
        intro he
        have hv := v.isLt
        have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
        have h2 : ampEmb (n + (w + (a + 1))) 0 (by omega) v
            = (⟨3 * (n + (w + (a + 1))), by omega⟩ :
                Fin (3 * (n + (w + (a + 1))) + 1)) := hb.injective he
        have h3 : 0 + v.val = 3 * (n + (w + (a + 1))) := congrArg Fin.val h2
        omega)
      (by
        intro he
        have hv := v.isLt
        have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
        have h2 : ampEmb (n + (w + (a + 1))) (n + (w + (a + 1))) (by omega) v
            = (⟨3 * (n + (w + (a + 1))), by omega⟩ :
                Fin (3 * (n + (w + (a + 1))) + 1)) := hb.injective he
        have h3 : (n + (w + (a + 1))) + v.val = 3 * (n + (w + (a + 1))) :=
          congrArg Fin.val h2
        omega)
      (by
        intro he
        have hv := v.isLt
        have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
        have h2 : ampEmb (n + (w + (a + 1))) (2 * (n + (w + (a + 1)))) (by omega) v
            = (⟨3 * (n + (w + (a + 1))), by omega⟩ :
                Fin (3 * (n + (w + (a + 1))) + 1)) := hb.injective he
        have h3 : 2 * (n + (w + (a + 1))) + v.val = 3 * (n + (w + (a + 1))) :=
          congrArg Fin.val h2
        omega))

/-- The fan-out wire map from copy 1's input block to the input block at `off`. -/
noncomputable def ampG (n w a off : ℕ) (h1 : n ≤ off)
    (h2 : off + n ≤ 3 * (n + (w + (a + 1)))) :
    Fin (n + n) → Fin (n + (3 * w + ((2 * n + 3 * a + 3) + 1))) :=
  ampSig n w a ∘ ampFanEmb n (n + (w + (a + 1))) off h1 h2

/-- Copy 1's input block to copy 2's. -/
noncomputable def ampG2 (n w a : ℕ) :
    Fin (n + n) → Fin (n + (3 * w + ((2 * n + 3 * a + 3) + 1))) :=
  ampG n w a (n + (w + (a + 1))) (by omega) (by omega)

/-- Copy 1's input block to copy 3's. -/
noncomputable def ampG3 (n w a : ℕ) :
    Fin (n + n) → Fin (n + (3 * w + ((2 * n + 3 * a + 3) + 1))) :=
  ampG n w a (2 * (n + (w + (a + 1)))) (by omega) (by omega)

/-- Copy 2's input block inside the amplified ancilla block, layout clause 6. -/
def ampP (n a : ℕ) (j : Fin n) : Fin (2 * n + 3 * a + 3 + 1) :=
  ⟨a + 1 + j.val, by have := j.isLt; omega⟩

/-- Copy 3's input block inside the amplified ancilla block, layout clause 10. -/
def ampQ (n a : ℕ) (j : Fin n) : Fin (2 * n + 3 * a + 3 + 1) :=
  ⟨n + 2 * a + 2 + j.val, by have := j.isLt; omega⟩

/-- The one-layer fan-out copying the input into copy 2, built DIRECTLY on the amplified
register, so its action on an arbitrary ambient state is available. The existential this
chooses from is `ShiShallow.exists_fanout_embedded_pullback n _ (ampG2 n w a) _`. -/
noncomputable def ampFan2 (n w a : ℕ) :
    Layered (n + (3 * w + ((2 * n + 3 * a + 3) + 1))) :=
  Classical.choose
    (ShiShallow.exists_fanout_embedded_pullback n (n + (3 * w + ((2 * n + 3 * a + 3) + 1)))
      (ampG2 n w a)
      (by
        intro x y he
        have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
        have h2 : ampFanEmb n (n + (w + (a + 1))) (n + (w + (a + 1))) (by omega) (by omega) x
            = ampFanEmb n (n + (w + (a + 1))) (n + (w + (a + 1))) (by omega) (by omega) y :=
          hb.injective he
        have hx := x.isLt
        have hy := y.isLt
        have h : ampFanVal n (n + (w + (a + 1))) x.val
            = ampFanVal n (n + (w + (a + 1))) y.val := congrArg Fin.val h2
        apply Fin.val_injective
        simp only [ampFanVal] at h
        split_ifs at h <;> omega))

/-- The one-layer fan-out copying the input into copy 3. The existential this chooses from is
`ShiShallow.exists_fanout_embedded_pullback n _ (ampG3 n w a) _`. -/
noncomputable def ampFan3 (n w a : ℕ) :
    Layered (n + (3 * w + ((2 * n + 3 * a + 3) + 1))) :=
  Classical.choose
    (ShiShallow.exists_fanout_embedded_pullback n (n + (3 * w + ((2 * n + 3 * a + 3) + 1)))
      (ampG3 n w a)
      (by
        intro x y he
        have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
        have h2 : ampFanEmb n (n + (w + (a + 1))) (2 * (n + (w + (a + 1)))) (by omega)
              (by omega) x
            = ampFanEmb n (n + (w + (a + 1))) (2 * (n + (w + (a + 1)))) (by omega)
              (by omega) y := hb.injective he
        have hx := x.isLt
        have hy := y.isLt
        have h : ampFanVal n (2 * (n + (w + (a + 1)))) x.val
            = ampFanVal n (2 * (n + (w + (a + 1)))) y.val := congrArg Fin.val h2
        apply Fin.val_injective
        simp only [ampFanVal] at h
        split_ifs at h <;> omega))

/-- The amplified circuit: two fan-outs, three embedded copies of `F.circ n`, then the
111-layer majority readout at the three copies' output wires. Its depth is
`3 * depth (F.circ n) + 113`. -/
noncomputable def ampCirc (F : ShiClassQMA.QMAFamily) (n : ℕ) :
    Layered (n + (3 * F.wit n + ((2 * n + 3 * F.anc n + 3) + 1))) :=
  ampFan2 n (F.wit n) (F.anc n)
    ++ ampFan3 n (F.wit n) (F.anc n)
    ++ ShiEmbed.embedCirc (ampE n (F.wit n) (F.anc n) 0 (by omega))
      (by
        intro x y he
        have hb :=
          (Classical.choose_spec
            (ShiShallow.exists_layout_bijection n (F.wit n) (F.anc n))).1
        have h2 : ampEmb (n + (F.wit n + (F.anc n + 1))) 0 (by omega) x
            = ampEmb (n + (F.wit n + (F.anc n + 1))) 0 (by omega) y := hb.injective he
        have h3 : 0 + x.val = 0 + y.val := congrArg Fin.val h2
        exact Fin.val_injective (by omega)) (F.circ n)
    ++ ShiEmbed.embedCirc
      (ampE n (F.wit n) (F.anc n) (n + (F.wit n + (F.anc n + 1))) (by omega))
      (by
        intro x y he
        have hb :=
          (Classical.choose_spec
            (ShiShallow.exists_layout_bijection n (F.wit n) (F.anc n))).1
        have h2 : ampEmb (n + (F.wit n + (F.anc n + 1)))
              (n + (F.wit n + (F.anc n + 1))) (by omega) x
            = ampEmb (n + (F.wit n + (F.anc n + 1)))
              (n + (F.wit n + (F.anc n + 1))) (by omega) y := hb.injective he
        have h3 : (n + (F.wit n + (F.anc n + 1))) + x.val
            = (n + (F.wit n + (F.anc n + 1))) + y.val := congrArg Fin.val h2
        exact Fin.val_injective (by omega)) (F.circ n)
    ++ ShiEmbed.embedCirc
      (ampE n (F.wit n) (F.anc n) (2 * (n + (F.wit n + (F.anc n + 1)))) (by omega))
      (by
        intro x y he
        have hb :=
          (Classical.choose_spec
            (ShiShallow.exists_layout_bijection n (F.wit n) (F.anc n))).1
        have h2 : ampEmb (n + (F.wit n + (F.anc n + 1)))
              (2 * (n + (F.wit n + (F.anc n + 1)))) (by omega) x
            = ampEmb (n + (F.wit n + (F.anc n + 1)))
              (2 * (n + (F.wit n + (F.anc n + 1)))) (by omega) y := hb.injective he
        have h3 : 2 * (n + (F.wit n + (F.anc n + 1))) + x.val
            = 2 * (n + (F.wit n + (F.anc n + 1))) + y.val := congrArg Fin.val h2
        exact Fin.val_injective (by omega)) (F.circ n)
    ++ ampRead n (F.wit n) (F.anc n) (F.out n)

/-- The threefold majority amplifier as an EXPLICIT map on verifier families: three copies of
`F`, the input fanned out to all three, and a majority vote of the three copies' output wires
onto the scratch wire. This is the `T` built by
`ShiClassQMA.exists_threefold_amplifier_structure_at_output_wires`, with the same fields. -/
noncomputable def ampFamily (F : ShiClassQMA.QMAFamily) : ShiClassQMA.QMAFamily :=
  { anc := fun n => 2 * n + 3 * F.anc n + 3
    wit := fun n => 3 * F.wit n
    circ := ampCirc F
    out := fun n => ampScr n (F.wit n) (F.anc n) }

end ShiClassQMAAmp
