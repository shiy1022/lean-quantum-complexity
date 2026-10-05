/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Definitions.Def_ShiClassQMAAmp
import Definitions.Def_ShiExplicitCirc

set_option autoImplicit false

/-!
# An amplified verifier family whose circuit is a determined gate list

`ShiClassQMAAmp.ampFamily` amplifies a `ShiClassQMA.QMAFamily` correctly, but its circuit
field `ShiClassQMAAmp.ampCirc` is assembled from `ShiClassQMAAmp.ampFan2`,
`ShiClassQMAAmp.ampFan3` and `ShiClassQMAAmp.ampRead`, each of which is `Classical.choose` of
a purely BEHAVIOURAL existence statement -- `ShiShallow.exists_fanout_embedded_pullback` and
`ShiShallow.exists_majority_readout_at_wires_layerOk_depth`.  Those existentials pin only the
ACTION, the layerwise well-formedness and the depth of their circuits.  Many syntactically
different gate lists satisfy them, so the gate list of `ampCirc` is undetermined, and with it
the image of that gate list under `ShiBQP.encCirc`: there is no definite string for a machine
to emit.  The DEPTH and the ACTION of `ampFamily` are unaffected by this -- only the syntax is
loose -- so the gap is purely one of determinacy.

The definitions here close that gap by rebuilding the same six-way concatenation out of
circuit TERMS, so that the resulting family's circuit is a concrete gate list on every
argument.  They reuse the terms pinned by two accepted results:

* `ShiShallow.explicit_toffoli_majority_readout_and_fanout_circuits`, which pins the majority
  readout to `ShiExplicitCirc.readCirc` -- three explicit Toffolis built from
  `ShiExplicitCirc.toffCirc` and `ShiExplicitCirc.toffGates`, one gate per layer, depth 111;
* `ShiShallow.explicit_embedded_fanout_circuit`, which pins the fan-out embedded along an
  injection `g : Fin (n + n) → Fin N` to the single-layer list of controlled-nots
  `(List.finRange n).map (fun j => Instr.cnot (g (Fin.castAdd n j)) (g (Fin.natAdd n j)) _)`
  reproduced as `fanEmbCirc` below.  The plain ladder `ShiExplicitCirc.fanCirc` is NOT usable
  here: it lives on the doubled register `Fin (n + n)`, whereas the amplifier needs the
  fan-out pushed along the layout map into the amplified register.

The layout permutation `ShiClassQMAAmp.ampSig` is reused unchanged and stays noncomputable.
That is intended and is not a determinacy gap: the thirteen clauses of
`ShiShallow.exists_layout_bijection` pin its value on every wire of the register, so each wire
index is provably equal to explicit arithmetic and the choice is never evaluated.  Likewise
`ampScr`, `ampE`, `ampG2`, `ampG3`, `ampEmb`, `ampFanVal` and `ampFanEmb` are reused verbatim;
only the three chosen circuits are replaced.  Everything here is `noncomputable` for that
reason.

The action, well-formedness, depth and amplification properties of `ampFamilyX` are NOT
asserted here -- a definition bundle may contain no theorem -- and are left to downstream
results.
-/

namespace ShiClassQMAAmpX

open ShiShallow ShiClassQMA

/-- The one-layer fan-out along an injection `g : Fin (n + n) → Fin N`: one controlled-not
from the image of wire `j` of the low half onto the image of the matching wire of the high
half.  Depth 1.  This is the term pinned by
`ShiShallow.explicit_embedded_fanout_circuit`. -/
def fanEmbCirc (n N : ℕ) (g : Fin (n + n) → Fin N) (hg : Function.Injective g) : Layered N :=
  [(List.finRange n).map (fun j =>
    Instr.cnot (g (Fin.castAdd n j)) (g (Fin.natAdd n j))
      (fun h => by
        have hj : (j : ℕ) < n := j.isLt
        have hv : (j : ℕ) = n + (j : ℕ) := congrArg Fin.val (hg h)
        omega))]

/-- The one-layer fan-out copying the input block into copy 2, as an EXPLICIT gate list.
Determinate replacement for `ShiClassQMAAmp.ampFan2`; the injectivity argument is the one
inlined there. -/
noncomputable def ampFan2X (n w a : ℕ) :
    Layered (n + (3 * w + ((2 * n + 3 * a + 3) + 1))) :=
  fanEmbCirc n (n + (3 * w + ((2 * n + 3 * a + 3) + 1)))
    (ShiClassQMAAmp.ampG2 n w a)
    (by
      intro x y he
      have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
      have h2 : ShiClassQMAAmp.ampFanEmb n (n + (w + (a + 1))) (n + (w + (a + 1)))
            (by omega) (by omega) x
          = ShiClassQMAAmp.ampFanEmb n (n + (w + (a + 1))) (n + (w + (a + 1)))
            (by omega) (by omega) y :=
        hb.injective he
      have hx := x.isLt
      have hy := y.isLt
      have h : ShiClassQMAAmp.ampFanVal n (n + (w + (a + 1))) x.val
          = ShiClassQMAAmp.ampFanVal n (n + (w + (a + 1))) y.val := congrArg Fin.val h2
      apply Fin.val_injective
      simp only [ShiClassQMAAmp.ampFanVal] at h
      split_ifs at h <;> omega)

/-- The one-layer fan-out copying the input block into copy 3, as an EXPLICIT gate list.
Determinate replacement for `ShiClassQMAAmp.ampFan3`; the injectivity argument is the one
inlined there. -/
noncomputable def ampFan3X (n w a : ℕ) :
    Layered (n + (3 * w + ((2 * n + 3 * a + 3) + 1))) :=
  fanEmbCirc n (n + (3 * w + ((2 * n + 3 * a + 3) + 1)))
    (ShiClassQMAAmp.ampG3 n w a)
    (by
      intro x y he
      have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
      have h2 : ShiClassQMAAmp.ampFanEmb n (n + (w + (a + 1))) (2 * (n + (w + (a + 1))))
            (by omega) (by omega) x
          = ShiClassQMAAmp.ampFanEmb n (n + (w + (a + 1))) (2 * (n + (w + (a + 1))))
            (by omega) (by omega) y :=
        hb.injective he
      have hx := x.isLt
      have hy := y.isLt
      have h : ShiClassQMAAmp.ampFanVal n (2 * (n + (w + (a + 1)))) x.val
          = ShiClassQMAAmp.ampFanVal n (2 * (n + (w + (a + 1)))) y.val := congrArg Fin.val h2
      apply Fin.val_injective
      simp only [ShiClassQMAAmp.ampFanVal] at h
      split_ifs at h <;> omega)

/-- The 111-layer majority readout onto the scratch wire, as an EXPLICIT gate list: three
`ShiExplicitCirc.toffCirc` Toffolis at the three copies' images of `v` and the scratch wire.
Determinate replacement for `ShiClassQMAAmp.ampRead`; the six distinctness arguments are the
ones inlined there. -/
noncomputable def ampReadX (n w a : ℕ) (v : Fin (n + (w + (a + 1)))) :
    Layered (n + (3 * w + ((2 * n + 3 * a + 3) + 1))) :=
  ShiExplicitCirc.readCirc
    (ShiClassQMAAmp.ampE n w a 0 (by omega) v)
    (ShiClassQMAAmp.ampE n w a (n + (w + (a + 1))) (by omega) v)
    (ShiClassQMAAmp.ampE n w a (2 * (n + (w + (a + 1)))) (by omega) v)
    (ShiClassQMAAmp.ampScr n w a)
    (by
      intro he
      have hv := v.isLt
      have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
      have h2 : ShiClassQMAAmp.ampEmb (n + (w + (a + 1))) 0 (by omega) v
          = ShiClassQMAAmp.ampEmb (n + (w + (a + 1))) (n + (w + (a + 1))) (by omega) v :=
        hb.injective he
      have h3 : 0 + v.val = (n + (w + (a + 1))) + v.val := congrArg Fin.val h2
      omega)
    (by
      intro he
      have hv := v.isLt
      have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
      have h2 : ShiClassQMAAmp.ampEmb (n + (w + (a + 1))) 0 (by omega) v
          = ShiClassQMAAmp.ampEmb (n + (w + (a + 1))) (2 * (n + (w + (a + 1)))) (by omega) v :=
        hb.injective he
      have h3 : 0 + v.val = 2 * (n + (w + (a + 1))) + v.val := congrArg Fin.val h2
      omega)
    (by
      intro he
      have hv := v.isLt
      have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
      have h2 : ShiClassQMAAmp.ampEmb (n + (w + (a + 1))) (n + (w + (a + 1))) (by omega) v
          = ShiClassQMAAmp.ampEmb (n + (w + (a + 1))) (2 * (n + (w + (a + 1)))) (by omega) v :=
        hb.injective he
      have h3 : (n + (w + (a + 1))) + v.val = 2 * (n + (w + (a + 1))) + v.val :=
        congrArg Fin.val h2
      omega)
    (by
      intro he
      have hv := v.isLt
      have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
      have h2 : ShiClassQMAAmp.ampEmb (n + (w + (a + 1))) 0 (by omega) v
          = (⟨3 * (n + (w + (a + 1))), by omega⟩ :
              Fin (3 * (n + (w + (a + 1))) + 1)) := hb.injective he
      have h3 : 0 + v.val = 3 * (n + (w + (a + 1))) := congrArg Fin.val h2
      omega)
    (by
      intro he
      have hv := v.isLt
      have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
      have h2 : ShiClassQMAAmp.ampEmb (n + (w + (a + 1))) (n + (w + (a + 1))) (by omega) v
          = (⟨3 * (n + (w + (a + 1))), by omega⟩ :
              Fin (3 * (n + (w + (a + 1))) + 1)) := hb.injective he
      have h3 : (n + (w + (a + 1))) + v.val = 3 * (n + (w + (a + 1))) :=
        congrArg Fin.val h2
      omega)
    (by
      intro he
      have hv := v.isLt
      have hb := (Classical.choose_spec (ShiShallow.exists_layout_bijection n w a)).1
      have h2 : ShiClassQMAAmp.ampEmb (n + (w + (a + 1))) (2 * (n + (w + (a + 1))))
            (by omega) v
          = (⟨3 * (n + (w + (a + 1))), by omega⟩ :
              Fin (3 * (n + (w + (a + 1))) + 1)) := hb.injective he
      have h3 : 2 * (n + (w + (a + 1))) + v.val = 3 * (n + (w + (a + 1))) :=
        congrArg Fin.val h2
      omega)

/-- The amplified circuit as a DETERMINED gate list: the same six-way concatenation as
`ShiClassQMAAmp.ampCirc` -- two fan-outs, three embedded copies of `F.circ n`, then the
majority readout at the three copies' output wires -- with the explicit circuits in place of
the three chosen ones.  The three `ShiEmbed.embedCirc` factors and their injectivity arguments
are exactly those of `ampCirc`. -/
noncomputable def ampCircX (F : ShiClassQMA.QMAFamily) (n : ℕ) :
    Layered (n + (3 * F.wit n + ((2 * n + 3 * F.anc n + 3) + 1))) :=
  ampFan2X n (F.wit n) (F.anc n)
    ++ ampFan3X n (F.wit n) (F.anc n)
    ++ ShiEmbed.embedCirc (ShiClassQMAAmp.ampE n (F.wit n) (F.anc n) 0 (by omega))
      (by
        intro x y he
        have hb :=
          (Classical.choose_spec
            (ShiShallow.exists_layout_bijection n (F.wit n) (F.anc n))).1
        have h2 : ShiClassQMAAmp.ampEmb (n + (F.wit n + (F.anc n + 1))) 0 (by omega) x
            = ShiClassQMAAmp.ampEmb (n + (F.wit n + (F.anc n + 1))) 0 (by omega) y :=
          hb.injective he
        have h3 : 0 + x.val = 0 + y.val := congrArg Fin.val h2
        exact Fin.val_injective (by omega)) (F.circ n)
    ++ ShiEmbed.embedCirc
      (ShiClassQMAAmp.ampE n (F.wit n) (F.anc n) (n + (F.wit n + (F.anc n + 1))) (by omega))
      (by
        intro x y he
        have hb :=
          (Classical.choose_spec
            (ShiShallow.exists_layout_bijection n (F.wit n) (F.anc n))).1
        have h2 : ShiClassQMAAmp.ampEmb (n + (F.wit n + (F.anc n + 1)))
              (n + (F.wit n + (F.anc n + 1))) (by omega) x
            = ShiClassQMAAmp.ampEmb (n + (F.wit n + (F.anc n + 1)))
              (n + (F.wit n + (F.anc n + 1))) (by omega) y := hb.injective he
        have h3 : (n + (F.wit n + (F.anc n + 1))) + x.val
            = (n + (F.wit n + (F.anc n + 1))) + y.val := congrArg Fin.val h2
        exact Fin.val_injective (by omega)) (F.circ n)
    ++ ShiEmbed.embedCirc
      (ShiClassQMAAmp.ampE n (F.wit n) (F.anc n)
        (2 * (n + (F.wit n + (F.anc n + 1)))) (by omega))
      (by
        intro x y he
        have hb :=
          (Classical.choose_spec
            (ShiShallow.exists_layout_bijection n (F.wit n) (F.anc n))).1
        have h2 : ShiClassQMAAmp.ampEmb (n + (F.wit n + (F.anc n + 1)))
              (2 * (n + (F.wit n + (F.anc n + 1)))) (by omega) x
            = ShiClassQMAAmp.ampEmb (n + (F.wit n + (F.anc n + 1)))
              (2 * (n + (F.wit n + (F.anc n + 1)))) (by omega) y := hb.injective he
        have h3 : 2 * (n + (F.wit n + (F.anc n + 1))) + x.val
            = 2 * (n + (F.wit n + (F.anc n + 1))) + y.val := congrArg Fin.val h2
        exact Fin.val_injective (by omega)) (F.circ n)
    ++ ampReadX n (F.wit n) (F.anc n) (F.out n)

/-- The threefold majority amplifier with a DETERMINED circuit: the fields are exactly those
of `ShiClassQMAAmp.ampFamily`, except that the circuit is `ampCircX` and hence an explicit
gate list on every input length. -/
noncomputable def ampFamilyX (F : ShiClassQMA.QMAFamily) : ShiClassQMA.QMAFamily :=
  { anc := fun n => 2 * n + 3 * F.anc n + 3
    wit := fun n => 3 * F.wit n
    circ := ampCircX F
    out := fun n => ShiClassQMAAmp.ampScr n (F.wit n) (F.anc n) }

end ShiClassQMAAmpX
