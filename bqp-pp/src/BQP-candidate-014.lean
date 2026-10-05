import Definitions.Def_ShiBQP_Core
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiBQP_one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one

namespace BQPReferenceValidation.Source14
/-
PHI-M5.  THE TARGET: `ShiBQP.layer_stripping_encoding_transducer`.

WHAT THIS SLICE IS.  THE WELD, and nothing else.  `PHI-Ac` pinned the transducer by EIGHT
BINDERS and NINETEEN EQUATIONS and exhibited closed functions satisfying all nineteen;
`PHI-B` lifted the token-level transduction law to the REAL encodings; `PHI-M1` to `PHI-M3`
built the machine and ran it on every word; `PHI-M4` packaged that run as
`PvsNP.PolyTimeComputable`.  Every one of those is a statement about the SAME pinned `Φ`, held
fixed across the whole chain precisely so that this file can instantiate the binder list ONCE
(RESUME 512).  That instantiation is what happens here, and the nineteen equations are
discharged at it by `PHI-Ac`'s own conjunct (5), which is why the existential seam of RESUME
508 had to be closed before any machine slice was written.

WHY THE INSTANTIATION IS THE WHOLE POINT.  RESUME 508's counterexample is real: `Ψ s := Φ s`
on the image of the layered renderer and `Ψ s := []` elsewhere satisfies the transduction law
and the length law, yet differs from `Φ` at `[false]`.  So `∃ Φ₁, transduction` and
`∃ Φ₂, PolyTimeComputable` cannot be merged.  Here BOTH conjuncts of the target are proved of
ONE witness -- the `Φ` of the exhibited instance -- because `PHI-B` and the machine chain are
both consumed AT THAT INSTANCE, under the same nineteen equations.

THE FIVE HYPOTHESES, AND WHERE EACH COMES FROM.
* `hFlat` -- the `encFlat` contract of `wave30 ENCFLAT_CONTRACT.md`, character for character,
  so this slice welds with `COMPILE-FLATb`.  `encFlat` is a BINDER, never defined here.
* `hAc` -- `PHI-Ac` conjunct (A), the pinned-binder restatement.  Only its conjuncts (2) and
  (4) are used; conjunct (3) is not needed once the machine chain is in hand.
* `hSat` -- `PHI-Ac` conjunct (5), reproduced in full.  This is the ONLY source of a concrete
  witness, and the reason the hypothesis block of `hAc` is not an empty premise.
* `hB` -- `PHI-B` conjunct (1), the lift to the real `encNat`, `encInstr`, `encLayer`,
  `encCirc` and `encFamilyAt`.  It needs NEITHER `WellFormed` NOR `PolyBounded`, so the
  transduction law delivered below holds for an ARBITRARY family.
* `hPTC` -- `PHI-M3` conjunct (6) composed with `PHI-M4` conjunct (1), stated at exactly
  `PHI-Ac`'s nineteen equations.  THIS IS THE ONE HYPOTHESIS THAT IS A COMPOSITE RATHER THAN A
  SINGLE ACCEPTED CONJUNCT, and the report says so: `PHI-M3` (6) carries ten antecedents of its
  own -- `PHI-Ac` (3), `PHI-M2` (6a) and (6d), `initList_haltList_laws`, the single-stack drain
  run theorem, and `PHI-M1` (6) to (9) -- which are facts about the machine `PHI-M3` exhibits
  and cannot be restated here without also restating that machine's thirty-label transition
  table.  Discharging them is the machine-level weld, not this slice's business.

WHAT IS PROVED, NOT ASSUMED, HERE.  That the exhibited instance satisfies all nineteen
equations (by `hSat`); that `hAc` therefore delivers the transduction and length laws AT that
instance; that `hB` therefore delivers `Φ (encFamilyAt F n) = encFlat F n` over the real
encodings for EVERY family and EVERY input length; and that the SAME `Φ` is the one `hPTC`
speaks about.  The conclusion is the target's exact shape.

GOTCHA 300 CLOSES WITH IT.  RESUME 496 records that gotcha 300 -- "`Uniform` does not transfer
to the flattened family, because nothing shows `encFamilyAt G n` is poly-time computable from
`encFamilyAt F n`" -- is the same gap under another name.  A poly-time `Φ` carrying the layered
encoding to the flat one is exactly the missing re-encoder, and composition with
`PvsNP.PolyTimeComputable` (`Thm_PvsNP_polyTimeComputable_comp`, already used at `READ-1c`)
then transports `Uniform`.  The composition step is NOT performed here -- this slice states the
transducer, not the transfer -- so gotcha 300 closes in the sense that its missing ingredient
now exists, with one named one-line consumer left to write.

GOTCHAS OBSERVED.  No `namespace` line (468); `open ShiShallow ShiClass ShiBQP` is legal because
this is a `Definitions`-tier file.  `++` is LEFT-ASSOCIATIVE and the contract's right-hand side
is reproduced with its own parenthesisation, unchanged (ENCFLAT_CONTRACT consumption note).  No
abbreviation joined by a slash to a hyphenated name in any comment (499a).  Nothing is keyed on
`Function.iterate`, so 522(b) does not arise.  `F.anc n` is never pinned numerically (502).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open ShiShallow ShiClass ShiBQP

theorem _root_.BQPReferenceValidation.candidate14 :
    ∀ (encFlat : Family → ℕ → PvsNP.Str),
      -- the `encFlat` contract, character for character
      (∀ (F : Family) (n : ℕ),
        encFlat F n
          = encNat (F.anc n) ++ encNat ((F.out n : ℕ))
            ++ encNat (((F.circ n).flatten).length)
            ++ ((((F.circ n).flatten).map encInstr).flatten)) →
      -- `PHI-Ac` conjunct (A): the pinned-binder transducer laws
      (∀ (E : List ℕ → List Bool) (bump : List ℕ → List ℕ) (upk : List Bool → List ℕ)
          (ar : ℕ → ℕ) (pg : ℕ → List ℕ → List (List ℕ) × List ℕ)
          (sl : ℕ → List ℕ → List (List ℕ)) (pt : List ℕ → List ℕ)
          (Φ : List Bool → List Bool),
        E [] = [] →
        (∀ (c : ℕ) (cs : List ℕ),
          E (c :: cs) = List.replicate c true ++ false :: E cs) →
        bump [] = [] →
        (∀ (k : ℕ) (t : List ℕ), bump (k :: t) = ((k + 1) :: t)) →
        upk [] = [] →
        (∀ r : List Bool, upk (false :: r) = 0 :: upk r) →
        (∀ r : List Bool, upk (true :: r) = bump (upk r)) →
        (∀ t : ℕ, ar t = if t = 4 then 3 else 2) →
        (∀ ts : List ℕ, pg 0 ts = ([], ts)) →
        (∀ k : ℕ, pg (k + 1) [] = ([], [])) →
        (∀ (k t : ℕ) (u : List ℕ),
          pg (k + 1) (t :: u)
            = (if ar t ≤ u.length + 1 then
                ((t :: u).take (ar t) :: (pg k ((t :: u).drop (ar t))).1,
                  (pg k ((t :: u).drop (ar t))).2)
              else ([], []))) →
        (∀ ts : List ℕ, sl 0 ts = []) →
        (∀ k : ℕ, sl (k + 1) [] = []) →
        (∀ (k l : ℕ) (u : List ℕ),
          sl (k + 1) (l :: u) = (pg l u).1 ++ sl k (pg l u).2) →
        pt [] = [] →
        (∀ a : ℕ, pt [a] = [a]) →
        (∀ a b : ℕ, pt [a, b] = [a, b]) →
        (∀ (a b n : ℕ) (r : List ℕ),
          pt (a :: b :: n :: r) = a :: b :: (sl n r).length :: (sl n r).flatten) →
        (∀ s : List Bool, Φ s = E (pt (upk s))) →
        ((E [] = []
            ∧ (∀ (c : ℕ) (cs : List ℕ),
                E (c :: cs) = List.replicate c true ++ false :: E cs))
          ∧ (∀ (anc out : ℕ) (c : List (List (List ℕ))),
              (∀ q ∈ c, ∀ rec ∈ q,
                (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])) →
              Φ (E (anc :: out :: c.length
                      :: (c.map (fun q => q.length :: q.flatten)).flatten))
                = E (anc :: out :: c.flatten.length :: c.flatten.flatten))
          ∧ (∀ s : List Bool, (Φ s).length ≤ s.length)
          ∧ (∀ (anc out : ℕ) (c : List (List (List ℕ))),
              (E (anc :: out :: c.length
                    :: (c.map (fun q => q.length :: q.flatten)).flatten)).length
                = (E (anc :: out :: c.flatten.length :: c.flatten.flatten)).length
                  + 2 * c.length))) →
      -- `PHI-Ac` conjunct (5): closed functions satisfying every one of the nineteen equations
      (∃ (E : List ℕ → List Bool) (bump : List ℕ → List ℕ) (upk : List Bool → List ℕ)
          (ar : ℕ → ℕ) (pg : ℕ → List ℕ → List (List ℕ) × List ℕ)
          (sl : ℕ → List ℕ → List (List ℕ)) (pt : List ℕ → List ℕ)
          (Φ : List Bool → List Bool),
        E [] = []
        ∧ (∀ (c : ℕ) (cs : List ℕ),
            E (c :: cs) = List.replicate c true ++ false :: E cs)
        ∧ bump [] = []
        ∧ (∀ (k : ℕ) (t : List ℕ), bump (k :: t) = ((k + 1) :: t))
        ∧ upk [] = []
        ∧ (∀ r : List Bool, upk (false :: r) = 0 :: upk r)
        ∧ (∀ r : List Bool, upk (true :: r) = bump (upk r))
        ∧ (∀ t : ℕ, ar t = if t = 4 then 3 else 2)
        ∧ (∀ ts : List ℕ, pg 0 ts = ([], ts))
        ∧ (∀ k : ℕ, pg (k + 1) [] = ([], []))
        ∧ (∀ (k t : ℕ) (u : List ℕ),
            pg (k + 1) (t :: u)
              = (if ar t ≤ u.length + 1 then
                  ((t :: u).take (ar t) :: (pg k ((t :: u).drop (ar t))).1,
                    (pg k ((t :: u).drop (ar t))).2)
                else ([], [])))
        ∧ (∀ ts : List ℕ, sl 0 ts = [])
        ∧ (∀ k : ℕ, sl (k + 1) [] = [])
        ∧ (∀ (k l : ℕ) (u : List ℕ),
            sl (k + 1) (l :: u) = (pg l u).1 ++ sl k (pg l u).2)
        ∧ pt [] = []
        ∧ (∀ a : ℕ, pt [a] = [a])
        ∧ (∀ a b : ℕ, pt [a, b] = [a, b])
        ∧ (∀ (a b n : ℕ) (r : List ℕ),
            pt (a :: b :: n :: r) = a :: b :: (sl n r).length :: (sl n r).flatten)
        ∧ (∀ s : List Bool, Φ s = E (pt (upk s)))
        ∧ Φ (E [0, 0, 0]) = E [0, 0, 0]
        ∧ Φ (E [0, 0, 1, 1, 0, 0]) = E [0, 0, 1, 0, 0]
        ∧ Φ (E [0, 0, 2, 2, 0, 0, 1, 1, 1, 4, 0, 1]) = E [0, 0, 3, 0, 0, 1, 1, 4, 0, 1]
        ∧ (E [0, 0, 2, 2, 0, 0, 1, 1, 1, 4, 0, 1]).length = 24
        ∧ (E [0, 0, 3, 0, 0, 1, 1, 4, 0, 1]).length = 20) →
      -- `PHI-B` conjunct (1): the lift to the real encodings
      (∀ (E : List ℕ → List Bool) (Φ : List Bool → List Bool)
          (encFlat' : Family → ℕ → PvsNP.Str),
        E [] = [] →
        (∀ (c : ℕ) (cs : List ℕ),
          E (c :: cs) = List.replicate c true ++ false :: E cs) →
        (∀ (anc out : ℕ) (c : List (List (List ℕ))),
          (∀ q ∈ c, ∀ rec ∈ q,
            (∃ t i : ℕ, t < 4 ∧ rec = [t, i]) ∨ (∃ i j : ℕ, rec = [4, i, j])) →
          Φ (E (anc :: out :: c.length
                  :: (c.map (fun q => q.length :: q.flatten)).flatten))
            = E (anc :: out :: c.flatten.length :: c.flatten.flatten)) →
        (∀ (anc out : ℕ) (c : List (List (List ℕ))),
          (E (anc :: out :: c.length
                :: (c.map (fun q => q.length :: q.flatten)).flatten)).length
            = (E (anc :: out :: c.flatten.length :: c.flatten.flatten)).length
              + 2 * c.length) →
        (∀ (F : Family) (n : ℕ),
          encFlat' F n
            = encNat (F.anc n) ++ encNat ((F.out n : ℕ))
              ++ encNat (((F.circ n).flatten).length)
              ++ ((((F.circ n).flatten).map encInstr).flatten)) →
        ∀ (F : Family) (n : ℕ),
          Φ (encFamilyAt F n) = encFlat' F n
          ∧ (encFamilyAt F n).length
              = (encFlat' F n).length + 2 * (F.circ n).length) →
      -- `PHI-M3` conjunct (6) composed with `PHI-M4` conjunct (1): the machine, packaged
      (∀ (E : List ℕ → List Bool) (bump : List ℕ → List ℕ) (upk : List Bool → List ℕ)
          (ar : ℕ → ℕ) (pg : ℕ → List ℕ → List (List ℕ) × List ℕ)
          (sl : ℕ → List ℕ → List (List ℕ)) (pt : List ℕ → List ℕ)
          (Φ : List Bool → List Bool),
        E [] = [] →
        (∀ (c : ℕ) (cs : List ℕ),
          E (c :: cs) = List.replicate c true ++ false :: E cs) →
        bump [] = [] →
        (∀ (k : ℕ) (t : List ℕ), bump (k :: t) = ((k + 1) :: t)) →
        upk [] = [] →
        (∀ r : List Bool, upk (false :: r) = 0 :: upk r) →
        (∀ r : List Bool, upk (true :: r) = bump (upk r)) →
        (∀ t : ℕ, ar t = if t = 4 then 3 else 2) →
        (∀ ts : List ℕ, pg 0 ts = ([], ts)) →
        (∀ k : ℕ, pg (k + 1) [] = ([], [])) →
        (∀ (k t : ℕ) (u : List ℕ),
          pg (k + 1) (t :: u)
            = (if ar t ≤ u.length + 1 then
                ((t :: u).take (ar t) :: (pg k ((t :: u).drop (ar t))).1,
                  (pg k ((t :: u).drop (ar t))).2)
              else ([], []))) →
        (∀ ts : List ℕ, sl 0 ts = []) →
        (∀ k : ℕ, sl (k + 1) [] = []) →
        (∀ (k l : ℕ) (u : List ℕ),
          sl (k + 1) (l :: u) = (pg l u).1 ++ sl k (pg l u).2) →
        pt [] = [] →
        (∀ a : ℕ, pt [a] = [a]) →
        (∀ a b : ℕ, pt [a, b] = [a, b]) →
        (∀ (a b n : ℕ) (r : List ℕ),
          pt (a :: b :: n :: r) = a :: b :: (sl n r).length :: (sl n r).flatten) →
        (∀ s : List Bool, Φ s = E (pt (upk s))) →
        PvsNP.PolyTimeComputable Φ) →
      -- THE TARGET.  ONE transducer, carrying BOTH properties.
      ∃ Φ : PvsNP.Str → PvsNP.Str,
        (∀ (F : Family) (n : ℕ), Φ (encFamilyAt F n) = encFlat F n)
        ∧ PvsNP.PolyTimeComputable Φ := by
  intro encFlat hFlat hAc hSat hB hPTC
  -- THE ONE INSTANTIATION (RESUME 512).  The exhibited instance of `PHI-Ac` (5) supplies the
  -- eight functions; the nineteen equations come with it, and every consumer below is fed
  -- exactly those nineteen, so all three chains speak about the SAME `Φ`.
  obtain ⟨E, bump, upk, ar, pg, sl, pt, Φ,
    hE0, hE1, hb0, hb1, hu0, huF, huT, har,
    hpg0, hpgN, hpgC, hsl0, hslN, hslC,
    hpt0, hpt1, hpt2, hptL, hPhi, -, -, -, -, -⟩ := hSat
  -- the pinned transducer laws, AT that instance
  obtain ⟨-, hTrans, -, hLen⟩ :=
    hAc E bump upk ar pg sl pt Φ hE0 hE1 hb0 hb1 hu0 huF huT har
      hpg0 hpgN hpgC hsl0 hslN hslC hpt0 hpt1 hpt2 hptL hPhi
  -- the lift to the real encodings, AT that instance
  have hlift : ∀ (F : Family) (n : ℕ),
      Φ (encFamilyAt F n) = encFlat F n
      ∧ (encFamilyAt F n).length
          = (encFlat F n).length + 2 * (F.circ n).length :=
    hB E Φ encFlat hE0 hE1 hTrans hLen hFlat
  -- the machine, AT that instance
  have hpoly : PvsNP.PolyTimeComputable Φ :=
    hPTC E bump upk ar pg sl pt Φ hE0 hE1 hb0 hb1 hu0 huF huT har
      hpg0 hpgN hpgC hsl0 hslN hslC hpt0 hpt1 hpt2 hptL hPhi
  exact ⟨Φ, fun F n => (hlift F n).1, hpoly⟩

end BQPReferenceValidation.Source14

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate14
    let target ← getConstInfo ``ShiBQP.one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate14
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one; axioms {axioms}"
