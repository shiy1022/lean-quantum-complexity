-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `PvsNP.polyTime_composition_and_alphabet_transport`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_PvsNP_polyTime_composition_and_alphabet_transport`. The real proof is on prove2.me.
import Definitions.Def_PvsNP
import Theorems.Thm_PvsNP_polyTimeComputable_comp
import Theorems.Thm_ShiTM_comp_outputsInTime

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Turing

namespace PvsNP

theorem polyTime_composition_and_alphabet_transport :
    -- (1) GENERAL POLYNOMIAL-TIME COMPOSITION, arbitrary and DIFFERENT alphabets on all three
    -- sides, with the composite's time polynomial exhibited.  `q` bounds the length of the
    -- intermediate encoding; `z` supplies the dummy symbol `ShiTM2.comp` demands.
    (∀ (α β γ αΓ βΓ γΓ : Type) (eα : α → List αΓ) (eβ : β → List βΓ) (eγ : γ → List γΓ)
        (f : α → β) (g : β → γ) (q : Polynomial ℕ) (z : βΓ)
        (c₁ : Turing.TM2ComputableInPolyTime eα eβ f)
        (c₂ : Turing.TM2ComputableInPolyTime eβ eγ g),
        (∀ a : α, (eβ (f a)).length ≤ q.eval (eα a).length) →
        ∃ c : Turing.TM2ComputableInPolyTime eα eγ (g ∘ f),
          c.time = c₁.time + (Polynomial.C 2 * q + Polynomial.C 2) + c₂.time.comp q)
  ∧ -- (2) INPUT TRANSPORT.  Relabelling the input alphabet along a bijection and reindexing
    -- the domain is free: same machine, same time polynomial.
    (∀ (α α' β αΓ αΓ' βΓ : Type) (ea : α → List αΓ) (ea' : α' → List αΓ')
        (eb : β → List βΓ) (u : α' → α) (e : αΓ ≃ αΓ') (f : α → β),
        (∀ a' : α', ea' a' = List.map e (ea (u a'))) →
        Turing.TM2ComputableInPolyTime ea eb f →
        Nonempty (Turing.TM2ComputableInPolyTime ea' eb (f ∘ u)))
  ∧ -- (3) OUTPUT TRANSPORT, likewise free.
    (∀ (α β β' αΓ βΓ βΓ' : Type) (ea : α → List αΓ) (eb : β → List βΓ)
        (eb' : β' → List βΓ') (v : β → β') (d : βΓ ≃ βΓ') (f : α → β),
        (∀ b : β, eb' (v b) = List.map d (eb b)) →
        Turing.TM2ComputableInPolyTime ea eb f →
        Nonempty (Turing.TM2ComputableInPolyTime ea eb' (v ∘ f)))
  ∧ -- (4) A DECIDER IS A STRING FUNCTION: the two `Prop`s are equivalent.
    (∀ χ : PvsNP.Str → Bool,
        PvsNP.PolyTimeDecider χ ↔ PvsNP.PolyTimeComputable (fun w : PvsNP.Str => [χ w]))
  ∧ -- (5) UNCONDITIONAL plain-string chaining: no length hypothesis is needed, because this
    -- routes through the proved `PvsNP.polyTimeComputable_comp`.
    (∀ (χ : PvsNP.Str → Bool) (g : PvsNP.Str → PvsNP.Str),
        PvsNP.PolyTimeDecider χ → PvsNP.PolyTimeComputable g →
        PvsNP.PolyTimeDecider (fun w : PvsNP.Str => χ (g w)))
  ∧ -- (6) CHECKER PREPROCESSING: any poly-time transducer on the TAGGED alphabet may be
    -- prepended to any checker, with the composite's time polynomial exhibited.
    (∀ (R : PvsNP.Str × PvsNP.Str → Bool)
        (T : PvsNP.Str × PvsNP.Str → PvsNP.Str × PvsNP.Str) (q : Polynomial ℕ)
        (c₁ : Turing.TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair T)
        (c₂ : Turing.TM2ComputableInPolyTime PvsNP.encodePair Computability.encodeBool R),
        (∀ p : PvsNP.Str × PvsNP.Str,
          (PvsNP.encodePair (T p)).length ≤ q.eval (PvsNP.encodePair p).length) →
        ∃ c : Turing.TM2ComputableInPolyTime PvsNP.encodePair Computability.encodeBool
            (fun p : PvsNP.Str × PvsNP.Str => R (T p)),
          c.time = c₁.time + (Polynomial.C 2 * q + Polynomial.C 2) + c₂.time.comp q)
  ∧ -- (7) THE ALPHABET BRIDGE: one tagged-to-plain transducer turns EVERY plain-string
    -- polynomial-time decision procedure into a polynomial-time checking relation.
    (∀ (u : PvsNP.Str × PvsNP.Str → PvsNP.Str) (χ : PvsNP.Str → Bool) (q : Polynomial ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair
          (id : PvsNP.Str → PvsNP.Str) u) →
        PvsNP.PolyTimeDecider χ →
        (∀ p : PvsNP.Str × PvsNP.Str,
          (u p).length ≤ q.eval (PvsNP.encodePair p).length) →
        PvsNP.PolyTimeChecker (fun p : PvsNP.Str × PvsNP.Str => χ (u p)))
  ∧ -- (8) COMPLEMENT CLOSURE of `PolyTimeChecker`, the instance of (3) at Boolean negation.
    (∀ R : PvsNP.Str × PvsNP.Str → Bool,
        PvsNP.PolyTimeChecker R →
        PvsNP.PolyTimeChecker (fun p : PvsNP.Str × PvsNP.Str => !(R p)))
  ∧ -- (9) SYMBOLWISE INPUT NEGATION closure, the instance of (2) at `Sum.map not not`.
    (∀ R : PvsNP.Str × PvsNP.Str → Bool,
        PvsNP.PolyTimeChecker R →
        PvsNP.PolyTimeChecker
          (fun p : PvsNP.Str × PvsNP.Str => R (p.1.map not, p.2.map not)))
  ∧ -- (10) NON-VACUITY: (1) applied to two identity machines really does produce a composite,
    -- and its time polynomial evaluates as the formula predicts.
    (∃ c : Turing.TM2ComputableInPolyTime Computability.encodeBool Computability.encodeBool
        ((id : Bool → Bool) ∘ (id : Bool → Bool)),
      c.time.eval 1 = 6 ∧ c.time.eval 2 = 8)
  ∧ PvsNP.PolyTimeComputable (id : PvsNP.Str → PvsNP.Str)
  ∧ Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair
      (id : PvsNP.Str × PvsNP.Str → PvsNP.Str × PvsNP.Str)) := by
  sorry

end PvsNP
