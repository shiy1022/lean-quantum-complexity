-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `PvsNP.tagged_transducers_untaggers_and_projections`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_PvsNP_tagged_transducers_untaggers_and_projections`. The real proof is on prove2.me.
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_PvsNP
import Theorems.Thm_ShiTM_initList_haltList_laws
import Theorems.Thm_ShiTM_outputsInTime_of_run_to_halt

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Turing Turing.TM2

namespace PvsNP

theorem tagged_transducers_untaggers_and_projections :
    -- (1) THE GENERAL SYMBOLWISE TRANSDUCER, with a polynomial-time certificate, over an
    -- ARBITRARY finite output alphabet and an ARBITRARY target encoding: whenever `eb ∘ f`
    -- is `s ↦ (encodePair s).flatMap φ`, the function `f` is polynomial-time computable out
    -- of the tagged alphabet, with the time polynomial exhibited.
    (∀ (Γo : Type) [Inhabited Γo] [Fintype Γo] (φ : Bool ⊕ Bool → List Γo) (M : ℕ),
        (∀ c, (φ c).length ≤ M) →
        ∀ (β : Type) (eb : β → List Γo) (f : PvsNP.Str × PvsNP.Str → β),
          (∀ p, eb (f p) = (PvsNP.encodePair p).flatMap φ) →
          ∃ c : Turing.TM2ComputableInPolyTime PvsNP.encodePair eb f,
            c.time = Polynomial.C (M + 1) * Polynomial.X + Polynomial.C 3)
  ∧ -- (2) THE UNTAGGER FAMILY: every symbolwise drop-or-keep rule on the tagged alphabet is
    -- a polynomial-time transducer INTO the plain alphabet.  This is exactly the hypothesis
    -- `Nonempty (TM2ComputableInPolyTime encodePair id u)` of the alphabet bridge.
    (∀ ψ : Bool ⊕ Bool → Option Bool,
        Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair
          (id : PvsNP.Str → PvsNP.Str)
          (fun p : PvsNP.Str × PvsNP.Str => (PvsNP.encodePair p).filterMap ψ)))
  ∧ -- (3) the two projections, in the shape the bridge consumes
    (Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair (id : PvsNP.Str → PvsNP.Str)
        (fun p : PvsNP.Str × PvsNP.Str => p.1))
      ∧ Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair
          (id : PvsNP.Str → PvsNP.Str) (fun p : PvsNP.Str × PvsNP.Str => p.2)))
  ∧ -- (4) THE OUTPUT-LENGTH BOUND, which discharges the intermediate-length hypothesis `q`
    -- of the composition lemma at `q = X`.
    (∀ (ψ : Bool ⊕ Bool → Option Bool) (p : PvsNP.Str × PvsNP.Str),
        ((PvsNP.encodePair p).filterMap ψ).length ≤ (PvsNP.encodePair p).length)
  ∧ -- (5) NON-VACUITY at a length-TWO rule: the injective tagged-to-plain pairing
    -- `inl b ↦ 0b`, `inr b ↦ 1b`, which is not a filter-map, together with its value at a
    -- concrete pair.
    (Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair (id : PvsNP.Str → PvsNP.Str)
        (fun p : PvsNP.Str × PvsNP.Str =>
          (PvsNP.encodePair p).flatMap (Sum.elim (fun b => [false, b]) (fun b => [true, b]))))
      ∧ (PvsNP.encodePair ([true], [false])).flatMap
          (Sum.elim (fun b => [false, b]) (fun b => [true, b]))
          = [false, true, true, false]) := by
  sorry

end PvsNP
