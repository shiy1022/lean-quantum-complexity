-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `PvsNP.combined_checker_is_polynomial_time_via_the_lossless_pairing`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_PvsNP_combined_checker_is_polynomial_time_via_the_lossless_pairing`. The real proof is on prove2.me.
import Definitions.Def_PvsNP

set_option autoImplicit false
set_option maxHeartbeats 1600000

open PvsNP Turing

/-! ### The lossless tagged-to-plain pairing and its decoder -/

namespace PvsNP

theorem combined_checker_is_polynomial_time_via_the_lossless_pairing
    (hT1 : ∀ (Go : Type) [Inhabited Go] [Fintype Go] (φ : Bool ⊕ Bool → List Go) (M : ℕ),
        (∀ c, (φ c).length ≤ M) →
        ∀ (β : Type) (eb : β → List Go) (f : PvsNP.Str × PvsNP.Str → β),
          (∀ p, eb (f p) = (PvsNP.encodePair p).flatMap φ) →
          ∃ c : Turing.TM2ComputableInPolyTime PvsNP.encodePair eb f,
            c.time = Polynomial.C (M + 1) * Polynomial.X + Polynomial.C 3)
    (hB5 : ∀ (χ : PvsNP.Str → Bool) (g : PvsNP.Str → PvsNP.Str),
        PvsNP.PolyTimeDecider χ → PvsNP.PolyTimeComputable g →
        PvsNP.PolyTimeDecider (fun w : PvsNP.Str => χ (g w)))
    (hB7 : ∀ (u : PvsNP.Str × PvsNP.Str → PvsNP.Str) (χ : PvsNP.Str → Bool)
        (q : Polynomial ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair
          (id : PvsNP.Str → PvsNP.Str) u) →
        PvsNP.PolyTimeDecider χ →
        (∀ p : PvsNP.Str × PvsNP.Str,
          (u p).length ≤ q.eval (PvsNP.encodePair p).length) →
        PvsNP.PolyTimeChecker (fun p : PvsNP.Str × PvsNP.Str => χ (u p))) :
    ∃ (pr : PvsNP.Str × PvsNP.Str → PvsNP.Str)
      (up : PvsNP.Str → PvsNP.Str × PvsNP.Str),
    -- (0) `pr` IS the lossless pairing of TRANSDUCE-2 conjunct (5)
    (∀ p : PvsNP.Str × PvsNP.Str, pr p = (PvsNP.encodePair p).flatMap
        (Sum.elim (fun b => [false, b]) (fun b => [true, b])))
    -- (1) it loses nothing: `up` decodes it
  ∧ (∀ p : PvsNP.Str × PvsNP.Str, up (pr p) = p)
    -- (2) hence it is injective
  ∧ (∀ p q : PvsNP.Str × PvsNP.Str, pr p = pr q → p = q)
    -- (3) and exactly doubles length, so the composition bound holds at `q = C 2 * X`
  ∧ (∀ p : PvsNP.Str × PvsNP.Str, (pr p).length = 2 * (PvsNP.encodePair p).length)
    -- (4) THE GENERAL BRIDGE.  Any bounded-fan-out symbolwise re-encoding of the tagged
    -- pair into a plain string, followed by ANY polynomial-time plain-string decision
    -- procedure, is a polynomial-time checking relation.  No length hypothesis is left
    -- for the consumer: it is discharged here at `q = C M * X`.
  ∧ (∀ (φ : Bool ⊕ Bool → List Bool) (M : ℕ), (∀ c, (φ c).length ≤ M) →
        ∀ (χ : PvsNP.Str → Bool) (Rf : PvsNP.Str × PvsNP.Str → Bool),
          PvsNP.PolyTimeDecider χ →
          (∀ p : PvsNP.Str × PvsNP.Str, Rf p = χ ((PvsNP.encodePair p).flatMap φ)) →
          PvsNP.PolyTimeChecker Rf)
    -- (5) THE INSTANCE AT THE LOSSLESS PAIRING
  ∧ (∀ (χ : PvsNP.Str → Bool) (Rf : PvsNP.Str × PvsNP.Str → Bool),
        PvsNP.PolyTimeDecider χ →
        (∀ p : PvsNP.Str × PvsNP.Str, Rf p = χ (pr p)) →
        PvsNP.PolyTimeChecker Rf)
    -- (6) (5)'s SHAPE HYPOTHESIS IS NO RESTRICTION: every relation whatever factors
    -- through `pr`, so the only real content of (5) is `PolyTimeDecider χ`.
  ∧ (∀ Rf : PvsNP.Str × PvsNP.Str → Bool,
        ∃ χ : PvsNP.Str → Bool, ∀ p : PvsNP.Str × PvsNP.Str, Rf p = χ (pr p))
    -- (7) THE ROUTER FORM: the decision procedure may be preceded by any polynomial-time
    -- plain-string function `g`.  This is the form a DISPATCHING `Rf` takes.
  ∧ (∀ (Rf : PvsNP.Str × PvsNP.Str → Bool) (chi : PvsNP.Str → Bool)
        (g : PvsNP.Str → PvsNP.Str),
        PvsNP.PolyTimeDecider chi → PvsNP.PolyTimeComputable g →
        (∀ p : PvsNP.Str × PvsNP.Str, Rf p = chi (g (pr p))) →
        PvsNP.PolyTimeChecker Rf)
    -- (8) FINITELY-MANY-ARM DISPATCH, with the semantic read-off: a selector `sel` reads a
    -- number off the paired string and `arm` chooses the argument handed to `chi`.
  ∧ (∀ (Rf : PvsNP.Str × PvsNP.Str → Bool) (chi : PvsNP.Str → Bool)
        (sel : PvsNP.Str → ℕ) (arm : ℕ → PvsNP.Str → PvsNP.Str)
        (g : PvsNP.Str → PvsNP.Str),
        PvsNP.PolyTimeDecider chi → PvsNP.PolyTimeComputable g →
        (∀ w : PvsNP.Str, g w = arm (sel w) w) →
        (∀ p : PvsNP.Str × PvsNP.Str, Rf p = chi (g (pr p))) →
        PvsNP.PolyTimeChecker Rf
          ∧ ∀ p : PvsNP.Str × PvsNP.Str, Rf p = chi (arm (sel (pr p)) (pr p)))
    -- (9) THE TWO-ARM INTEGER-COMPARISON DISPATCH in the shape the campaign needs: on the
    -- cases selected by `selB` the combined checker IS the component `chi ∘ cut`, and on
    -- the remaining cases it is the constant gadget `chi w0`.
  ∧ (∀ (Rf : PvsNP.Str × PvsNP.Str → Bool) (chi : PvsNP.Str → Bool)
        (selB : PvsNP.Str → Bool) (cut : PvsNP.Str → PvsNP.Str) (w0 : PvsNP.Str)
        (g : PvsNP.Str → PvsNP.Str),
        PvsNP.PolyTimeDecider chi → PvsNP.PolyTimeComputable g →
        (∀ w : PvsNP.Str, g w = if selB w then cut w else w0) →
        (∀ p : PvsNP.Str × PvsNP.Str, Rf p = chi (g (pr p))) →
        PvsNP.PolyTimeChecker Rf
          ∧ (∀ p : PvsNP.Str × PvsNP.Str, selB (pr p) = true → Rf p = chi (cut (pr p)))
          ∧ (∀ p : PvsNP.Str × PvsNP.Str, selB (pr p) = false → Rf p = chi w0))
    -- (10) NON-VACUITY: the pairing and its decoder at a concrete pair, matching the value
    -- recorded in TRANSDUCE-2 conjunct (5).
  ∧ pr ([true], [false]) = [false, true, true, false]
  ∧ up [false, true, true, false] = ([true], [false]) := by
  sorry

end PvsNP
