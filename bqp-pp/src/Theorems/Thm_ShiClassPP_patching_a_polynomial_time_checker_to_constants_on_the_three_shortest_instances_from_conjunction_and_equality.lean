-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassPP.patching_a_polynomial_time_checker_to_constants_on_the_three_shortest_instances_from_conjunction_and_equality`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassPP_patching_a_polynomial_time_checker_to_constants_on_the_three_shortest_instances_from_conjunction_and_equality`. The real proof is on prove2.me.
import Definitions.Def_ShiClassPP

set_option autoImplicit false
set_option maxHeartbeats 1600000

open PvsNP ShiClassPP

namespace ShiClassPP

theorem patching_a_polynomial_time_checker_to_constants_on_the_three_shortest_instances_from_conjunction_and_equality
    -- ACCEPTED: complement closure (`BRIDGE-Cb` (8)).
    (hNeg : ∀ R : Str × Str → Bool, PolyTimeChecker R →
      PolyTimeChecker (fun p => !(R p)))
    -- ACCEPTED: the instance projection bridge (`TRANSDUCE-1c` (6)).
    (hProj : ∀ χ : Str → Bool, PolyTimeDecider χ →
      PolyTimeChecker (fun p : Str × Str => χ p.1))
    -- NEW MACHINE OBLIGATION, the whole content of the branch: `PolyTimeChecker` is closed
    -- under `&&`.  NOT derivable from the accepted kit, which only produces `R ∘ T` and
    -- `!(R ∘ T)` and can therefore never reach a constant.
    (hAnd : ∀ R S : Str × Str → Bool, PolyTimeChecker R → PolyTimeChecker S →
      PolyTimeChecker (fun p => R p && S p))
    -- NEW, but a concrete bounded-lookahead machine, not a closure property.
    (hEqDec : ∀ a : Str, PolyTimeDecider (fun w : Str => decide (w = a))) :
    -- (1) DISJUNCTION, from `&&` and complement.
    (∀ R S : Str × Str → Bool, PolyTimeChecker R → PolyTimeChecker S →
        PolyTimeChecker (fun p => R p || S p))
    -- (2) THE INSTANCE-EQUALITY SELECTOR is a polynomial-time checker.
  ∧ (∀ a : Str, PolyTimeChecker (fun p : Str × Str => decide (p.1 = a)))
    -- (3) THE BRANCH COMBINATOR: a checker patched to a CONSTANT on ONE instance is still a
    -- polynomial-time checker.
  ∧ (∀ (R : Str × Str → Bool) (a : Str) (c : Bool), PolyTimeChecker R →
        PolyTimeChecker (fun p : Str × Str => if p.1 = a then c else R p))
    -- (4) THE TARGET: patched to constants on ALL THREE instances of length at most one.
  ∧ (∀ (R : Str × Str → Bool) (c₀ c₁ c₂ : Bool), PolyTimeChecker R →
        PolyTimeChecker (fun p : Str × Str =>
          if p.1 = [] then c₀ else if p.1 = [false] then c₁ else
            if p.1 = [true] then c₂ else R p))
    -- (5) THE PATCHED CHECKER IS CONSTANT IN THE WITNESS on each short instance -- exactly
    -- the three hypotheses `SHORT-COUNT` (7) asks for.
  ∧ (∀ (R : Str × Str → Bool) (c₀ c₁ c₂ : Bool),
        (∀ w : Str, (fun p : Str × Str =>
            if p.1 = [] then c₀ else if p.1 = [false] then c₁ else
              if p.1 = [true] then c₂ else R p) ([], w) = c₀)
      ∧ (∀ w : Str, (fun p : Str × Str =>
            if p.1 = [] then c₀ else if p.1 = [false] then c₁ else
              if p.1 = [true] then c₂ else R p) ([false], w) = c₁)
      ∧ (∀ w : Str, (fun p : Str × Str =>
            if p.1 = [] then c₀ else if p.1 = [false] then c₁ else
              if p.1 = [true] then c₂ else R p) ([true], w) = c₂))
    -- (6) AND IT IS `R` ITSELF on every instance of length at least two: the patch is
    -- invisible exactly where the counting argument lives.
  ∧ (∀ (R : Str × Str → Bool) (c₀ c₁ c₂ : Bool) (x w : Str), 2 ≤ x.length →
        (fun p : Str × Str =>
          if p.1 = [] then c₀ else if p.1 = [false] then c₁ else
            if p.1 = [true] then c₂ else R p) (x, w) = R (x, w))
    -- (7) HENCE THE COUNTS AGREE at every long instance and every witness length.
  ∧ (∀ (R : Str × Str → Bool) (c₀ c₁ c₂ : Bool) (x : Str) (m : ℕ), 2 ≤ x.length →
        countAccept (fun p : Str × Str =>
          if p.1 = [] then c₀ else if p.1 = [false] then c₁ else
            if p.1 = [true] then c₂ else R p) x m = countAccept R x m)
    -- (8) THE WELD TO `SHORT-COUNT` (7), taken as a hypothesis here since it is an accepted
    -- theorem.  Note what is left for the consumer: long-input correctness of the ORIGINAL
    -- `R`, and the three membership equivalences.  No polynomial-time hypothesis on the
    -- patched checker survives.
  ∧ (∀ (L : Language Bool) (R : Str × Str → Bool) (k : ℕ) (c₀ c₁ c₂ : Bool),
        (∀ (L' : Language Bool) (R' : Str × Str → Bool) (k' : ℕ) (d₀ d₁ d₂ : Bool),
            1 ≤ k' → PolyTimeChecker R' →
            (∀ x : Str, 2 ≤ x.length →
              (x ∈ L' ↔ 2 * countAccept R' x (x.length ^ k') > 2 ^ (x.length ^ k'))) →
            (∀ w : Str, R' ([], w) = d₀) → (∀ w : Str, R' ([false], w) = d₁) →
            (∀ w : Str, R' ([true], w) = d₂) →
            (d₀ = true ↔ [] ∈ L') → (d₁ = true ↔ [false] ∈ L') →
            (d₂ = true ↔ [true] ∈ L') →
            L' ∈ PP) →
        1 ≤ k → PolyTimeChecker R →
        (∀ x : Str, 2 ≤ x.length →
          (x ∈ L ↔ 2 * countAccept R x (x.length ^ k) > 2 ^ (x.length ^ k))) →
        (c₀ = true ↔ [] ∈ L) → (c₁ = true ↔ [false] ∈ L) → (c₂ = true ↔ [true] ∈ L) →
        L ∈ PP)
    -- (9) NON-VACUITY: the patch really does change values.  At the concrete seed
    -- `fun p => (p.1 ++ p.2).headI`, which accepts `([], [true])` and `([true], [])`, the
    -- patch to `false, false, false` rejects BOTH, while a length-two instance is untouched.
  ∧ ((fun p : Str × Str => (p.1 ++ p.2).headI) ([], [true]) = true
      ∧ (fun p : Str × Str => (p.1 ++ p.2).headI) ([true], []) = true
      ∧ (fun p : Str × Str =>
          if p.1 = [] then false else if p.1 = [false] then false else
            if p.1 = [true] then false else (p.1 ++ p.2).headI) ([], [true]) = false
      ∧ (fun p : Str × Str =>
          if p.1 = [] then false else if p.1 = [false] then false else
            if p.1 = [true] then false else (p.1 ++ p.2).headI) ([true], []) = false
      ∧ (fun p : Str × Str =>
          if p.1 = [] then false else if p.1 = [false] then false else
            if p.1 = [true] then false else (p.1 ++ p.2).headI)
              ([true, false], []) = true) := by
  sorry

end ShiClassPP
