-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.single_run_checker_is_polynomial_time_and_counts_branches_by_phase`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_single_run_checker_is_polynomial_time_and_counts_branches_by_phase`. The real proof is on prove2.me.
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_ShiClassPP
import Theorems.Thm_ShiTM_initList_haltList_laws

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Turing Turing.TM2

namespace ShiBQP

theorem single_run_checker_is_polynomial_time_and_counts_branches_by_phase :
    ∃ (sTr : (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool) → ℕ →
          (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool))
      (enc : List ℕ → PvsNP.Str) (hc : List ℕ → ℕ) (ev : List ℕ → List Bool → Option ℕ)
      (R : ZMod 8 → PvsNP.Str × PvsNP.Str → Bool) (pol : Polynomial ℕ),
    -- (I) the one-branch gate walk: phase exponent mod 8 and moving head on the basis string
    (∀ (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
        sTr (ph, tl, tr, ct, de, bd, w) 0 = (ph, tl.tail, tl.headI :: tr, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 1 = (ph, tr.headI :: tl, tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 2
          = (ph + (if tr.headI && w.headI then 4 else 0), tl, w.headI :: tr.tail, ct, de,
              bd || w.isEmpty, w.tail)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 3
          = (ph + (if tr.headI then 1 else 0), tl, tr.headI :: tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 4
          = (ph + (if tr.headI then 2 else 0), tl, tr.headI :: tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 5 = (ph, tl, (!tr.headI) :: tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 6 = (ph, tl, tr.headI :: tr.tail, tr.headI, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 7
          = (ph, tl, (xor tr.headI ct) :: tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 8
          = (ph, tl, tr.headI :: tr.tail, ct, de || !tr.headI, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 9 = (ph, tl, tr.headI :: tr.tail, ct, de, true, w)
      ∧ (∀ c : ℕ, sTr (ph, tl, tr, ct, de, bd, w) c
            = sTr (ph, tl, tr, ct, de, bd, w) (c % 16)))
    -- (II) the encoding, the Hadamard count, the one-branch evaluator
    ∧ enc [] = []
    ∧ (∀ (c : ℕ) (P : List ℕ), enc (c :: P)
          = enc P ++ [decide (c / 8 % 2 = 1), decide (c / 4 % 2 = 1),
                      decide (c / 2 % 2 = 1), decide (c % 2 = 1)])
    ∧ (∀ P : List ℕ, (enc P).length = 4 * P.length)
    ∧ hc [] = 0
    ∧ (∀ (c : ℕ) (P : List ℕ), hc (c :: P) = (if c % 16 = 2 then 1 else 0) + hc P)
    ∧ (∀ (P : List ℕ) (bs : List Bool),
        ev P bs = (match P.foldl sTr (0, [], [], false, false, false, bs) with
                   | (ph, _, _, _, de, bd, w) =>
                       if de || bd || !w.isEmpty then none else some ph.val))
    -- (II') concatenation laws, so a DOUBLED program `U ++ test ++ U†` is budgeted exactly
    ∧ (∀ P Q : List ℕ, hc (P ++ Q) = hc P + hc Q)
    ∧ (∀ P Q : List ℕ, enc (P ++ Q) = enc Q ++ enc P)
    ∧ (∀ (P Q : List ℕ)
          (s : ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool),
        (P ++ Q).foldl sTr s = Q.foldl sTr (P.foldl sTr s))
    -- (III) the evaluator IS a polynomial-time checking relation, total on every input
    ∧ (∀ dg : ZMod 8, PvsNP.PolyTimeChecker (R dg))
    ∧ (∀ dg : ZMod 8, ∃ c : Turing.TM2ComputableInPolyTime PvsNP.encodePair
          Computability.encodeBool (R dg), c.time = pol)
    ∧ (∀ n : ℕ, pol.eval n = 24 * n + 48)
    ∧ pol.eval 16 = 432
    -- (IV) SINGLE RUN: it accepts exactly the surviving branches at phase `dg`, counted
    -- at `hc Q` — no pair structure, so the endpoint constraint is carried by `Q` itself
    ∧ (∀ (dg : ZMod 8) (Q : List ℕ) (w : PvsNP.Str),
        R dg (enc Q, w) = decide (ev Q w = some dg.val))
    ∧ (∀ (dg : ZMod 8) (Q : List ℕ),
        ShiClassPP.countAccept (R dg) (enc Q) (hc Q)
          = (Finset.univ.filter (fun b : Fin (hc Q) → Bool =>
              ev Q (List.ofFn b) = some dg.val)).card)
    -- (V) non-vacuity, on the two-Hadamard circuit `H, T, H`
    ∧ hc [2, 3, 2] = 2
    ∧ (enc [2, 3, 2]).length = 12
    ∧ ev [2, 3, 2] [false, false] = some 0
    ∧ ev [2, 3, 2] [false, true] = some 0
    ∧ ev [2, 3, 2] [true, false] = some 1
    ∧ ev [2, 3, 2] [true, true] = some 5
    ∧ ev [2, 3, 2] [true] = none
    ∧ ev [2, 3, 2, 8] [true, false] = none
    ∧ ev [2, 3, 2, 8] [true, true] = some 5
    ∧ ev [9] [] = none
    ∧ R 0 (enc [2, 3, 2], [false, false]) = true
    ∧ R 1 (enc [2, 3, 2], [false, false]) = false
    ∧ R 1 (enc [2, 3, 2], [true, false]) = true
    ∧ R 5 (enc [2, 3, 2], [true, true]) = true
    ∧ R 0 (enc [2, 3, 2], [true]) = false
    ∧ R 0 (enc [2, 3, 2], [true, true, true]) = false
    ∧ ShiClassPP.countAccept (R 0) (enc [2, 3, 2]) (hc [2, 3, 2]) = 2
    ∧ ShiClassPP.countAccept (R 1) (enc [2, 3, 2]) (hc [2, 3, 2]) = 1
    ∧ ShiClassPP.countAccept (R 2) (enc [2, 3, 2]) (hc [2, 3, 2]) = 0
    -- (VI) the DOUBLED-CIRCUIT witness: `U = H`, output-wire test, `U† = H`, then the
    -- endpoint test "wire 0 is back to 0" written as `X`, test, `X`.  Exactly one of the
    -- four branch strings survives, at phase 0, and `(1/2)^1 * 1 = 1/2 = ⟨0|H Π H|0⟩`.
    ∧ hc [2, 8, 2, 5, 8, 5] = 2
    ∧ hc [2, 8, 2, 5, 8, 5] = hc [2] + hc [2]
    ∧ ev [2, 8, 2, 5, 8, 5] [true, false] = some 0
    ∧ ev [2, 8, 2, 5, 8, 5] [false, false] = none
    ∧ ev [2, 8, 2, 5, 8, 5] [false, true] = none
    ∧ ev [2, 8, 2, 5, 8, 5] [true, true] = none
    ∧ ShiClassPP.countAccept (R 0) (enc [2, 8, 2, 5, 8, 5])
        (hc [2, 8, 2, 5, 8, 5]) = 1
    ∧ ShiClassPP.countAccept (R 1) (enc [2, 8, 2, 5, 8, 5])
        (hc [2, 8, 2, 5, 8, 5]) = 0
    ∧ ShiClassPP.countAccept (R 3) (enc [2, 8, 2, 5, 8, 5])
        (hc [2, 8, 2, 5, 8, 5]) = 0
    ∧ ShiClassPP.countAccept (R 4) (enc [2, 8, 2, 5, 8, 5])
        (hc [2, 8, 2, 5, 8, 5]) = 0 := by
  sorry

end ShiBQP
