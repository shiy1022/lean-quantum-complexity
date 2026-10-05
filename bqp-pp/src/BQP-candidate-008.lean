import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_ShiBQP_digit_by_digit_integer_square_root_and_bit_serial_subtractor

namespace BQPReferenceValidation.Source8
/-
SQRTMACH.  THE ARITHMETIC CORE OF THE INTEGER-SQUARE-ROOT ROUTER STEP.

WHAT IS MISSING AND WHY.  `RF-BUILDc`'s threshold ladder is built from
`S = Nat.sqrt (2 * 4 ^ (h + 3)) = ⌊2 ^ (h + 3) * √2⌋`, and `ROUTER-1b` consumes that `S` as
a GIVEN: it expands it to `h + 7` bits and compares against it, but nothing anywhere
COMPUTES it.  Repeated subtraction of odd numbers computes it in `S ≈ 2 ^ (h + 3)` steps --
exponential in `h`, fatal for the poly-time claim -- so the router needs the digit-by-digit
(restoring) square root, whose iteration count is linear in `h`.

WHAT THIS SLICE PROVES.  Two independent halves, both stated over ∀-quantified functions
pinned only by their defining equations (never over functions bound in the same `∃` as the
conjunct that constrains them):

  * THE RECURRENCE.  `sq 0 = rm 0 = 1` and, at each step,
    `sq (k+1) = 2 * sq k + [sq k < rm k]`,
    `rm (k+1) = if sq k < rm k then 4 * (rm k - sq k - 1) + 3 else 4 * rm k`
    computes `sq k = Nat.sqrt (2 * 4 ^ k)` EXACTLY, with the remainder invariant
    `sq k * sq k + rm k = 2 * 4 ^ k`, the sharp bound `rm k ≤ 2 * sq k`, and
    `sq k < 2 ^ (k+1)`.  ONE iteration per output bit: `h + 3` iterations, not `2 ^ (h+3)`.
    The test is `sq k < rm k` -- a COMPARISON OF THE TWO RUNNING REGISTERS, with no
    multiplication and no squaring anywhere in the loop.  `Nat.sqrt` is never rewritten
    under: the identification is made once, through `Nat.le_sqrt` / `Nat.sqrt_lt` applied to
    the bracketing pair supplied by the remainder invariant.

  * THE BIT-SERIAL REALISATION.  The little-endian value fold `bval`, the fixed-width encoder
    `bits` (both EXACTLY as in `ROUTER-1b`), and the bit-serial borrow subtractor `sbd`
    (difference digits) / `sbo` (borrow out) are shown to implement that comparison and that
    subtraction TOGETHER, in one left-to-right sweep: on `W`-bit operands, `sbo` with
    borrow-in `true` is the verdict of `S < R` and `sbd` is `R - S - 1`, so a machine needs
    one pass, not two.  Also: the encoder inverts the fold on fixed-width lists, a width-`k+1`
    encoding is the width-`k` encoding with one further high bit, and
    `b :: bits k v = bits (k+1) (2*v + b)` -- the shift law that lets a stack machine multiply
    by two with a single `push`.

NOT CLAIMED: no machine appears here, and nothing about `Rf` or the router itself.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

/-! ### Concrete witnesses, for the non-vacuity conjunct -/

private def bvalC : List Bool → ℕ
  | [] => 0
  | b :: t => (bif b then 1 else 0) + 2 * bvalC t

private def bitsC : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n => (n % 2 == 1) :: bitsC k (n / 2)

private def sbdC : Bool → List Bool → List Bool → List Bool
  | _, [], _ => []
  | _, _ :: _, [] => []
  | c, x :: r, y :: s => (xor x (xor y c)) :: sbdC (bif x then y && c else y || c) r s

private def sboC : Bool → List Bool → List Bool → Bool
  | c, [], _ => c
  | c, _ :: _, [] => c
  | c, x :: r, y :: s => sboC (bif x then y && c else y || c) r s

/-! ### The statement -/

theorem _root_.BQPReferenceValidation.candidate8 :
    -- (I) THE DIGIT-BY-DIGIT SQUARE ROOT OF `2 * 4 ^ k`.  One iteration per bit; the
    -- iteration is a comparison and a subtraction of the two running registers, with no
    -- multiplication.  `sq k` IS `Nat.sqrt (2 * 4 ^ k)`, on the nose.
    (∀ (sq rm : ℕ → ℕ), sq 0 = 1 → rm 0 = 1 →
        (∀ k : ℕ, sq (k + 1) = 2 * sq k + (if sq k < rm k then 1 else 0)) →
        (∀ k : ℕ, rm (k + 1)
            = if sq k < rm k then 4 * (rm k - sq k - 1) + 3 else 4 * rm k) →
        ∀ k : ℕ, sq k * sq k + rm k = 2 * 4 ^ k
            ∧ rm k ≤ 2 * sq k
            ∧ Nat.sqrt (2 * 4 ^ k) = sq k
            ∧ sq k < 2 ^ (k + 1))
    -- (II) THE BIT-SERIAL LAYER.  `bval` and `bits` are `ROUTER-1b`'s value fold and
    -- fixed-width encoder verbatim; `sbd` / `sbo` are the digit and borrow streams of the
    -- standard borrow subtractor.  All four are ∀-quantified and pinned by equations only.
  ∧ (∀ (bval : List Bool → ℕ) (bits : ℕ → ℕ → List Bool)
        (sbd : Bool → List Bool → List Bool → List Bool)
        (sbo : Bool → List Bool → List Bool → Bool),
      bval [] = 0 →
      (∀ (b : Bool) (t : List Bool),
          bval (b :: t) = (bif b then 1 else 0) + 2 * bval t) →
      (∀ n : ℕ, bits 0 n = []) →
      (∀ k n : ℕ, bits (k + 1) n = (n % 2 == 1) :: bits k (n / 2)) →
      (∀ (c : Bool) (s : List Bool), sbd c [] s = []) →
      (∀ (c x : Bool) (r : List Bool), sbd c (x :: r) [] = []) →
      (∀ (c x y : Bool) (r s : List Bool),
          sbd c (x :: r) (y :: s)
            = (xor x (xor y c)) :: sbd (bif x then y && c else y || c) r s) →
      (∀ (c : Bool) (s : List Bool), sbo c [] s = c) →
      (∀ (c x : Bool) (r : List Bool), sbo c (x :: r) [] = c) →
      (∀ (c x y : Bool) (r s : List Bool),
          sbo c (x :: r) (y :: s) = sbo (bif x then y && c else y || c) r s) →
        -- (1) the encoder has the advertised width, and is exact below `2 ^ k`
        (∀ k n : ℕ, (bits k n).length = k)
      ∧ (∀ k n : ℕ, n < 2 ^ k → bval (bits k n) = n)
        -- (2) a width-`n` list holds a value below `2 ^ n`, and the encoder INVERTS the
        -- fold on lists of that width: fixed-width bit lists and numbers correspond
      ∧ (∀ l : List Bool, bval l < 2 ^ l.length)
      ∧ (∀ (l : List Bool) (k : ℕ), l.length = k → bits k (bval l) = l)
        -- (3) a width-`k+1` encoding is the width-`k` encoding with ONE more high bit, and
        -- prefixing a low bit is exactly doubling.  These two are what let a stack machine
        -- shift by pushing, and discard the deepest symbol without disturbing the value.
      ∧ (∀ k n : ℕ, ∃ b : Bool, bits (k + 1) n = bits k n ++ [b])
      ∧ (∀ (b : Bool) (k v : ℕ),
            b :: bits k v = bits (k + 1) (2 * v + (bif b then 1 else 0)))
        -- (4) THE ONE-SWEEP COMPARE-AND-SUBTRACT.  With borrow-in `true` the sweep computes
        -- `R - S - 1`, and its borrow-OUT is precisely the verdict of the comparison
        -- `S < R` that the square-root iteration tests.  One pass decides AND subtracts.
      ∧ (∀ (c : Bool) (r s : List Bool),
            r.length = s.length → (sbd c r s).length = r.length)
      ∧ (∀ W S R : ℕ, S < 2 ^ W → R < 2 ^ W → S < R →
            sbo true (bits W R) (bits W S) = false
          ∧ sbd true (bits W R) (bits W S) = bits W (R - S - 1))
      ∧ (∀ W S R : ℕ, S < 2 ^ W → R < 2 ^ W → R ≤ S →
            sbo true (bits W R) (bits W S) = true))
    -- (III) NON-VACUITY, INSIDE THE THEOREM.  The ten defining equations are satisfiable,
    -- and the witnesses really do compute: `bits 5 11` is exhibited, the sweep on
    -- `(7, 5)` returns no borrow and the difference `1`, and the sweep on `(4, 11)` borrows.
  ∧ (∃ (bval : List Bool → ℕ) (bits : ℕ → ℕ → List Bool)
        (sbd : Bool → List Bool → List Bool → List Bool)
        (sbo : Bool → List Bool → List Bool → Bool),
      bval [] = 0
    ∧ (∀ (b : Bool) (t : List Bool),
          bval (b :: t) = (bif b then 1 else 0) + 2 * bval t)
    ∧ (∀ n : ℕ, bits 0 n = [])
    ∧ (∀ k n : ℕ, bits (k + 1) n = (n % 2 == 1) :: bits k (n / 2))
    ∧ (∀ (c : Bool) (s : List Bool), sbd c [] s = [])
    ∧ (∀ (c x : Bool) (r : List Bool), sbd c (x :: r) [] = [])
    ∧ (∀ (c x y : Bool) (r s : List Bool),
          sbd c (x :: r) (y :: s)
            = (xor x (xor y c)) :: sbd (bif x then y && c else y || c) r s)
    ∧ (∀ (c : Bool) (s : List Bool), sbo c [] s = c)
    ∧ (∀ (c x : Bool) (r : List Bool), sbo c (x :: r) [] = c)
    ∧ (∀ (c x y : Bool) (r s : List Bool),
          sbo c (x :: r) (y :: s) = sbo (bif x then y && c else y || c) r s)
    ∧ bval [false, true] = 2
    ∧ bits 5 11 = [true, true, false, true, false]
    ∧ bval (bits 5 11) = 11
    ∧ sbo true (bits 5 7) (bits 5 5) = false
    ∧ sbd true (bits 5 7) (bits 5 5) = bits 5 1
    ∧ sbo true (bits 5 4) (bits 5 11) = true)
    -- (IV) THE TWO ANCHORS OF THE RECURRENCE, computed.
  ∧ Nat.sqrt (2 * 4 ^ 3) = 11
  ∧ Nat.sqrt (2 * 4 ^ 0) = 1 := by
  have sqrtEq : ∀ s n : ℕ, s * s ≤ n → n < (s + 1) * (s + 1) → Nat.sqrt n = s := by
    intro s n h1 h2
    have ha : s ≤ Nat.sqrt n := Nat.le_sqrt.mpr h1
    have hb : Nat.sqrt n < s + 1 := Nat.sqrt_lt.mpr h2
    omega
  have bracket : ∀ X Y N : ℕ, X * X + Y = N → Y < 2 * X + 1 → Nat.sqrt N = X := by
    intro X Y N h1 h2
    refine sqrtEq X N ?_ ?_
    · rw [← h1]
      exact Nat.le_add_right _ _
    · have e : (X + 1) * (X + 1) = X * X + (2 * X + 1) := by ring
      rw [e, ← h1]
      exact Nat.add_lt_add_left h2 (X * X)
  have twoPow : ∀ n : ℕ, 0 < 2 ^ n := by
    intro n
    induction n with
    | zero => exact Nat.zero_lt_one
    | succ n ih =>
        rw [pow_succ]
        omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (I) THE RECURRENCE
    intro sq rm h0 h1 hs hr k
    induction k with
    | zero =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · norm_num [h0, h1]
        · norm_num [h0, h1]
        · have he : Nat.sqrt (2 * 4 ^ 0) = 1 := by
            have h2 : (2 : ℕ) * 4 ^ 0 = 1 * 1 + 1 := by norm_num
            rw [h2]
            exact bracket 1 1 _ rfl (by norm_num)
          rw [h0]
          exact he
        · norm_num [h0]
    | succ k ih =>
        obtain ⟨hsum, hle, -, hlt2⟩ := ih
        have hpow : (2 : ℕ) * 4 ^ (k + 1) = 4 * (2 * 4 ^ k) := by
          rw [pow_succ]
          ring
        have hpow2 : (2 : ℕ) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by
          rw [pow_succ]
          ring
        by_cases hc : sq k < rm k
        · have hS : sq (k + 1) = 2 * sq k + 1 := by
            rw [hs k, if_pos hc]
          have hR : rm (k + 1) = 4 * (rm k - sq k - 1) + 3 := by
            rw [hr k, if_pos hc]
          obtain ⟨T, hT⟩ : ∃ T : ℕ, rm k = T + sq k + 1 := ⟨rm k - sq k - 1, by omega⟩
          have hRT : rm (k + 1) = 4 * T + 3 := by
            rw [hR, hT]
            omega
          have hsum' : sq (k + 1) * sq (k + 1) + rm (k + 1) = 2 * 4 ^ (k + 1) := by
            rw [hS, hRT, hpow, ← hsum, hT]
            ring
          refine ⟨hsum', ?_, ?_, ?_⟩
          · rw [hS, hRT]
            omega
          · refine bracket _ _ _ hsum' ?_
            rw [hS, hRT]
            omega
          · rw [hS, hpow2]
            omega
        · have hS : sq (k + 1) = 2 * sq k := by
            rw [hs k, if_neg hc]
            omega
          have hR : rm (k + 1) = 4 * rm k := by
            rw [hr k, if_neg hc]
          have hsum' : sq (k + 1) * sq (k + 1) + rm (k + 1) = 2 * 4 ^ (k + 1) := by
            rw [hS, hR, hpow, ← hsum]
            ring
          refine ⟨hsum', ?_, ?_, ?_⟩
          · rw [hS, hR]
            omega
          · refine bracket _ _ _ hsum' ?_
            rw [hS, hR]
            omega
          · rw [hS, hpow2]
            omega
  · -- (II) THE BIT-SERIAL LAYER
    intro bval bits sbd sbo hv0 hvc hb0 hbs hd0 hd1 hd2 ho0 ho1 ho2
    have ct : (bif true then (1 : ℕ) else 0) = 1 := rfl
    have cf : (bif false then (1 : ℕ) else 0) = 0 := rfl
    have lenBits : ∀ k n : ℕ, (bits k n).length = k := by
      intro k
      induction k with
      | zero =>
          intro n
          exact congrArg List.length (hb0 n)
      | succ k ih =>
          intro n
          rw [hbs, List.length_cons, ih]
    have valLt : ∀ l : List Bool, bval l < 2 ^ l.length := by
      intro l
      induction l with
      | nil =>
          rw [hv0]
          exact twoPow _
      | cons b t ih =>
          have hb : (bif b then 1 else 0) ≤ 1 := by
            cases b
            · show (0 : ℕ) ≤ 1
              omega
            · show (1 : ℕ) ≤ 1
              omega
          rw [hvc, List.length_cons, pow_succ]
          omega
    have valBits : ∀ k n : ℕ, n < 2 ^ k → bval (bits k n) = n := by
      intro k
      induction k with
      | zero =>
          intro n hn
          rw [pow_zero] at hn
          rw [hb0, hv0]
          omega
      | succ k ih =>
          intro n hn
          rw [pow_succ] at hn
          have hn2 : n / 2 < 2 ^ k := by omega
          rw [hbs, hvc, ih (n / 2) hn2]
          rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with h | h
          · have hcc : ((n % 2 == 1)) = false := by
              rw [h]
              rfl
            rw [hcc]
            show 0 + 2 * (n / 2) = n
            omega
          · have hcc : ((n % 2 == 1)) = true := by
              rw [h]
              rfl
            rw [hcc]
            show 1 + 2 * (n / 2) = n
            omega
    have bitsVal : ∀ (l : List Bool) (k : ℕ), l.length = k → bits k (bval l) = l := by
      intro l
      induction l with
      | nil =>
          intro k hk
          rw [List.length_nil] at hk
          rw [← hk, hb0]
      | cons b t ih =>
          intro k hk
          cases k with
          | zero =>
              exfalso
              rw [List.length_cons] at hk
              omega
          | succ k =>
              have hlen : t.length = k := by
                rw [List.length_cons] at hk
                omega
              have hdiv : ((bif b then 1 else 0) + 2 * bval t) / 2 = bval t := by
                cases b
                · show (0 + 2 * bval t) / 2 = bval t
                  omega
                · show (1 + 2 * bval t) / 2 = bval t
                  omega
              have hmod : (((bif b then 1 else 0) + 2 * bval t) % 2 == 1) = b := by
                cases b
                · show ((0 + 2 * bval t) % 2 == 1) = false
                  have hz : (0 + 2 * bval t) % 2 = 0 := by omega
                  rw [hz]
                  rfl
                · show ((1 + 2 * bval t) % 2 == 1) = true
                  have hz : (1 + 2 * bval t) % 2 = 1 := by omega
                  rw [hz]
                  rfl
              rw [hbs, hvc, hdiv, hmod, ih k hlen]
    have bitsSnoc : ∀ k n : ℕ, ∃ b : Bool, bits (k + 1) n = bits k n ++ [b] := by
      intro k
      induction k with
      | zero =>
          intro n
          refine ⟨(n % 2 == 1), ?_⟩
          have e3 : bits 0 n = [] := hb0 n
          rw [e3, List.nil_append, hbs, hb0]
      | succ k ih =>
          intro n
          obtain ⟨b, hb⟩ := ih (n / 2)
          refine ⟨b, ?_⟩
          rw [hbs (k + 1) n, hb, hbs k n, List.cons_append]
    have bitsCons : ∀ (b : Bool) (k v : ℕ),
        b :: bits k v = bits (k + 1) (2 * v + (bif b then 1 else 0)) := by
      intro b k v
      have hdiv : (2 * v + (bif b then 1 else 0)) / 2 = v := by
        cases b
        · show (2 * v + 0) / 2 = v
          omega
        · show (2 * v + 1) / 2 = v
          omega
      have hmod : ((2 * v + (bif b then 1 else 0)) % 2 == 1) = b := by
        cases b
        · show ((2 * v + 0) % 2 == 1) = false
          have hz : (2 * v + 0) % 2 = 0 := by omega
          rw [hz]
          rfl
        · show ((2 * v + 1) % 2 == 1) = true
          have hz : (2 * v + 1) % 2 = 1 := by omega
          rw [hz]
          rfl
      rw [hbs, hdiv, hmod]
    have lenSbd : ∀ (r s : List Bool) (c : Bool),
        r.length = s.length → (sbd c r s).length = r.length := by
      intro r
      induction r with
      | nil =>
          intro s c _
          rw [hd0]
      | cons x r ih =>
          intro s c hlen
          cases s with
          | nil =>
              exfalso
              rw [List.length_cons, List.length_nil] at hlen
              omega
          | cons y s =>
              have hl : r.length = s.length := by
                rw [List.length_cons, List.length_cons] at hlen
                omega
              rw [hd2, List.length_cons, List.length_cons,
                ih s (bif x then y && c else y || c) hl]
    have fullsub : ∀ x y c : Bool,
        (bif (xor x (xor y c)) then 1 else 0) + (bif y then 1 else 0)
            + (bif c then 1 else 0)
          = (bif x then 1 else 0)
            + 2 * (bif (bif x then y && c else y || c) then 1 else 0) := by
      intro x y c
      cases x <;> cases y <;> cases c <;> rfl
    have subVal : ∀ (r s : List Bool) (c : Bool), r.length = s.length →
        bval (sbd c r s) + bval s + (bif c then 1 else 0)
          = bval r + 2 ^ r.length * (bif (sbo c r s) then 1 else 0) := by
      intro r
      induction r with
      | nil =>
          intro s c hlen
          rw [List.length_nil] at hlen
          cases s with
          | nil =>
              rw [hd0, ho0, hv0, List.length_nil, pow_zero]
              omega
          | cons y s =>
              exfalso
              rw [List.length_cons] at hlen
              omega
      | cons x r ih =>
          intro s c hlen
          cases s with
          | nil =>
              exfalso
              rw [List.length_cons, List.length_nil] at hlen
              omega
          | cons y s =>
              have hl : r.length = s.length := by
                rw [List.length_cons, List.length_cons] at hlen
                omega
              have IH := ih s (bif x then y && c else y || c) hl
              have key := fullsub x y c
              rw [hd2, ho2, hvc, hvc, hvc, List.length_cons, pow_succ]
              rcases Bool.eq_false_or_eq_true
                  (sbo (bif x then y && c else y || c) r s) with hh | hh
              · rw [hh] at IH ⊢
                rw [ct] at IH ⊢
                omega
              · rw [hh] at IH ⊢
                rw [cf] at IH ⊢
                omega
    have decide1 : ∀ W S R : ℕ, S < 2 ^ W → R < 2 ^ W → S < R →
        sbo true (bits W R) (bits W S) = false
      ∧ sbd true (bits W R) (bits W S) = bits W (R - S - 1) := by
      intro W S R hS hR hSR
      have hlenR : (bits W R).length = W := lenBits W R
      have hlenS : (bits W S).length = W := lenBits W S
      have hlen : (bits W R).length = (bits W S).length := by rw [hlenR, hlenS]
      have hvR : bval (bits W R) = R := valBits W R hR
      have hvS : bval (bits W S) = S := valBits W S hS
      have hdlen : (sbd true (bits W R) (bits W S)).length = W := by
        rw [lenSbd (bits W R) (bits W S) true hlen, hlenR]
      have hdlt : bval (sbd true (bits W R) (bits W S)) < 2 ^ W := by
        have hx := valLt (sbd true (bits W R) (bits W S))
        rw [hdlen] at hx
        exact hx
      have hkey := subVal (bits W R) (bits W S) true hlen
      rw [hvR, hvS, hlenR, ct] at hkey
      have hobool : sbo true (bits W R) (bits W S) = false := by
        rcases Bool.eq_false_or_eq_true (sbo true (bits W R) (bits W S)) with hh | hh
        · exfalso
          rw [hh, ct] at hkey
          omega
        · exact hh
      refine ⟨hobool, ?_⟩
      rw [hobool, cf] at hkey
      have hval : bval (sbd true (bits W R) (bits W S)) = R - S - 1 := by omega
      have hb := bitsVal (sbd true (bits W R) (bits W S)) W hdlen
      rw [hval] at hb
      exact hb.symm
    have decide2 : ∀ W S R : ℕ, S < 2 ^ W → R < 2 ^ W → R ≤ S →
        sbo true (bits W R) (bits W S) = true := by
      intro W S R hS hR hSR
      have hlenR : (bits W R).length = W := lenBits W R
      have hlenS : (bits W S).length = W := lenBits W S
      have hlen : (bits W R).length = (bits W S).length := by rw [hlenR, hlenS]
      have hvR : bval (bits W R) = R := valBits W R hR
      have hvS : bval (bits W S) = S := valBits W S hS
      have hkey := subVal (bits W R) (bits W S) true hlen
      rw [hvR, hvS, hlenR, ct] at hkey
      rcases Bool.eq_false_or_eq_true (sbo true (bits W R) (bits W S)) with hh | hh
      · exact hh
      · exfalso
        rw [hh, cf] at hkey
        omega
    exact ⟨lenBits, valBits, valLt, bitsVal, bitsSnoc, bitsCons,
      fun c r s h => lenSbd r s c h, decide1, decide2⟩
  · -- (III) NON-VACUITY
    refine ⟨bvalC, bitsC, sbdC, sboC, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro b t
      rfl
    · intro n
      rfl
    · intro k n
      rfl
    · intro c s
      rfl
    · intro c x r
      rfl
    · intro c x y r s
      rfl
    · intro c s
      rfl
    · intro c x r
      rfl
    · intro c x y r s
      rfl
  · have h2 : (2 : ℕ) * 4 ^ 3 = 11 * 11 + 7 := by norm_num
    rw [h2]
    exact bracket 11 7 _ rfl (by norm_num)
  · have h2 : (2 : ℕ) * 4 ^ 0 = 1 * 1 + 1 := by norm_num
    rw [h2]
    exact bracket 1 1 _ rfl (by norm_num)

end BQPReferenceValidation.Source8

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate8
    let target ← getConstInfo ``ShiBQP.digit_by_digit_integer_square_root_and_bit_serial_subtractor
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.digit_by_digit_integer_square_root_and_bit_serial_subtractor"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.digit_by_digit_integer_square_root_and_bit_serial_subtractor"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.digit_by_digit_integer_square_root_and_bit_serial_subtractor"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate8
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.digit_by_digit_integer_square_root_and_bit_serial_subtractor; axioms {axioms}"
