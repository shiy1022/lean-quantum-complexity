-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.digit_by_digit_integer_square_root_and_bit_serial_subtractor`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_digit_by_digit_integer_square_root_and_bit_serial_subtractor`. The real proof is on prove2.me.
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace ShiBQP

theorem digit_by_digit_integer_square_root_and_bit_serial_subtractor :
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
  sorry

end ShiBQP
