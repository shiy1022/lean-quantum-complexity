/-
BRIDGE-D.  The two SWEEPS of the route-(A) program -- input loading and the endpoint test
-- verified against the abstract CHECK-1f transition `sTr`, so the file mentions no
encoding name.

`ev` starts every run on the EMPTY zipper `(tl, tr) = ([], [])`: there is no tape to load
`x` onto, and `tr.headI` on `[]` is `false`.  The classical input must therefore be written
in by the program.  The loading sweep `Ld l` walks RIGHT once per wire, emitting an `X`
(opcode 5) exactly where `l` is true, so it touches only opcodes 1 and 5 -- never opcode 0,
which at the left end would insert a cell and shift every wire index.  Each step pushes one
cell onto the left stack, so after `Ld l` the left stack is `l.reverse` and the right tape
is still empty; walking back with `l.length` opcode-0s then yields the head at wire 0 on
the tape `l` exactly.

The endpoint test `En l` is the mirror image: it walks right once per wire, testing "wire
is 1" (opcode 8) where `l` is true and "wire is 0" (opcodes 5, 8, 5) where `l` is false,
restoring the cell each time.  The reject flag afterwards is `de || decide (e ≠ l)`, where
`e` is the tape it found: it rejects precisely when the final tape is not `l`.  This is the
constraint that makes route (A)'s doubled program count `⟨x|U†ΠU|x⟩` rather than an
endpoint-free pair sum.
-/
import Mathlib.Data.ZMod.Basic

namespace BQPBridgeReference

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem inputEndpointSweeps :
    ∀ (sTr : (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool) → ℕ →
          (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool))
      (Ld En : List Bool → List ℕ),
      -- CHECK-1f (I): the one-branch gate walk
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
        ∧ sTr (ph, tl, tr, ct, de, bd, w) 5
            = (ph, tl, (!tr.headI) :: tr.tail, ct, de, bd, w)
        ∧ sTr (ph, tl, tr, ct, de, bd, w) 6
            = (ph, tl, tr.headI :: tr.tail, tr.headI, de, bd, w)
        ∧ sTr (ph, tl, tr, ct, de, bd, w) 7
            = (ph, tl, (xor tr.headI ct) :: tr.tail, ct, de, bd, w)
        ∧ sTr (ph, tl, tr, ct, de, bd, w) 8
            = (ph, tl, tr.headI :: tr.tail, ct, de || !tr.headI, bd, w)
        ∧ sTr (ph, tl, tr, ct, de, bd, w) 9 = (ph, tl, tr.headI :: tr.tail, ct, de, true, w)
        ∧ (∀ c : ℕ, sTr (ph, tl, tr, ct, de, bd, w) c
              = sTr (ph, tl, tr, ct, de, bd, w) (c % 16))) →
      -- the two sweeps, by their recursion clauses
      Ld [] = [] →
      (∀ (b : Bool) (l : List Bool), Ld (b :: l) = (if b then [5, 1] else [1]) ++ Ld l) →
      En [] = [] →
      (∀ (b : Bool) (l : List Bool),
          En (b :: l) = (if b then [8, 1] else [5, 8, 5, 1]) ++ En l) →
      -- the balanced left move, inside the left stack
      (∀ (r : ℕ) (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
          r ≤ tl.length →
          (List.replicate r 0).foldl sTr (ph, tl, tr, ct, de, bd, w)
            = (ph, tl.drop r, (tl.take r).reverse ++ tr, ct, de, bd, w))
      -- the loading sweep pushes the whole tape onto the left stack
      ∧ (∀ (l : List Bool) (ph : ZMod 8) (tl : List Bool) (ct de bd : Bool)
            (w : List Bool),
          (Ld l).foldl sTr (ph, tl, [], ct, de, bd, w)
            = (ph, l.reverse ++ tl, [], ct, de, bd, w))
      -- INPUT LOADING: from the empty zipper, the head ends at wire 0 on the tape `l`
      ∧ (∀ (l : List Bool) (ph : ZMod 8) (ct de bd : Bool) (w : List Bool),
          (Ld l ++ List.replicate l.length 0).foldl sTr (ph, [], [], ct, de, bd, w)
            = (ph, [], l, ct, de, bd, w))
      -- the endpoint sweep restores every cell and rejects on the first mismatch
      ∧ (∀ (l e : List Bool), l.length = e.length →
          ∀ (ph : ZMod 8) (tl : List Bool) (ct de bd : Bool) (w : List Bool),
            (En l).foldl sTr (ph, tl, e, ct, de, bd, w)
              = (ph, e.reverse ++ tl, [], ct, de || decide (e ≠ l), bd, w))
      -- ENDPOINT TEST: it rejects exactly when the final tape is not `l`, head restored
      ∧ (∀ (l e : List Bool), l.length = e.length →
          ∀ (ph : ZMod 8) (ct de bd : Bool) (w : List Bool),
            (En l ++ List.replicate l.length 0).foldl sTr (ph, [], e, ct, de, bd, w)
              = (ph, [], e, ct, de || decide (e ≠ l), bd, w)) := by
  intro sTr Ld En hS hLd0 hLdC hEn0 hEnC
  have h0 := fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).1
  have h1 := fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.1
  have h5 := fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.2.2.2.1
  have h8 := fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.2.2.2.2.2.2.1
  -- the balanced left move
  have hL : ∀ (r : ℕ) (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
      r ≤ tl.length →
      (List.replicate r 0).foldl sTr (ph, tl, tr, ct, de, bd, w)
        = (ph, tl.drop r, (tl.take r).reverse ++ tr, ct, de, bd, w) := by
    intro r
    induction r with
    | zero => intro ph tl tr ct de bd w _; simp
    | succ r ih =>
      intro ph tl tr ct de bd w hlen
      cases tl with
      | nil => simp at hlen
      | cons a s =>
        have hs : r ≤ s.length := by simpa using hlen
        rw [List.replicate_succ, List.foldl_cons, h0 ph (a :: s) tr ct de bd w]
        simp only [List.headI, List.tail]
        rw [ih ph s (a :: tr) ct de bd w hs]
        simp
  -- the loading sweep
  have hload : ∀ (l : List Bool) (ph : ZMod 8) (tl : List Bool) (ct de bd : Bool)
      (w : List Bool),
      (Ld l).foldl sTr (ph, tl, [], ct, de, bd, w)
        = (ph, l.reverse ++ tl, [], ct, de, bd, w) := by
    intro l
    induction l with
    | nil => intro ph tl ct de bd w; rw [hLd0]; simp
    | cons b l ih =>
      intro ph tl ct de bd w
      rw [hLdC, List.foldl_append]
      have hstep : (if b then [5, 1] else ([1] : List ℕ)).foldl sTr
          (ph, tl, [], ct, de, bd, w) = (ph, b :: tl, [], ct, de, bd, w) := by
        have e5 : sTr (ph, tl, ([] : List Bool), ct, de, bd, w) 5
            = (ph, tl, [true], ct, de, bd, w) := by
          rw [h5 ph tl [] ct de bd w]
          first | rfl | simp
        have e1n : sTr (ph, tl, ([] : List Bool), ct, de, bd, w) 1
            = (ph, false :: tl, [], ct, de, bd, w) := by
          rw [h1 ph tl [] ct de bd w]
          first | rfl | simp
        have e1t : sTr (ph, tl, ([true] : List Bool), ct, de, bd, w) 1
            = (ph, true :: tl, [], ct, de, bd, w) := by
          rw [h1 ph tl [true] ct de bd w]
          first | rfl | simp
        cases b
        · rw [if_neg (by simp), List.foldl_cons, List.foldl_nil, e1n]
        · rw [if_pos rfl, List.foldl_cons, List.foldl_cons, List.foldl_nil, e5, e1t]
      rw [hstep, ih ph (b :: tl) ct de bd w]
      simp
  -- the endpoint sweep
  have hcons : ∀ (a b : Bool) (e l : List Bool),
      decide (a :: e ≠ b :: l) = (decide (a ≠ b) || decide (e ≠ l)) := by
    intro a b e l
    by_cases hab : a = b <;> by_cases hel : e = l <;> simp [hab, hel]
  have htest : ∀ (l e : List Bool), l.length = e.length →
      ∀ (ph : ZMod 8) (tl : List Bool) (ct de bd : Bool) (w : List Bool),
        (En l).foldl sTr (ph, tl, e, ct, de, bd, w)
          = (ph, e.reverse ++ tl, [], ct, de || decide (e ≠ l), bd, w) := by
    intro l
    induction l with
    | nil =>
      intro e hlen ph tl ct de bd w
      cases e with
      | nil => rw [hEn0]; simp
      | cons a s => simp at hlen
    | cons b l ih =>
      intro e hlen ph tl ct de bd w
      cases e with
      | nil => simp at hlen
      | cons a s =>
        have hs : l.length = s.length := by simpa using hlen
        rw [hEnC, List.foldl_append]
        have hstep : (if b then [8, 1] else ([5, 8, 5, 1] : List ℕ)).foldl sTr
            (ph, tl, a :: s, ct, de, bd, w)
              = (ph, a :: tl, s, ct, de || decide (a ≠ b), bd, w) := by
          cases b
          · rw [if_neg (by simp), List.foldl_cons, List.foldl_cons, List.foldl_cons,
              List.foldl_cons, List.foldl_nil, h5 ph tl (a :: s) ct de bd w]
            simp only [List.headI, List.tail]
            rw [h8 ph tl ((!a) :: s) ct de bd w]
            simp only [List.headI, List.tail]
            rw [h5 ph tl ((!a) :: s) ct (de || !(!a)) bd w]
            simp only [List.headI, List.tail]
            rw [h1 ph tl ((!(!a)) :: s) ct (de || !(!a)) bd w]
            simp only [List.headI, List.tail]
            cases a <;> simp
          · rw [if_pos rfl, List.foldl_cons, List.foldl_cons, List.foldl_nil,
              h8 ph tl (a :: s) ct de bd w]
            simp only [List.headI, List.tail]
            rw [h1 ph tl (a :: s) ct (de || !a) bd w]
            simp only [List.headI, List.tail]
            cases a <;> simp
        rw [hstep, ih s hs ph (a :: tl) ct (de || decide (a ≠ b)) bd w, hcons]
        simp [Bool.or_assoc]
  refine ⟨hL, hload, ?_, htest, ?_⟩
  · intro l ph ct de bd w
    rw [List.foldl_append, hload l ph [] ct de bd w, List.append_nil]
    have hlen : l.length ≤ (l.reverse).length := by simp
    rw [hL l.length ph l.reverse [] ct de bd w hlen]
    have d1 : (l.reverse).drop l.length = [] := by
      apply List.drop_eq_nil_of_le
      simp
    have d2 : (l.reverse).take l.length = l.reverse := by
      have hle : (l.reverse).length ≤ l.length := by simp
      first
        | exact List.take_of_length_le hle
        | exact List.take_all_of_le hle
        | simp
    rw [d1, d2, List.reverse_reverse, List.append_nil]
  · intro l e hlen ph ct de bd w
    rw [List.foldl_append, htest l e hlen ph [] ct de bd w, List.append_nil]
    have hlen2 : l.length ≤ (e.reverse).length := by simp [← hlen]
    rw [hL l.length ph e.reverse [] ct (de || decide (e ≠ l)) bd w hlen2]
    have d1 : (e.reverse).drop l.length = [] := by
      apply List.drop_eq_nil_of_le
      simp [← hlen]
    have d2 : (e.reverse).take l.length = e.reverse := by
      have hle : (e.reverse).length ≤ l.length := by simp [← hlen]
      first
        | exact List.take_of_length_le hle
        | exact List.take_all_of_le hle
        | simp
    rw [d1, d2, List.reverse_reverse, List.append_nil]


end BQPBridgeReference
