/-
BRIDGE-B.  The TAPE-ZIPPER ENGINE of the semantic bridge, stated against the abstract
`CHECK-1f` transition `sTr` so that the file never mentions `ShiShallow.Instr` and stays
outside the encoding's transitive name closure.

`sTr` carries a two-list zipper `(tl, tr)`: the tape is `tl.reverse ++ tr` with the head at
index `tl.length`.  A compiler that emits one head-neutral BLOCK per gate needs exactly
three things, and this file supplies all three.

(1) The two balanced move blocks act on the zipper as `take`/`drop`, PROVIDED the move stays
    inside the list.  Moving right past the end of `tr`, or left at `tl = []`, is the drift
    hazard: those are excluded by the length hypotheses `r ≤ tr.length`, `r ≤ tl.length`.

(2) THE LOCAL-BLOCK LEMMA.  If `body` leaves the head where it found it, leaves `tl`
    untouched, and rewrites only the cell under the head, then
    `replicate i 1 ++ body ++ replicate i 0` run from head position `0` on the tape `l`
    yields head position `0` again and the tape `l.set i b'`.  This is the statement that
    turns "gate on wire `i`" into "`List.set` at index `i`" once and for all.

(3) The bodies themselves, each in the `∀ tl` form that (2) consumes: `T` and its adjoint
    (seven opcode-3s), `S` and its adjoint (three opcode-4s), `X`, the Hadamard (the one
    opcode that consumes a witness bit), the two endpoint tests "wire = 1" and "wire = 0",
    and the two halves of the CNOT block, the control latch and the xor.
-/
import Mathlib.Data.ZMod.Basic

namespace BQPBridgeReference

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem tapeZipper :
    ∀ sTr : (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool) → ℕ →
          (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool),
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
      -- (1) the balanced move blocks, inside the tape
      (∀ (r : ℕ) (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
          r ≤ tr.length →
          (List.replicate r 1).foldl sTr (ph, tl, tr, ct, de, bd, w)
            = (ph, (tr.take r).reverse ++ tl, tr.drop r, ct, de, bd, w))
      ∧ (∀ (r : ℕ) (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
          r ≤ tl.length →
          (List.replicate r 0).foldl sTr (ph, tl, tr, ct, de, bd, w)
            = (ph, tl.drop r, (tl.take r).reverse ++ tr, ct, de, bd, w))
      -- the cell under the head, and the fact that writing it back is a no-op
      ∧ (∀ (i : ℕ) (l : List Bool), i < l.length →
          ∃ b : Bool, l.drop i = b :: l.drop (i + 1) ∧ l.set i b = l)
      -- (2) THE LOCAL-BLOCK LEMMA
      ∧ (∀ (body : List ℕ) (i : ℕ) (l t : List Bool) (b b' : Bool) (ph ph' : ZMod 8)
            (ct ct' de de' bd bd' : Bool) (w w' : List Bool),
          i < l.length → l.drop i = b :: t →
          (∀ tl : List Bool, body.foldl sTr (ph, tl, b :: t, ct, de, bd, w)
              = (ph', tl, b' :: t, ct', de', bd', w')) →
          (List.replicate i 1 ++ (body ++ List.replicate i 0)).foldl sTr
              (ph, [], l, ct, de, bd, w)
            = (ph', [], l.set i b', ct', de', bd', w'))
      -- (3) the bodies, in the shape (2) consumes
      ∧ (∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
            (tl : List Bool),
          [3].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
            = (ph + (if b then 1 else 0), tl, b :: t, ct, de, bd, w))
      ∧ (∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
            (tl : List Bool),
          [3, 3, 3, 3, 3, 3, 3].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
            = (ph + (if b then 7 else 0), tl, b :: t, ct, de, bd, w))
      ∧ (∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
            (tl : List Bool),
          [4].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
            = (ph + (if b then 2 else 0), tl, b :: t, ct, de, bd, w))
      ∧ (∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
            (tl : List Bool),
          [4, 4, 4].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
            = (ph + (if b then 6 else 0), tl, b :: t, ct, de, bd, w))
      ∧ (∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
            (tl : List Bool),
          [5].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
            = (ph, tl, (!b) :: t, ct, de, bd, w))
      ∧ (∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
            (tl : List Bool),
          [2].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
            = (ph + (if b && w.headI then 4 else 0), tl, w.headI :: t, ct, de,
                bd || w.isEmpty, w.tail))
      ∧ (∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
            (tl : List Bool),
          [8].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
            = (ph, tl, b :: t, ct, de || !b, bd, w))
      ∧ (∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
            (tl : List Bool),
          [5, 8, 5].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
            = (ph, tl, b :: t, ct, de || b, bd, w))
      ∧ (∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
            (tl : List Bool),
          [6].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
            = (ph, tl, b :: t, b, de, bd, w))
      ∧ (∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
            (tl : List Bool),
          [7].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
            = (ph, tl, (xor b ct) :: t, ct, de, bd, w)) := by
  intro sTr hS
  have h0 := fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).1
  have h1 := fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.1
  have h2 := fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.1
  have h3 := fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.2.1
  have h4 := fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.2.2.1
  have h5 := fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.2.2.2.1
  have h6 := fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.2.2.2.2.1
  have h7 := fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.2.2.2.2.2.1
  have h8 := fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.2.2.2.2.2.2.1
  -- the move blocks
  have hR : ∀ (r : ℕ) (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
      r ≤ tr.length →
      (List.replicate r 1).foldl sTr (ph, tl, tr, ct, de, bd, w)
        = (ph, (tr.take r).reverse ++ tl, tr.drop r, ct, de, bd, w) := by
    intro r
    induction r with
    | zero => intro ph tl tr ct de bd w _; simp
    | succ r ih =>
      intro ph tl tr ct de bd w hlen
      cases tr with
      | nil => simp at hlen
      | cons a s =>
        have hs : r ≤ s.length := by simpa using hlen
        rw [List.replicate_succ, List.foldl_cons, h1 ph tl (a :: s) ct de bd w]
        simp only [List.headI, List.tail]
        rw [ih ph (a :: tl) s ct de bd w hs]
        simp
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
  -- the cell under the head
  have hcell : ∀ (i : ℕ) (l : List Bool), i < l.length →
      ∃ b : Bool, l.drop i = b :: l.drop (i + 1) ∧ l.set i b = l := by
    intro i
    induction i with
    | zero =>
      intro l hl
      cases l with
      | nil => simp at hl
      | cons a s => exact ⟨a, by simp, by simp⟩
    | succ i ih =>
      intro l hl
      cases l with
      | nil => simp at hl
      | cons a s =>
        have hs : i < s.length := by simpa using hl
        obtain ⟨b, hb1, hb2⟩ := ih s hs
        refine ⟨b, ?_, ?_⟩
        · simpa using hb1
        · simpa using hb2
  have hsetTake : ∀ (i : ℕ) (l : List Bool) (b' : Bool), i < l.length →
      l.set i b' = l.take i ++ b' :: l.drop (i + 1) := by
    intro i
    induction i with
    | zero =>
      intro l b' hl
      cases l with
      | nil => simp at hl
      | cons a s => simp
    | succ i ih =>
      intro l b' hl
      cases l with
      | nil => simp at hl
      | cons a s =>
        have hs : i < s.length := by simpa using hl
        simpa using ih s b' hs
  -- the local-block lemma
  have hblock : ∀ (body : List ℕ) (i : ℕ) (l t : List Bool) (b b' : Bool)
      (ph ph' : ZMod 8) (ct ct' de de' bd bd' : Bool) (w w' : List Bool),
      i < l.length → l.drop i = b :: t →
      (∀ tl : List Bool, body.foldl sTr (ph, tl, b :: t, ct, de, bd, w)
          = (ph', tl, b' :: t, ct', de', bd', w')) →
      (List.replicate i 1 ++ (body ++ List.replicate i 0)).foldl sTr
          (ph, [], l, ct, de, bd, w)
        = (ph', [], l.set i b', ct', de', bd', w') := by
    intro body i l t b b' ph ph' ct ct' de de' bd bd' w w' hi hdi hbody
    have hti : ((l.take i).reverse).length = i := by
      rw [List.length_reverse, List.length_take]
      omega
    have e1 : (List.replicate i 1).foldl sTr (ph, [], l, ct, de, bd, w)
        = (ph, (l.take i).reverse, b :: t, ct, de, bd, w) := by
      rw [hR i ph [] l ct de bd w (le_of_lt hi), List.append_nil, hdi]
    have e2 := hL i ph' ((l.take i).reverse) (b' :: t) ct' de' bd' w' (le_of_eq hti.symm)
    have d1 : ((l.take i).reverse).drop i = [] := by
      apply List.drop_eq_nil_of_le
      omega
    have d2 : ((l.take i).reverse).take i = (l.take i).reverse := by
      have hle : ((l.take i).reverse).length ≤ i := by omega
      first
        | exact List.take_of_length_le hle
        | exact List.take_all_of_le hle
        | simp [hle]
    have ht : t = l.drop (i + 1) := by
      have hd : l.drop (i + 1) = (l.drop i).drop 1 := by
        rw [List.drop_drop]
        all_goals (congr 1; all_goals omega)
      simp [hd, hdi]
    rw [List.foldl_append, List.foldl_append, e1, hbody ((l.take i).reverse), e2, d1, d2,
      List.reverse_reverse, hsetTake i l b' hi, ht]
  -- the bodies
  have hz7 : ∀ x : ZMod 8, x + 1 + 1 + 1 + 1 + 1 + 1 + 1 = x + 7 := by decide
  have hz6 : ∀ x : ZMod 8, x + 2 + 2 + 2 = x + 6 := by decide
  have g3 : ∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
      (tl : List Bool),
      [3].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
        = (ph + (if b then 1 else 0), tl, b :: t, ct, de, bd, w) := by
    intro ph t b ct de bd w tl
    simp only [List.foldl_cons, List.foldl_nil, h3 ph tl (b :: t) ct de bd w,
      List.headI, List.tail]
    all_goals rfl
  have g4 : ∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
      (tl : List Bool),
      [4].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
        = (ph + (if b then 2 else 0), tl, b :: t, ct, de, bd, w) := by
    intro ph t b ct de bd w tl
    simp only [List.foldl_cons, List.foldl_nil, h4 ph tl (b :: t) ct de bd w,
      List.headI, List.tail]
    all_goals rfl
  have g5 : ∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
      (tl : List Bool),
      [5].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
        = (ph, tl, (!b) :: t, ct, de, bd, w) := by
    intro ph t b ct de bd w tl
    simp only [List.foldl_cons, List.foldl_nil, h5 ph tl (b :: t) ct de bd w,
      List.headI, List.tail]
    all_goals rfl
  have g2 : ∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
      (tl : List Bool),
      [2].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
        = (ph + (if b && w.headI then 4 else 0), tl, w.headI :: t, ct, de,
            bd || w.isEmpty, w.tail) := by
    intro ph t b ct de bd w tl
    simp only [List.foldl_cons, List.foldl_nil, h2 ph tl (b :: t) ct de bd w,
      List.headI, List.tail]
    all_goals rfl
  have g8 : ∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
      (tl : List Bool),
      [8].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
        = (ph, tl, b :: t, ct, de || !b, bd, w) := by
    intro ph t b ct de bd w tl
    simp only [List.foldl_cons, List.foldl_nil, h8 ph tl (b :: t) ct de bd w,
      List.headI, List.tail]
    all_goals rfl
  have g6 : ∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
      (tl : List Bool),
      [6].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
        = (ph, tl, b :: t, b, de, bd, w) := by
    intro ph t b ct de bd w tl
    simp only [List.foldl_cons, List.foldl_nil, h6 ph tl (b :: t) ct de bd w,
      List.headI, List.tail]
    all_goals rfl
  have g7 : ∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
      (tl : List Bool),
      [7].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
        = (ph, tl, (xor b ct) :: t, ct, de, bd, w) := by
    intro ph t b ct de bd w tl
    simp only [List.foldl_cons, List.foldl_nil, h7 ph tl (b :: t) ct de bd w,
      List.headI, List.tail]
    all_goals rfl
  refine ⟨hR, hL, hcell, hblock, g3, ?_, g4, ?_, g5, g2, g8, ?_, g6, g7⟩
  · intro ph t b ct de bd w tl
    have e : ([3, 3, 3, 3, 3, 3, 3] : List ℕ) = [3] ++ ([3] ++ ([3] ++ ([3] ++
        ([3] ++ ([3] ++ [3]))))) := by rfl
    rw [e]
    simp only [List.foldl_append, g3]
    cases b
    · simp
    · simp only [if_true]
      rw [hz7 ph]
  · intro ph t b ct de bd w tl
    have e : ([4, 4, 4] : List ℕ) = [4] ++ ([4] ++ [4]) := by rfl
    rw [e]
    simp only [List.foldl_append, g4]
    cases b
    · simp
    · simp only [if_true]
      rw [hz6 ph]
  · intro ph t b ct de bd w tl
    have e : ([5, 8, 5] : List ℕ) = [5] ++ ([8] ++ [5]) := by rfl
    rw [e]
    simp only [List.foldl_append, g5, g8]
    cases b
    · simp
    · simp


end BQPBridgeReference
