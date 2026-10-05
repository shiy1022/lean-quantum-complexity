/-
BRIDGE-SIMb.  The GATE-BLOCK DICTIONARY of the route-(A) compiler, stated against the
abstract `CHECK-1f` transition `sTr` so that the file never mentions `ShiShallow.Instr`
and stays outside the encoding's transitive name closure (gotcha 214).

BRIDGE-Bc gave the tape-zipper engine and the ten gate BODIES.  What a simulation
induction actually consumes is the WHOLE WRAPPED BLOCK, read as an operation on the tape
`l` with the head parked at wire 0.  This file supplies exactly that:

(0) a program assembled as a list of blocks is run block by block;

(1) THE GENERAL WRAPPER LEMMA, strictly more general than BRIDGE-Bc's local-block lemma:
    the body no longer has to leave the tail of the tape alone, only to return the head
    where it found it.  This is what the CNOT block needs, and BRIDGE-Bc's version cannot
    express it;

(2)-(8) the one-cell blocks -- `T`, its adjoint (seven opcode-3s), `S`, its adjoint (three
    opcode-4s), `X`, the Hadamard, the output-wire test -- each as a `List.set` on the
    tape and an increment of the phase;

(9)-(10) THE TWO CNOT BLOCKS, in both orientations, in exactly the form BRIDGE-C2c's
    compiler emits them.  BRIDGE-C2c proves only that these blocks are head-safe and use
    legal opcodes; their SEMANTICS was a hand check (gotcha 276).  Here they are proved:
    each writes `xor (cell j) (cell i)` into wire `j`, leaves every other cell alone,
    leaves the phase and both reject flags alone, consumes no witness bit, and returns the
    head to wire 0.  Note that CHECK-1fc's `[6, 1, 7]` is neither head-neutral nor general;
    these blocks are.
-/
import Mathlib.Data.ZMod.Basic

namespace BQPBridgeReference

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem blockDictionary :
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
      -- (0) a program assembled from blocks is run block by block
      (∀ (bs : List (List ℕ))
          (s : ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool),
          bs.flatten.foldl sTr s = bs.foldl (fun t p => p.foldl sTr t) s)
      -- (1) THE GENERAL WRAPPER LEMMA
      ∧ (∀ (body : List ℕ) (d : ℕ) (tl u u' : List Bool) (ph ph' : ZMod 8)
            (ct ct' de de' bd bd' : Bool) (w w' : List Bool),
          d ≤ u.length →
          (∀ tl2 : List Bool, body.foldl sTr (ph, tl2, u.drop d, ct, de, bd, w)
              = (ph', tl2, u', ct', de', bd', w')) →
          (List.replicate d 1 ++ (body ++ List.replicate d 0)).foldl sTr
              (ph, tl, u, ct, de, bd, w)
            = (ph', tl, u.take d ++ u', ct', de', bd', w'))
      -- (2) the `T` block
      ∧ (∀ (i : ℕ) (l : List Bool) (ph : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < l.length →
          (List.replicate i 1 ++ ([3] ++ List.replicate i 0)).foldl sTr
              (ph, [], l, ct, de, bd, w)
            = (ph + (if (l.drop i).headI then 1 else 0), [], l, ct, de, bd, w))
      -- (3) the adjoint `T` block
      ∧ (∀ (i : ℕ) (l : List Bool) (ph : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < l.length →
          (List.replicate i 1 ++ ([3, 3, 3, 3, 3, 3, 3] ++ List.replicate i 0)).foldl sTr
              (ph, [], l, ct, de, bd, w)
            = (ph + (if (l.drop i).headI then 7 else 0), [], l, ct, de, bd, w))
      -- (4) the `S` block
      ∧ (∀ (i : ℕ) (l : List Bool) (ph : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < l.length →
          (List.replicate i 1 ++ ([4] ++ List.replicate i 0)).foldl sTr
              (ph, [], l, ct, de, bd, w)
            = (ph + (if (l.drop i).headI then 2 else 0), [], l, ct, de, bd, w))
      -- (5) the adjoint `S` block
      ∧ (∀ (i : ℕ) (l : List Bool) (ph : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < l.length →
          (List.replicate i 1 ++ ([4, 4, 4] ++ List.replicate i 0)).foldl sTr
              (ph, [], l, ct, de, bd, w)
            = (ph + (if (l.drop i).headI then 6 else 0), [], l, ct, de, bd, w))
      -- (6) the `X` block
      ∧ (∀ (i : ℕ) (l : List Bool) (ph : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < l.length →
          (List.replicate i 1 ++ ([5] ++ List.replicate i 0)).foldl sTr
              (ph, [], l, ct, de, bd, w)
            = (ph, [], l.set i (!(l.drop i).headI), ct, de, bd, w))
      -- (7) the HADAMARD block: the only block that consumes a witness bit
      ∧ (∀ (i : ℕ) (l : List Bool) (ph : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < l.length →
          (List.replicate i 1 ++ ([2] ++ List.replicate i 0)).foldl sTr
              (ph, [], l, ct, de, bd, w)
            = (ph + (if (l.drop i).headI && w.headI then 4 else 0), [],
                l.set i w.headI, ct, de, bd || w.isEmpty, w.tail))
      -- (8) the output-wire test block
      ∧ (∀ (i : ℕ) (l : List Bool) (ph : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < l.length →
          (List.replicate i 1 ++ ([8] ++ List.replicate i 0)).foldl sTr
              (ph, [], l, ct, de, bd, w)
            = (ph, [], l, ct, de || !(l.drop i).headI, bd, w))
      -- (9) THE CNOT BLOCK, control `i` below target `j`
      ∧ (∀ (i j : ℕ) (l : List Bool) (ph : ZMod 8) (ct de bd : Bool) (w : List Bool),
          i < j → j < l.length →
          (List.replicate i 1 ++ (([6] ++ (List.replicate (j - i) 1
              ++ ([7] ++ List.replicate (j - i) 0))) ++ List.replicate i 0)).foldl sTr
              (ph, [], l, ct, de, bd, w)
            = (ph, [], l.set j (xor (l.drop j).headI (l.drop i).headI),
                (l.drop i).headI, de, bd, w))
      -- (10) THE CNOT BLOCK, target `j` below control `i`
      ∧ (∀ (i j : ℕ) (l : List Bool) (ph : ZMod 8) (ct de bd : Bool) (w : List Bool),
          j < i → i < l.length →
          (List.replicate j 1 ++ ((List.replicate (i - j) 1 ++ ([6]
              ++ (List.replicate (i - j) 0 ++ [7]))) ++ List.replicate j 0)).foldl sTr
              (ph, [], l, ct, de, bd, w)
            = (ph, [], l.set j (xor (l.drop j).headI (l.drop i).headI),
                (l.drop i).headI, de, bd, w)) := by
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
  -- the move blocks (BRIDGE-Bc)
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
  -- list surgery
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
        exact ⟨b, by simpa using hb1, by simpa using hb2⟩
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
  have hcomb : ∀ (i : ℕ) (l : List Bool) (d : ℕ),
      l.take i ++ (l.drop i).take d = l.take (i + d) := by
    intro i
    induction i with
    | zero => intro l d; simp
    | succ i ih =>
      intro l d
      cases l with
      | nil => simp
      | cons a s =>
        have hj : i + 1 + d = (i + d) + 1 := by omega
        rw [hj]
        simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
        rw [ih s d]
  have hdd : ∀ (l : List Bool) (a b : ℕ), (l.drop a).drop b = l.drop (a + b) := by
    intro l a b
    rw [List.drop_drop]
    try (congr 1; omega)
  -- (0) block-by-block execution
  have hflat : ∀ (bs : List (List ℕ))
      (s : ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool),
      bs.flatten.foldl sTr s = bs.foldl (fun t p => p.foldl sTr t) s := by
    intro bs
    induction bs with
    | nil => intro s; rfl
    | cons p ps ih =>
      intro s
      simp only [List.flatten_cons, List.foldl_append, List.foldl_cons]
      exact ih _
  -- (1) the general wrapper lemma
  have hwrap : ∀ (body : List ℕ) (d : ℕ) (tl u u' : List Bool) (ph ph' : ZMod 8)
      (ct ct' de de' bd bd' : Bool) (w w' : List Bool),
      d ≤ u.length →
      (∀ tl2 : List Bool, body.foldl sTr (ph, tl2, u.drop d, ct, de, bd, w)
          = (ph', tl2, u', ct', de', bd', w')) →
      (List.replicate d 1 ++ (body ++ List.replicate d 0)).foldl sTr
          (ph, tl, u, ct, de, bd, w)
        = (ph', tl, u.take d ++ u', ct', de', bd', w') := by
    intro body d tl u u' ph ph' ct ct' de de' bd bd' w w' hd hbody
    have hlen : ((u.take d).reverse ++ tl).length = d + tl.length := by
      simp [List.length_take]
      omega
    have hle : d ≤ ((u.take d).reverse ++ tl).length := by omega
    have hdr : ((u.take d).reverse ++ tl).drop d = tl := by
      have : ((u.take d).reverse).length = d := by simp [List.length_take]; omega
      rw [List.drop_append_of_le_length (by omega)] at *
      simp [List.drop_eq_nil_of_le (le_of_eq this)]
    have htk : (((u.take d).reverse ++ tl).take d).reverse = u.take d := by
      have hlr : ((u.take d).reverse).length = d := by simp [List.length_take]; omega
      rw [List.take_append_of_le_length (le_of_eq hlr.symm)]
      rw [List.take_of_length_le (le_of_eq hlr)]
      exact List.reverse_reverse _
    rw [List.foldl_append, List.foldl_append, hR d ph tl u ct de bd w hd,
      hbody ((u.take d).reverse ++ tl),
      hL d ph' ((u.take d).reverse ++ tl) u' ct' de' bd' w' hle, hdr, htk]
  -- the bodies (BRIDGE-Bc)
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
  have g3s : ∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
      (tl : List Bool),
      [3, 3, 3, 3, 3, 3, 3].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
        = (ph + (if b then 7 else 0), tl, b :: t, ct, de, bd, w) := by
    intro ph t b ct de bd w tl
    have e : ([3, 3, 3, 3, 3, 3, 3] : List ℕ) = [3] ++ ([3] ++ ([3] ++ ([3] ++
        ([3] ++ ([3] ++ [3]))))) := by rfl
    rw [e]
    simp only [List.foldl_append, g3]
    cases b
    · simp
    · simp only [if_true]
      rw [hz7 ph]
  have g4s : ∀ (ph : ZMod 8) (t : List Bool) (b ct de bd : Bool) (w : List Bool)
      (tl : List Bool),
      [4, 4, 4].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
        = (ph + (if b then 6 else 0), tl, b :: t, ct, de, bd, w) := by
    intro ph t b ct de bd w tl
    have e : ([4, 4, 4] : List ℕ) = [4] ++ ([4] ++ [4]) := by rfl
    rw [e]
    simp only [List.foldl_append, g4]
    cases b
    · simp
    · simp only [if_true]
      rw [hz6 ph]
  -- the head cell, as `headI` of the dropped tape
  have hhd : ∀ (i : ℕ) (l : List Bool) (b : Bool), l.drop i = b :: l.drop (i + 1) →
      (l.drop i).headI = b := by
    intro i l b hb
    rw [hb]
    rfl
  refine ⟨hflat, hwrap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (2) T
  · intro i l ph ct de bd w hi
    obtain ⟨b, hb1, hb2⟩ := hcell i l hi
    have hbh := hhd i l b hb1
    have hbody : ∀ tl2 : List Bool, [3].foldl sTr (ph, tl2, l.drop i, ct, de, bd, w)
        = (ph + (if b then 1 else 0), tl2, b :: l.drop (i + 1), ct, de, bd, w) := by
      intro tl2; rw [hb1]; exact g3 ph (l.drop (i + 1)) b ct de bd w tl2
    rw [hwrap [3] i [] l (b :: l.drop (i + 1)) ph (ph + (if b then 1 else 0)) ct ct
      de de bd bd w w (le_of_lt hi) hbody, hbh, ← hsetTake i l b hi, hb2]
  -- (3) T dagger
  · intro i l ph ct de bd w hi
    obtain ⟨b, hb1, hb2⟩ := hcell i l hi
    have hbh := hhd i l b hb1
    have hbody : ∀ tl2 : List Bool,
        [3, 3, 3, 3, 3, 3, 3].foldl sTr (ph, tl2, l.drop i, ct, de, bd, w)
        = (ph + (if b then 7 else 0), tl2, b :: l.drop (i + 1), ct, de, bd, w) := by
      intro tl2; rw [hb1]; exact g3s ph (l.drop (i + 1)) b ct de bd w tl2
    rw [hwrap [3, 3, 3, 3, 3, 3, 3] i [] l (b :: l.drop (i + 1)) ph
      (ph + (if b then 7 else 0)) ct ct de de bd bd w w (le_of_lt hi) hbody, hbh,
      ← hsetTake i l b hi, hb2]
  -- (4) S
  · intro i l ph ct de bd w hi
    obtain ⟨b, hb1, hb2⟩ := hcell i l hi
    have hbh := hhd i l b hb1
    have hbody : ∀ tl2 : List Bool, [4].foldl sTr (ph, tl2, l.drop i, ct, de, bd, w)
        = (ph + (if b then 2 else 0), tl2, b :: l.drop (i + 1), ct, de, bd, w) := by
      intro tl2; rw [hb1]; exact g4 ph (l.drop (i + 1)) b ct de bd w tl2
    rw [hwrap [4] i [] l (b :: l.drop (i + 1)) ph (ph + (if b then 2 else 0)) ct ct
      de de bd bd w w (le_of_lt hi) hbody, hbh, ← hsetTake i l b hi, hb2]
  -- (5) S dagger
  · intro i l ph ct de bd w hi
    obtain ⟨b, hb1, hb2⟩ := hcell i l hi
    have hbh := hhd i l b hb1
    have hbody : ∀ tl2 : List Bool, [4, 4, 4].foldl sTr (ph, tl2, l.drop i, ct, de, bd, w)
        = (ph + (if b then 6 else 0), tl2, b :: l.drop (i + 1), ct, de, bd, w) := by
      intro tl2; rw [hb1]; exact g4s ph (l.drop (i + 1)) b ct de bd w tl2
    rw [hwrap [4, 4, 4] i [] l (b :: l.drop (i + 1)) ph (ph + (if b then 6 else 0)) ct ct
      de de bd bd w w (le_of_lt hi) hbody, hbh, ← hsetTake i l b hi, hb2]
  -- (6) X
  · intro i l ph ct de bd w hi
    obtain ⟨b, hb1, hb2⟩ := hcell i l hi
    have hbh := hhd i l b hb1
    have hbody : ∀ tl2 : List Bool, [5].foldl sTr (ph, tl2, l.drop i, ct, de, bd, w)
        = (ph, tl2, (!b) :: l.drop (i + 1), ct, de, bd, w) := by
      intro tl2; rw [hb1]; exact g5 ph (l.drop (i + 1)) b ct de bd w tl2
    rw [hwrap [5] i [] l ((!b) :: l.drop (i + 1)) ph ph ct ct de de bd bd w w
      (le_of_lt hi) hbody, hbh, ← hsetTake i l (!b) hi]
  -- (7) Hadamard
  · intro i l ph ct de bd w hi
    obtain ⟨b, hb1, hb2⟩ := hcell i l hi
    have hbh := hhd i l b hb1
    have hbody : ∀ tl2 : List Bool, [2].foldl sTr (ph, tl2, l.drop i, ct, de, bd, w)
        = (ph + (if b && w.headI then 4 else 0), tl2, w.headI :: l.drop (i + 1), ct, de,
            bd || w.isEmpty, w.tail) := by
      intro tl2; rw [hb1]; exact g2 ph (l.drop (i + 1)) b ct de bd w tl2
    rw [hwrap [2] i [] l (w.headI :: l.drop (i + 1)) ph
      (ph + (if b && w.headI then 4 else 0)) ct ct de de bd (bd || w.isEmpty) w w.tail
      (le_of_lt hi) hbody, hbh, ← hsetTake i l w.headI hi]
  -- (8) the output-wire test
  · intro i l ph ct de bd w hi
    obtain ⟨b, hb1, hb2⟩ := hcell i l hi
    have hbh := hhd i l b hb1
    have hbody : ∀ tl2 : List Bool, [8].foldl sTr (ph, tl2, l.drop i, ct, de, bd, w)
        = (ph, tl2, b :: l.drop (i + 1), ct, de || !b, bd, w) := by
      intro tl2; rw [hb1]; exact g8 ph (l.drop (i + 1)) b ct de bd w tl2
    rw [hwrap [8] i [] l (b :: l.drop (i + 1)) ph ph ct ct de (de || !b) bd bd w w
      (le_of_lt hi) hbody, hbh, ← hsetTake i l b hi, hb2]
  -- (9) CNOT, control below target
  · intro i j l ph ct de bd w hij hjl
    have hil : i < l.length := by omega
    obtain ⟨b, hb1, hb2⟩ := hcell i l hil
    obtain ⟨c, hc1, hc2⟩ := hcell j l hjl
    have hbh := hhd i l b hb1
    have hch := hhd j l c hc1
    have hdj : i + (j - i) = j := by omega
    -- the inner xor block, wrapped at distance `j - i` inside the tape from wire `i`
    have hinner : ∀ tl3 : List Bool,
        (List.replicate (j - i) 1 ++ ([7] ++ List.replicate (j - i) 0)).foldl sTr
            (ph, tl3, b :: l.drop (i + 1), b, de, bd, w)
          = (ph, tl3, (b :: l.drop (i + 1)).take (j - i)
              ++ ((xor c b) :: l.drop (j + 1)), b, de, bd, w) := by
      intro tl3
      have hlen : (j - i) ≤ (b :: l.drop (i + 1)).length := by
        simp [List.length_drop]
        omega
      have hdrp : (b :: l.drop (i + 1)).drop (j - i) = c :: l.drop (j + 1) := by
        rw [← hb1, hdd l i (j - i), hdj, hc1]
      have hb7 : ∀ tl4 : List Bool,
          [7].foldl sTr (ph, tl4, (b :: l.drop (i + 1)).drop (j - i), b, de, bd, w)
            = (ph, tl4, (xor c b) :: l.drop (j + 1), b, de, bd, w) := by
        intro tl4
        rw [hdrp]
        exact g7 ph (l.drop (j + 1)) c b de bd w tl4
      exact hwrap [7] (j - i) tl3 (b :: l.drop (i + 1)) ((xor c b) :: l.drop (j + 1))
        ph ph b b de de bd bd w w hlen hb7
    have hbody : ∀ tl2 : List Bool,
        ([6] ++ (List.replicate (j - i) 1 ++ ([7] ++ List.replicate (j - i) 0))).foldl sTr
            (ph, tl2, l.drop i, ct, de, bd, w)
          = (ph, tl2, (l.drop i).take (j - i) ++ ((xor c b) :: l.drop (j + 1)), b,
              de, bd, w) := by
      intro tl2
      rw [hb1, List.foldl_append, g6 ph (l.drop (i + 1)) b ct de bd w tl2]
      exact hinner tl2
    rw [hwrap ([6] ++ (List.replicate (j - i) 1 ++ ([7] ++ List.replicate (j - i) 0))) i
      [] l ((l.drop i).take (j - i) ++ ((xor c b) :: l.drop (j + 1))) ph ph ct b de de
      bd bd w w (le_of_lt hil) hbody, ← List.append_assoc, hcomb i l (j - i), hdj,
      ← hsetTake j l (xor c b) hjl, hbh, hch]
  -- (10) CNOT, target below control
  · intro i j l ph ct de bd w hji hil
    have hjl : j < l.length := by omega
    obtain ⟨b, hb1, hb2⟩ := hcell j l hjl
    obtain ⟨c, hc1, hc2⟩ := hcell i l hil
    have hbh := hhd j l b hb1
    have hch := hhd i l c hc1
    have hdj : j + (i - j) = i := by omega
    have hre : (List.replicate (i - j) 1 ++ ([6] ++ (List.replicate (i - j) 0 ++ [7])))
        = (List.replicate (i - j) 1 ++ ([6] ++ List.replicate (i - j) 0)) ++ [7] := by
      simp [List.append_assoc]
    -- the latch, wrapped at distance `i - j` inside the tape from wire `j`
    have hlatch : ∀ tl3 : List Bool,
        (List.replicate (i - j) 1 ++ ([6] ++ List.replicate (i - j) 0)).foldl sTr
            (ph, tl3, b :: l.drop (j + 1), ct, de, bd, w)
          = (ph, tl3, (b :: l.drop (j + 1)).take (i - j)
              ++ (c :: l.drop (i + 1)), c, de, bd, w) := by
      intro tl3
      have hlen : (i - j) ≤ (b :: l.drop (j + 1)).length := by
        simp [List.length_drop]
        omega
      have hdrp : (b :: l.drop (j + 1)).drop (i - j) = c :: l.drop (i + 1) := by
        rw [← hb1, hdd l j (i - j), hdj, hc1]
      have hb6 : ∀ tl4 : List Bool,
          [6].foldl sTr (ph, tl4, (b :: l.drop (j + 1)).drop (i - j), ct, de, bd, w)
            = (ph, tl4, c :: l.drop (i + 1), c, de, bd, w) := by
        intro tl4
        rw [hdrp]
        exact g6 ph (l.drop (i + 1)) c ct de bd w tl4
      exact hwrap [6] (i - j) tl3 (b :: l.drop (j + 1)) (c :: l.drop (i + 1))
        ph ph ct c de de bd bd w w hlen hb6
    have hres : (b :: l.drop (j + 1)).take (i - j) ++ (c :: l.drop (i + 1))
        = b :: l.drop (j + 1) := by
      have hdrp : (b :: l.drop (j + 1)).drop (i - j) = c :: l.drop (i + 1) := by
        rw [← hb1, hdd l j (i - j), hdj, hc1]
      rw [← hdrp]
      exact List.take_append_drop (i - j) (b :: l.drop (j + 1))
    have hbody : ∀ tl2 : List Bool,
        (List.replicate (i - j) 1 ++ ([6] ++ (List.replicate (i - j) 0 ++ [7]))).foldl sTr
            (ph, tl2, l.drop j, ct, de, bd, w)
          = (ph, tl2, (xor b c) :: l.drop (j + 1), c, de, bd, w) := by
      intro tl2
      rw [hb1, hre, List.foldl_append, hlatch tl2, hres]
      exact g7 ph (l.drop (j + 1)) b c de bd w tl2
    rw [hwrap (List.replicate (i - j) 1 ++ ([6] ++ (List.replicate (i - j) 0 ++ [7]))) j
      [] l ((xor b c) :: l.drop (j + 1)) ph ph ct c de de bd bd w w (le_of_lt hjl) hbody,
      ← hsetTake j l (xor b c) hjl, hbh, hch]

end BQPBridgeReference
