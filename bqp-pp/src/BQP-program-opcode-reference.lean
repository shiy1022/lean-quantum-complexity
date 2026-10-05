/-
BRIDGE-A.  The ALPHABET-GENERIC half of the semantic bridge's plumbing: everything about
the `CHECK-1f` opcode stream (`sTr`, `hc`, `ev`) and the `CHECK-1fc` left-safety analyser
`mv` that does NOT mention `ShiShallow.Instr`, so the file stays outside the encoding's
transitive name closure.

Four groups.

(a) `mv` is a Kleisli homomorphism for list concatenation, and the two balanced move
    blocks `replicate r 1` (r steps right) and `replicate r 0` (r steps left) behave as
    arithmetic.  Together these reduce a compiler's head-drift obligation
    `mv (comp gs) 0 = some j` to an induction over blocks instead of a `decide` on a
    concrete program.

(b) A program with no opcode-2 has Hadamard count zero -- this is what makes an
    input-loading prefix of moves and `X` gates contribute no witness bits.

(c) The WITNESS-TAPE DISCIPLINE: the only opcode that consumes a witness bit is 2, so
    after any run the remaining witness is exactly `w.drop (hc P)`; the underflow flag
    `bd` is true whenever `w.length < hc P` and stays false when `hc P ≤ w.length` and
    the program has no opcode 9; and `bd`, `de` are both sticky.

(d) Consequently `ev P w = none` for EVERY witness of the wrong length -- conjunct (7)
    of the semantic bridge, proved once and for all programs rather than for a
    particular compiler's output.
-/
import Mathlib.Data.ZMod.Basic

namespace BQPBridgeReference

set_option autoImplicit false
set_option maxHeartbeats 1600000

private abbrev St : Type := ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool

theorem opcodeLaws :
    ∀ (sTr : (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool) → ℕ →
          (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool))
      (hc : List ℕ → ℕ) (ev : List ℕ → List Bool → Option ℕ)
      (mv : List ℕ → ℕ → Option ℕ),
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
      -- CHECK-1f (II): the Hadamard count and the one-branch evaluator
      hc [] = 0 →
      (∀ (c : ℕ) (Q : List ℕ), hc (c :: Q) = (if c % 16 = 2 then 1 else 0) + hc Q) →
      (∀ (Q : List ℕ) (bs : List Bool),
          ev Q bs = (match Q.foldl sTr (0, [], [], false, false, false, bs) with
                     | (ph, _, _, _, de, bd, w) =>
                         if de || bd || !w.isEmpty then none else some ph.val)) →
      -- CHECK-1fc (1): the left-safety analyser, by its recursion clauses
      (∀ k : ℕ, mv [] k = some k) →
      (∀ (c : ℕ) (P : List ℕ), c % 16 = 0 → mv (c :: P) 0 = none) →
      (∀ (c : ℕ) (P : List ℕ) (k : ℕ), c % 16 = 0 → mv (c :: P) (k + 1) = mv P k) →
      (∀ (c : ℕ) (P : List ℕ) (k : ℕ), c % 16 = 1 → mv (c :: P) k = mv P (k + 1)) →
      (∀ (c : ℕ) (P : List ℕ) (k : ℕ), 2 ≤ c % 16 → c % 16 ≤ 9 →
          mv (c :: P) k = mv P k) →
      (∀ (c : ℕ) (P : List ℕ) (k : ℕ), 10 ≤ c % 16 → mv (c :: P) k = none) →
      -- (a) the analyser composes, and the balanced move blocks are arithmetic
      (∀ (P Q : List ℕ) (k : ℕ), mv (P ++ Q) k = (mv P k).bind (fun j => mv Q j))
      ∧ (∀ (r k : ℕ), mv (List.replicate r 1) k = some (k + r))
      ∧ (∀ (r k : ℕ), mv (List.replicate r 0) (k + r) = some k)
      -- (b) no opcode 2 means no witness bits
      ∧ (∀ P : List ℕ, (∀ c ∈ P, c % 16 ≠ 2) → hc P = 0)
      -- (c) the witness tape is consumed exactly `hc P` times, and the flags are sticky
      ∧ (∀ P : List ℕ, (∀ c ∈ P, c % 16 ≤ 9) →
          ∀ (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
            (P.foldl sTr (ph, tl, tr, ct, de, bd, w)).2.2.2.2.2.2 = w.drop (hc P))
      ∧ (∀ P : List ℕ, (∀ c ∈ P, c % 16 ≤ 9) →
          ∀ (ph : ZMod 8) (tl tr : List Bool) (ct de : Bool) (w : List Bool),
            (P.foldl sTr (ph, tl, tr, ct, de, true, w)).2.2.2.2.2.1 = true)
      ∧ (∀ P : List ℕ, (∀ c ∈ P, c % 16 ≤ 9) →
          ∀ (ph : ZMod 8) (tl tr : List Bool) (ct bd : Bool) (w : List Bool),
            (P.foldl sTr (ph, tl, tr, ct, true, bd, w)).2.2.2.2.1 = true)
      ∧ (∀ P : List ℕ, (∀ c ∈ P, c % 16 ≤ 9) →
          ∀ (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
            w.length < hc P →
              (P.foldl sTr (ph, tl, tr, ct, de, bd, w)).2.2.2.2.2.1 = true)
      ∧ (∀ P : List ℕ, (∀ c ∈ P, c % 16 ≤ 9) → (∀ c ∈ P, c % 16 ≠ 9) →
          ∀ (ph : ZMod 8) (tl tr : List Bool) (ct de : Bool) (w : List Bool),
            hc P ≤ w.length →
              (P.foldl sTr (ph, tl, tr, ct, de, false, w)).2.2.2.2.2.1 = false)
      -- (d) every witness of the wrong length is rejected
      ∧ (∀ (P : List ℕ) (w : List Bool), (∀ c ∈ P, c % 16 ≤ 9) →
          w.length ≠ hc P → ev P w = none) := by
  intro sTr hc ev mv hS hc0 hcC hev hmvN hmvZ0 hmvZS hmvR hmvS hmvB
  -- the per-step facts we need, for any opcode in `0..9`
  have hstep : ∀ (s : St) (c : ℕ), c % 16 ≤ 9 →
      ((sTr s c).2.2.2.2.2.2
          = (if c % 16 = 2 then s.2.2.2.2.2.2.tail else s.2.2.2.2.2.2))
      ∧ ((sTr s c).2.2.2.2.2.1
          = (if c % 16 = 2 then s.2.2.2.2.2.1 || s.2.2.2.2.2.2.isEmpty
             else if c % 16 = 9 then true else s.2.2.2.2.2.1))
      ∧ (s.2.2.2.2.1 = true → (sTr s c).2.2.2.2.1 = true) := by
    intro s c hc9
    obtain ⟨ph, tl, tr, ct, de, bd, w⟩ := s
    have t := hS ph tl tr ct de bd w
    have hred := t.2.2.2.2.2.2.2.2.2.2 c
    have hd : c % 16 = 0 ∨ c % 16 = 1 ∨ c % 16 = 2 ∨ c % 16 = 3 ∨ c % 16 = 4
        ∨ c % 16 = 5 ∨ c % 16 = 6 ∨ c % 16 = 7 ∨ c % 16 = 8 ∨ c % 16 = 9 := by omega
    rcases hd with h|h|h|h|h|h|h|h|h|h <;> rw [hred, h] <;>
      simp [t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1,
        t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.1,
        t.2.2.2.2.2.2.2.2.2.1] <;>
      try exact fun hh => Or.inl hh
  -- (a)
  have hcat : ∀ (P Q : List ℕ) (k : ℕ), mv (P ++ Q) k = (mv P k).bind (fun j => mv Q j) := by
    intro P
    induction P with
    | nil => intro Q k; rw [List.nil_append, hmvN k]; rfl
    | cons c P ih =>
      intro Q k
      have h16 : c % 16 = 0 ∨ c % 16 = 1 ∨ (2 ≤ c % 16 ∧ c % 16 ≤ 9) ∨ 10 ≤ c % 16 := by
        omega
      rcases h16 with h|h|⟨h1,h2⟩|h
      · cases k with
        | zero => rw [List.cons_append, hmvZ0 c (P ++ Q) h, hmvZ0 c P h]; rfl
        | succ k => rw [List.cons_append, hmvZS c (P ++ Q) k h, hmvZS c P k h, ih]
      · rw [List.cons_append, hmvR c (P ++ Q) k h, hmvR c P k h, ih]
      · rw [List.cons_append, hmvS c (P ++ Q) k h1 h2, hmvS c P k h1 h2, ih]
      · rw [List.cons_append, hmvB c (P ++ Q) k h, hmvB c P k h]; rfl
  have hrep1 : ∀ (r k : ℕ), mv (List.replicate r 1) k = some (k + r) := by
    intro r
    induction r with
    | zero => intro k; rw [List.replicate_zero, hmvN k, Nat.add_zero]
    | succ r ih =>
      intro k
      rw [List.replicate_succ, hmvR 1 _ k (by omega), ih]
      congr 1
      omega
  have hrep0 : ∀ (r k : ℕ), mv (List.replicate r 0) (k + r) = some k := by
    intro r
    induction r with
    | zero => intro k; rw [List.replicate_zero, Nat.add_zero, hmvN k]
    | succ r ih =>
      intro k
      have he : k + (r + 1) = (k + r) + 1 := by omega
      rw [List.replicate_succ, he, hmvZS 0 _ (k + r) (by omega), ih]
  -- (b)
  have hczero : ∀ P : List ℕ, (∀ c ∈ P, c % 16 ≠ 2) → hc P = 0 := by
    intro P
    induction P with
    | nil => intro _; exact hc0
    | cons c P ih =>
      intro h
      rw [hcC, if_neg (h c (by simp)), ih (fun d hd => h d (by simp [hd])), Nat.add_zero]
  -- (c)
  have hdrop : ∀ P : List ℕ, (∀ c ∈ P, c % 16 ≤ 9) → ∀ s : St,
      (P.foldl sTr s).2.2.2.2.2.2 = s.2.2.2.2.2.2.drop (hc P) := by
    intro P
    induction P with
    | nil => intro _ s; rw [List.foldl_nil, hc0, List.drop_zero]
    | cons c P ih =>
      intro hP s
      have h9 : c % 16 ≤ 9 := hP c (by simp)
      have hrest : ∀ d ∈ P, d % 16 ≤ 9 := fun d hd => hP d (by simp [hd])
      rw [List.foldl_cons, ih hrest, (hstep s c h9).1, hcC]
      by_cases h2 : c % 16 = 2
      · rw [if_pos h2, if_pos h2, ← List.drop_one, List.drop_drop]
        all_goals (congr 1; all_goals omega)
      · rw [if_neg h2, if_neg h2, Nat.zero_add]
  have hbd : ∀ P : List ℕ, (∀ c ∈ P, c % 16 ≤ 9) → ∀ s : St,
      s.2.2.2.2.2.1 = true → (P.foldl sTr s).2.2.2.2.2.1 = true := by
    intro P
    induction P with
    | nil => intro _ s h; exact h
    | cons c P ih =>
      intro hP s h
      have h9 : c % 16 ≤ 9 := hP c (by simp)
      have hrest : ∀ d ∈ P, d % 16 ≤ 9 := fun d hd => hP d (by simp [hd])
      refine ih hrest _ ?_
      rw [(hstep s c h9).2.1, h]
      by_cases h2 : c % 16 = 2
      · rw [if_pos h2]; simp
      · rw [if_neg h2]
        by_cases h9' : c % 16 = 9
        · rw [if_pos h9']
        · rw [if_neg h9']
  have hde : ∀ P : List ℕ, (∀ c ∈ P, c % 16 ≤ 9) → ∀ s : St,
      s.2.2.2.2.1 = true → (P.foldl sTr s).2.2.2.2.1 = true := by
    intro P
    induction P with
    | nil => intro _ s h; exact h
    | cons c P ih =>
      intro hP s h
      have h9 : c % 16 ≤ 9 := hP c (by simp)
      have hrest : ∀ d ∈ P, d % 16 ≤ 9 := fun d hd => hP d (by simp [hd])
      exact ih hrest _ ((hstep s c h9).2.2 h)
  have hunder : ∀ P : List ℕ, (∀ c ∈ P, c % 16 ≤ 9) → ∀ s : St,
      s.2.2.2.2.2.2.length < hc P → (P.foldl sTr s).2.2.2.2.2.1 = true := by
    intro P
    induction P with
    | nil => intro _ s h; rw [hc0] at h; omega
    | cons c P ih =>
      intro hP s h
      have h9 : c % 16 ≤ 9 := hP c (by simp)
      have hrest : ∀ d ∈ P, d % 16 ≤ 9 := fun d hd => hP d (by simp [hd])
      rw [hcC] at h
      rw [List.foldl_cons]
      by_cases h2 : c % 16 = 2
      · rw [if_pos h2] at h
        rcases List.eq_nil_or_concat s.2.2.2.2.2.2 with hw | hw
        · refine hbd P hrest _ ?_
          rw [(hstep s c h9).2.1, if_pos h2, hw]
          simp
        · refine ih hrest _ ?_
          rw [(hstep s c h9).1, if_pos h2]
          have hpos : 0 < s.2.2.2.2.2.2.length := by
            obtain ⟨l, a, hla⟩ := hw
            rw [hla]
            simp
          rw [List.length_tail]
          omega
      · rw [if_neg h2, Nat.zero_add] at h
        refine ih hrest _ ?_
        rw [(hstep s c h9).1, if_neg h2]
        exact h
  have hnound : ∀ P : List ℕ, (∀ c ∈ P, c % 16 ≤ 9) → (∀ c ∈ P, c % 16 ≠ 9) → ∀ s : St,
      s.2.2.2.2.2.1 = false → hc P ≤ s.2.2.2.2.2.2.length →
        (P.foldl sTr s).2.2.2.2.2.1 = false := by
    intro P
    induction P with
    | nil => intro _ _ s h _; exact h
    | cons c P ih =>
      intro hP hP9 s h hlen
      have h9 : c % 16 ≤ 9 := hP c (by simp)
      have h9' : c % 16 ≠ 9 := hP9 c (by simp)
      have hrest : ∀ d ∈ P, d % 16 ≤ 9 := fun d hd => hP d (by simp [hd])
      have hrest9 : ∀ d ∈ P, d % 16 ≠ 9 := fun d hd => hP9 d (by simp [hd])
      rw [hcC] at hlen
      rw [List.foldl_cons]
      by_cases h2 : c % 16 = 2
      · rw [if_pos h2] at hlen
        have hpos : 0 < s.2.2.2.2.2.2.length := by omega
        have hne : s.2.2.2.2.2.2.isEmpty = false := by
          cases hcase : s.2.2.2.2.2.2 with
          | nil => rw [hcase] at hpos; simp at hpos
          | cons a l => simp
        refine ih hrest hrest9 _ ?_ ?_
        · rw [(hstep s c h9).2.1, if_pos h2, h, hne]
          all_goals rfl
        · rw [(hstep s c h9).1, if_pos h2, List.length_tail]
          omega
      · rw [if_neg h2, Nat.zero_add] at hlen
        refine ih hrest hrest9 _ ?_ ?_
        · rw [(hstep s c h9).2.1, if_neg h2, if_neg h9', h]
        · rw [(hstep s c h9).1, if_neg h2]
          exact hlen
  -- (d)
  have hevnone : ∀ (P : List ℕ) (w : List Bool),
      ((P.foldl sTr (0, [], [], false, false, false, w)).2.2.2.2.2.1 = true
        ∨ (P.foldl sTr (0, [], [], false, false, false, w)).2.2.2.2.2.2 ≠ []) →
      ev P w = none := by
    intro P w h
    rw [hev P w]
    rcases hq : (P.foldl sTr ((0 : ZMod 8), ([] : List Bool), ([] : List Bool),
        false, false, false, w)) with ⟨ph, tl, tr, ct, de, bd, wf⟩
    rw [hq] at h
    rcases h with h | h
    · simp only at h
      simp [h]
    · simp only at h
      have : wf.isEmpty = false := by
        rcases wf with _ | ⟨a, l⟩
        · exact absurd rfl h
        · simp
      simp [this]
  refine ⟨hcat, hrep1, hrep0, hczero,
    fun P hP ph tl tr ct de bd w => hdrop P hP (ph, tl, tr, ct, de, bd, w),
    fun P hP ph tl tr ct de w => hbd P hP (ph, tl, tr, ct, de, true, w) rfl,
    fun P hP ph tl tr ct bd w => hde P hP (ph, tl, tr, ct, true, bd, w) rfl,
    fun P hP ph tl tr ct de bd w h => hunder P hP (ph, tl, tr, ct, de, bd, w) h,
    fun P hP hP9 ph tl tr ct de w h =>
      hnound P hP hP9 (ph, tl, tr, ct, de, false, w) rfl h, ?_⟩
  intro P w hP hne
  rcases Nat.lt_or_ge w.length (hc P) with hlt | hge
  · refine hevnone P w (Or.inl ?_)
    exact hunder P hP _ hlt
  · refine hevnone P w (Or.inr ?_)
    have hd := hdrop P hP ((0 : ZMod 8), ([] : List Bool), ([] : List Bool),
      false, false, false, w)
    rw [hd]
    intro hcon
    have : (w.drop (hc P)).length = 0 := by rw [hcon]; rfl
    rw [List.length_drop] at this
    omega


end BQPBridgeReference
