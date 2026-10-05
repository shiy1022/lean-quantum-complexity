import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Mathlib.Data.ZMod.Basic
import Theorems.Thm_ShiBQP_opcode_stream_head_safety_and_adjoint_blocks

namespace BQPReferenceValidation.Source15
/-
CHECK-1fc.  The route-(A) well-formedness obligations for the head-relative op stream of
`CHECK-1e`/`CHECK-1f`, stated against an ABSTRACT transition `sTr` pinned only by the
opcode table, so the file never mentions an encoding.

The hazard this discharges: opcode 0 ("move the head one wire left") is `tl.tail`,
`tl.headI :: tr`.  At the LEFT END (`tl = []`) that is NOT a move -- `[].tail = []` and
`[].headI = false`, so the head stays at wire 0 and a fresh `false` cell is PREPENDED to
the right tape.  Every wire index shifts by one.  A compiled program must provably never
move left past wire 0.

We give a decidable left-safety analyser `mv : List ℕ → ℕ → Option ℕ` (the head position
after the program, `none` if the program would step left at wire 0 or use an opcode
outside 0..9) and prove that whenever it succeeds the head position after the run is
exactly its arithmetic net displacement -- which is false in the presence of drift, so the
analyser certifies drift-freedom.

We also verify the blocks route (A) needs to compile `U ; Π-test ; U† ; endpoint-test` in
the EXISTING opcode set:
  T followed by T† is eight opcode-3s and is the identity;
  S followed by S† is four opcode-4s and is the identity;
  X is self-inverse;
  "wire = 1" is opcode 8 and "wire = 0" is opcode 5, 8, 5;
  the CNOT block `6,1,7` is undone by `0,6,1,7`, whose left move is safe because the block
  itself pushed the cell it moves back onto.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

private abbrev St : Type := ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool

/-- The left-safety analyser: the head position after the program, `none` if some step
would move left at wire 0, or would use an opcode outside `0..9`. -/
private def mvf : List ℕ → ℕ → Option ℕ
  | [], k => some k
  | c :: P, k =>
      if c % 16 = 0 then
        match k with
        | 0 => none
        | k' + 1 => mvf P k'
      else if c % 16 = 1 then mvf P (k + 1)
      else if c % 16 ≤ 9 then mvf P k
      else none

private lemma mvf_nil (k : ℕ) : mvf [] k = some k := rfl

private lemma mvf_zero (c : ℕ) (P : List ℕ) (h : c % 16 = 0) : mvf (c :: P) 0 = none := by
  simp [mvf, h]

private lemma mvf_left (c : ℕ) (P : List ℕ) (k : ℕ) (h : c % 16 = 0) :
    mvf (c :: P) (k + 1) = mvf P k := by
  simp [mvf, h]

private lemma mvf_right (c : ℕ) (P : List ℕ) (k : ℕ) (h : c % 16 = 1) :
    mvf (c :: P) k = mvf P (k + 1) := by
  simp [mvf, h]

private lemma mvf_stay (c : ℕ) (P : List ℕ) (k : ℕ) (h1 : 2 ≤ c % 16) (h2 : c % 16 ≤ 9) :
    mvf (c :: P) k = mvf P k := by
  have e0 : ¬ (c % 16 = 0) := by omega
  have e1 : ¬ (c % 16 = 1) := by omega
  simp [mvf, e0, e1, h2]

private lemma mvf_bad (c : ℕ) (P : List ℕ) (k : ℕ) (h : 10 ≤ c % 16) :
    mvf (c :: P) k = none := by
  have e0 : ¬ (c % 16 = 0) := by omega
  have e1 : ¬ (c % 16 = 1) := by omega
  have e2 : ¬ (c % 16 ≤ 9) := by omega
  simp [mvf, e0, e1, e2]

theorem _root_.BQPReferenceValidation.candidate15 :
    ∀ sTr : (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool) → ℕ →
        (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool),
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
      ∃ mv : List ℕ → ℕ → Option ℕ,
        -- (1) the analyser, by its recursion clauses
        (∀ k : ℕ, mv [] k = some k)
        ∧ (∀ (c : ℕ) (P : List ℕ), c % 16 = 0 → mv (c :: P) 0 = none)
        ∧ (∀ (c : ℕ) (P : List ℕ) (k : ℕ), c % 16 = 0 → mv (c :: P) (k + 1) = mv P k)
        ∧ (∀ (c : ℕ) (P : List ℕ) (k : ℕ), c % 16 = 1 → mv (c :: P) k = mv P (k + 1))
        ∧ (∀ (c : ℕ) (P : List ℕ) (k : ℕ), 2 ≤ c % 16 → c % 16 ≤ 9 →
              mv (c :: P) k = mv P k)
        ∧ (∀ (c : ℕ) (P : List ℕ) (k : ℕ), 10 ≤ c % 16 → mv (c :: P) k = none)
        -- (2) HEAD SAFETY.  If the analyser succeeds from head position `k`, the head
        -- position after the whole run is exactly its arithmetic net displacement.  Left
        -- drift would pin the position at 0, so this certifies that no cell was inserted.
        ∧ (∀ (P : List ℕ) (k j : ℕ), mv P k = some j →
              ∀ s : (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool),
                s.2.1.length = k → (P.foldl sTr s).2.1.length = j)
        -- (3) THE DRIFT ITSELF.  At the left end opcode 0 does not move the head: it
        -- prepends a cell, so the cell that was at wire 0 is afterwards at wire 1.
        ∧ (∀ (ph : ZMod 8) (tr : List Bool) (ct de bd : Bool) (w : List Bool),
              sTr (ph, [], tr, ct, de, bd, w) 0 = (ph, [], false :: tr, ct, de, bd, w))
        ∧ (∀ (P : List ℕ), mv (0 :: P) 0 = none)
        -- (4) route (A) blocks: the adjoints are inside the existing opcode set
        ∧ (∀ (ph : ZMod 8) (tl t : List Bool) (b ct de bd : Bool) (w : List Bool),
              [3, 3, 3, 3, 3, 3, 3, 3].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
                = (ph, tl, b :: t, ct, de, bd, w))
        ∧ (∀ (ph : ZMod 8) (tl t : List Bool) (b ct de bd : Bool) (w : List Bool),
              [4, 4, 4, 4].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
                = (ph, tl, b :: t, ct, de, bd, w))
        ∧ (∀ (ph : ZMod 8) (tl t : List Bool) (b ct de bd : Bool) (w : List Bool),
              [5, 5].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
                = (ph, tl, b :: t, ct, de, bd, w))
        -- (5) the two endpoint tests: "wire = 1" is opcode 8, "wire = 0" is 5, 8, 5
        ∧ (∀ (ph : ZMod 8) (tl t : List Bool) (b ct de bd : Bool) (w : List Bool),
              [8].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
                = (ph, tl, b :: t, ct, de || !b, bd, w))
        ∧ (∀ (ph : ZMod 8) (tl t : List Bool) (b ct de bd : Bool) (w : List Bool),
              [5, 8, 5].foldl sTr (ph, tl, b :: t, ct, de, bd, w)
                = (ph, tl, b :: t, ct, de || b, bd, w))
        -- (6) the CNOT block `6,1,7` is undone by `0,6,1,7`; the left move is safe
        -- because the block itself pushed the cell it moves back onto
        ∧ (∀ (ph : ZMod 8) (tl t : List Bool) (a b ct de bd : Bool) (w : List Bool),
              [6, 1, 7, 0, 6, 1, 7].foldl sTr (ph, tl, a :: b :: t, ct, de, bd, w)
                = (ph, a :: tl, b :: t, a, de, bd, w))
        -- (7) the doubled one-qubit witness `H ; test ; H ; X ; test ; X` is left-safe at
        -- every head position, so route (A)'s program never drifts
        ∧ (∀ k : ℕ, mv [2, 8, 2, 5, 8, 5] k = some k) := by
  intro sTr hS
  have o0 : ∀ (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
      sTr (ph, tl, tr, ct, de, bd, w) 0 = (ph, tl.tail, tl.headI :: tr, ct, de, bd, w) :=
    fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).1
  have o1 : ∀ (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
      sTr (ph, tl, tr, ct, de, bd, w) 1 = (ph, tr.headI :: tl, tr.tail, ct, de, bd, w) :=
    fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.1
  have o3 : ∀ (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
      sTr (ph, tl, tr, ct, de, bd, w) 3
        = (ph + (if tr.headI then 1 else 0), tl, tr.headI :: tr.tail, ct, de, bd, w) :=
    fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.2.1
  have o4 : ∀ (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
      sTr (ph, tl, tr, ct, de, bd, w) 4
        = (ph + (if tr.headI then 2 else 0), tl, tr.headI :: tr.tail, ct, de, bd, w) :=
    fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.2.2.1
  have o5 : ∀ (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
      sTr (ph, tl, tr, ct, de, bd, w) 5 = (ph, tl, (!tr.headI) :: tr.tail, ct, de, bd, w) :=
    fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.2.2.2.1
  have o6 : ∀ (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
      sTr (ph, tl, tr, ct, de, bd, w) 6
        = (ph, tl, tr.headI :: tr.tail, tr.headI, de, bd, w) :=
    fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.2.2.2.2.1
  have o7 : ∀ (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
      sTr (ph, tl, tr, ct, de, bd, w) 7
        = (ph, tl, (xor tr.headI ct) :: tr.tail, ct, de, bd, w) :=
    fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.2.2.2.2.2.1
  have o8 : ∀ (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
      sTr (ph, tl, tr, ct, de, bd, w) 8
        = (ph, tl, tr.headI :: tr.tail, ct, de || !tr.headI, bd, w) :=
    fun ph tl tr ct de bd w => (hS ph tl tr ct de bd w).2.2.2.2.2.2.2.2.1
  have safe : ∀ (P : List ℕ) (k j : ℕ), mvf P k = some j →
      ∀ s : St, s.2.1.length = k → (P.foldl sTr s).2.1.length = j := by
    intro P
    induction P with
    | nil =>
        intro k j hmv s hs
        rw [mvf_nil] at hmv
        have : k = j := by
          exact Option.some.inj hmv
        rw [List.foldl_nil, hs, this]
    | cons c P ih =>
        intro k j hmv s hs
        obtain ⟨ph, tl, tr, ct, de, bd, w⟩ := s
        have hsl : tl.length = k := hs
        have gm := (hS ph tl tr ct de bd w).2.2.2.2.2.2.2.2.2.2
        have hstep : (c :: P).foldl sTr (ph, tl, tr, ct, de, bd, w)
            = P.foldl sTr (sTr (ph, tl, tr, ct, de, bd, w) (c % 16)) := by
          rw [List.foldl_cons, gm c]
        have h16 : c % 16 = 0 ∨ c % 16 = 1 ∨ (2 ≤ c % 16 ∧ c % 16 ≤ 9) ∨ 10 ≤ c % 16 := by
          omega
        rcases h16 with h | h | h | h
        · cases k with
          | zero =>
              rw [mvf_zero c P h] at hmv
              exact absurd hmv (by simp)
          | succ k' =>
              rw [mvf_left c P k' h] at hmv
              rw [hstep, h, o0]
              refine ih k' j hmv _ ?_
              show tl.tail.length = k'
              rw [List.length_tail, hsl]
              omega
        · rw [mvf_right c P k h] at hmv
          rw [hstep, h, o1]
          refine ih (k + 1) j hmv _ ?_
          show (tr.headI :: tl).length = k + 1
          rw [List.length_cons, hsl]
        · rw [mvf_stay c P k h.1 h.2] at hmv
          rw [hstep]
          refine ih k j hmv _ ?_
          have hkey : (sTr (ph, tl, tr, ct, de, bd, w) (c % 16)).2.1 = tl := by
            have h9 : c % 16 = 2 ∨ c % 16 = 3 ∨ c % 16 = 4 ∨ c % 16 = 5 ∨ c % 16 = 6 ∨
                c % 16 = 7 ∨ c % 16 = 8 ∨ c % 16 = 9 := by omega
            have g2 := (hS ph tl tr ct de bd w).2.2.1
            have g9 := (hS ph tl tr ct de bd w).2.2.2.2.2.2.2.2.2.1
            rcases h9 with e | e | e | e | e | e | e | e
            · rw [e, g2]
            · rw [e, o3]
            · rw [e, o4]
            · rw [e, o5]
            · rw [e, o6]
            · rw [e, o7]
            · rw [e, o8]
            · rw [e, g9]
          show (sTr (ph, tl, tr, ct, de, bd, w) (c % 16)).2.1.length = k
          rw [hkey, hsl]
        · rw [mvf_bad c P k h] at hmv
          exact absurd hmv (by simp)
  have h8z : ∀ x : ZMod 8, x + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = x := by decide
  have h4z : ∀ x : ZMod 8, x + 2 + 2 + 2 + 2 = x := by decide
  refine ⟨mvf, mvf_nil, fun c P h => mvf_zero c P h, fun c P k h => mvf_left c P k h,
    fun c P k h => mvf_right c P k h, fun c P k h1 h2 => mvf_stay c P k h1 h2,
    fun c P k h => mvf_bad c P k h, safe, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ph tr ct de bd w
    rw [o0]
    rfl
  · intro P
    exact mvf_zero 0 P rfl
  · intro ph tl t b ct de bd w
    cases b <;> simp [o3, h8z]
  · intro ph tl t b ct de bd w
    cases b <;> simp [o4, h4z]
  · intro ph tl t b ct de bd w
    simp [o5]
  · intro ph tl t b ct de bd w
    simp [o8]
  · intro ph tl t b ct de bd w
    simp [o5, o8]
  · intro ph tl t a b ct de bd w
    cases a <;> cases b <;> simp [o0, o1, o6, o7]
  · intro k
    simp [mvf]

end BQPReferenceValidation.Source15

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate15
    let target ← getConstInfo ``ShiBQP.opcode_stream_head_safety_and_adjoint_blocks
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.opcode_stream_head_safety_and_adjoint_blocks"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.opcode_stream_head_safety_and_adjoint_blocks"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.opcode_stream_head_safety_and_adjoint_blocks"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate15
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.opcode_stream_head_safety_and_adjoint_blocks; axioms {axioms}"
