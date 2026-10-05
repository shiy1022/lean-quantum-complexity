-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.opcode_stream_head_safety_and_adjoint_blocks`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_opcode_stream_head_safety_and_adjoint_blocks`. The real proof is on prove2.me.
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace ShiBQP

theorem opcode_stream_head_safety_and_adjoint_blocks :
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
  sorry

end ShiBQP
