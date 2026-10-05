import «AMPUNI-layout-data»

set_option autoImplicit false

namespace ShiTMLayoutMachine

/-- Once the wire index has passed a prefix's widths, the evaluator sees exactly the
remaining pieces and the local index. -/
theorem depth_append_skip (headPieces suffix : List (Nat × Nat)) (i : Nat) :
    depth (headPieces ++ suffix) ((headPieces.map Prod.fst).sum + i) = depth suffix i := by
  induction headPieces with
  | nil => simp [depth]
  | cons p headPieces ih =>
    rcases p with ⟨a, z⟩
    have hn : ¬(a + (headPieces.map Prod.fst).sum + i < a) := by omega
    have hs : a + (headPieces.map Prod.fst).sum + i - a =
        (headPieces.map Prod.fst).sum + i := by omega
    simp only [List.cons_append, List.map_cons, List.sum_cons, depth]
    rw [if_neg hn, hs, ih]

/-- A suffix cannot affect evaluation of an index contained in the prefix. -/
theorem depth_append_within (headPieces suffix : List (Nat × Nat)) (i : Nat)
    (hi : i < (headPieces.map Prod.fst).sum) :
    depth (headPieces ++ suffix) i = depth headPieces i := by
  induction headPieces generalizing i with
  | nil => simp at hi
  | cons p headPieces ih =>
    rcases p with ⟨a, z⟩
    simp only [List.cons_append, List.map_cons, List.sum_cons, depth]
    by_cases h : i < a
    · simp [h]
    · have htail : i - a < (headPieces.map Prod.fst).sum := by
        have hsum : i < a + (headPieces.map Prod.fst).sum := by simpa using hi
        omega
      simp only [if_neg h]
      exact ih (i - a) htail

/-- A local piece block evaluates a local wire exactly as the full layout does after
the preceding blocks. -/
theorem depth_local_block (before block after : List (Nat × Nat)) (i : Nat)
    (hi : i < (block.map Prod.fst).sum) :
    depth (before ++ block ++ after) ((before.map Prod.fst).sum + i) =
      depth block i := by
  rw [List.append_assoc, depth_append_skip]
  exact depth_append_within block after i hi

end ShiTMLayoutMachine
