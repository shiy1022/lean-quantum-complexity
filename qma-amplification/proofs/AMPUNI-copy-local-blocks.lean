import «AMPUNI-local-copy-layout»
import «AMPUNI-concrete-copy-encoding»

set_option autoImplicit false

open ShiShallow ShiClassQMAAmp

namespace ShiTMLayoutMachine

def copyPieces0 (n wit anc : Nat) : List (Nat × Nat) :=
  [(n, 0), (wit, n), (anc, n + 3 * wit), (1, n + 3 * wit + anc)]

def copyPieces1 (n wit anc : Nat) : List (Nat × Nat) :=
  [(n, n + 3 * wit + anc + 1), (wit, n + wit),
   (anc, 2 * n + 3 * wit + anc + 1), (1, 2 * n + 3 * wit + 2 * anc + 1)]

def copyPieces2 (n wit anc : Nat) : List (Nat × Nat) :=
  [(n, 2 * n + 3 * wit + 2 * anc + 2), (wit, n + 2 * wit),
   (anc, 3 * n + 3 * wit + 2 * anc + 2), (1, 3 * n + 3 * wit + 3 * anc + 2)]

def copyTail (n wit anc : Nat) : List (Nat × Nat) :=
  [(1, 3 * n + 3 * wit + 3 * anc + 3)]

theorem ampPieces_split (n wit anc : Nat) :
    ShiTMRawLayout.ampPieces n wit anc =
      copyPieces0 n wit anc ++ copyPieces1 n wit anc ++
        copyPieces2 n wit anc ++ copyTail n wit anc := by
  rfl

theorem copyPieces0_width (n wit anc : Nat) :
    ((copyPieces0 n wit anc).map Prod.fst).sum = n + (wit + (anc + 1)) := by
  simp [copyPieces0]

theorem copyPieces1_width (n wit anc : Nat) :
    ((copyPieces1 n wit anc).map Prod.fst).sum = n + (wit + (anc + 1)) := by
  simp [copyPieces1]

theorem copyPieces2_width (n wit anc : Nat) :
    ((copyPieces2 n wit anc).map Prod.fst).sum = n + (wit + (anc + 1)) := by
  simp [copyPieces2]

theorem depth_copy0_global (n wit anc : Nat) (i : Nat)
    (hi : i < n + (wit + (anc + 1))) :
    depth (copyPieces0 n wit anc) i =
      depth (ShiTMRawLayout.ampPieces n wit anc) i := by
  rw [ampPieces_split]
  exact (depth_append_within (copyPieces0 n wit anc)
    (copyPieces1 n wit anc ++ copyPieces2 n wit anc ++ copyTail n wit anc)
    i (by simpa [copyPieces0_width] using hi)).symm

theorem depth_copy1_global (n wit anc : Nat) (i : Nat)
    (hi : i < n + (wit + (anc + 1))) :
    depth (copyPieces1 n wit anc) i =
      depth (ShiTMRawLayout.ampPieces n wit anc)
        (n + (wit + (anc + 1)) + i) := by
  rw [ampPieces_split]
  have h := depth_local_block (copyPieces0 n wit anc) (copyPieces1 n wit anc)
    (copyPieces2 n wit anc ++ copyTail n wit anc) i
    (by simpa [copyPieces1_width] using hi)
  simpa [copyPieces0_width, List.append_assoc] using h.symm

theorem depth_copy2_global (n wit anc : Nat) (i : Nat)
    (hi : i < n + (wit + (anc + 1))) :
    depth (copyPieces2 n wit anc) i =
      depth (ShiTMRawLayout.ampPieces n wit anc)
        (2 * (n + (wit + (anc + 1))) + i) := by
  rw [ampPieces_split]
  have h := depth_local_block
    (copyPieces0 n wit anc ++ copyPieces1 n wit anc)
    (copyPieces2 n wit anc) (copyTail n wit anc) i
    (by simpa [copyPieces2_width] using hi)
  simpa [copyPieces0_width, copyPieces1_width, List.map_append,
    List.sum_append, List.append_assoc, two_mul] using h.symm

end ShiTMLayoutMachine
