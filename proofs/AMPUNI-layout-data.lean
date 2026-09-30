import «AMPUNI-layout-machine»

set_option autoImplicit false

namespace ShiTMLayoutMachine

def depth : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (a, z) :: ps, w => if w < a then z + w else depth ps (w - a)

def cost : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (a, z) :: ps, w =>
      if w < a then 2 * w + z + 3 else 2 * a + z + 3 + cost ps (w - a)

def pieceCells (f : Nat × Nat → Nat) : List (Nat × Nat) → List Cell
  | [] => []
  | p :: ps => List.replicate (f p) .mark ++ .delim :: pieceCells f ps

end ShiTMLayoutMachine
