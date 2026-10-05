import Definitions.Def_ShiClassQMAAmpX

set_option autoImplicit false

namespace ShiQMAVariableRounds
open ShiShallow ShiClassQMA ShiClassQMAAmpX

noncomputable def iter (F : QMAFamily) : Nat → QMAFamily
  | 0 => F
  | r + 1 => ampFamilyX (iter F r)

/-- At each input length, choose a possibly different number of rounds. -/
noncomputable def varying (F : QMAFamily) (rounds : Nat → Nat) : QMAFamily where
  wit n := (iter F (rounds n)).wit n
  anc n := (iter F (rounds n)).anc n
  circ n := (iter F (rounds n)).circ n
  out n := (iter F (rounds n)).out n

end ShiQMAVariableRounds
