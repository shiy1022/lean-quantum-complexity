import «AMPUNI-piece-controller-draft»

set_option autoImplicit false

namespace ShiTMPieceController

theorem commandAt_some_lt (commands : List ShiTMPieceSchedule.Command)
    (index : Nat) (command : ShiTMPieceSchedule.Command)
    (h : commandAt commands index = some command) :
    index < commands.length := by
  induction commands generalizing index with
  | nil => simp [commandAt] at h
  | cons head tail ih =>
      cases index with
      | zero => simp
      | succ index =>
          simp only [commandAt, List.length_cons] at h ⊢
          have htail := ih index h
          omega

theorem nextPC_no_wrap (pc : PC) (hpc : pc.val < 64) :
    (nextPC pc).val = pc.val + 1 := by
  simp only [nextPC]
  exact Nat.mod_eq_of_lt (by omega)

theorem active_command_no_wrap (copy : Fin 3) (pc : PC)
    (command : ShiTMPieceSchedule.Command)
    (hcommand : commandAt (ShiTMPieceSchedule.program copy) pc.val =
      some command) :
    (nextPC pc).val = pc.val + 1 := by
  have hpos := commandAt_some_lt _ _ _ hcommand
  have hlength := ShiTMPieceSchedule.program_length_le_64 copy
  exact nextPC_no_wrap pc (by omega)

end ShiTMPieceController
