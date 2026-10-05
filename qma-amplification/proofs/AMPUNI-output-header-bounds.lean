import «AMPUNI-output-header-machine»
import «AMPUNI-output-header-cost-bound»

set_option autoImplicit false

namespace ShiTMOutputHeader

theorem commandAt_some_lt (commands : List Command)
    (index : Nat) (command : Command)
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

theorem nextPC_no_wrap (pc : PC) (hpc : pc.val < 31) :
    (nextPC pc).val = pc.val + 1 := by
  simp only [nextPC]
  exact Nat.mod_eq_of_lt (by omega)

theorem active_command_no_wrap (pc : PC) (command : Command)
    (hcommand : commandAt program pc.val = some command) :
    (nextPC pc).val = pc.val + 1 := by
  have hpos := commandAt_some_lt _ _ _ hcommand
  rw [program_length] at hpos
  exact nextPC_no_wrap pc (by omega)

theorem commandAt_eq_head_drop (commands : List Command) (index : Nat) :
    commandAt commands index = (commands.drop index).head? := by
  induction commands generalizing index with
  | nil => simp [commandAt]
  | cons c cs ih =>
      cases index with
      | zero => rfl
      | succ index => simpa [commandAt] using ih index

end ShiTMOutputHeader
