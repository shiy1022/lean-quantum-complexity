import «AMPUNI-piece-controller-command»

set_option autoImplicit false

namespace ShiTMPieceController

open ShiTMPieceSchedule

theorem commandAt_eq_head_drop (xs : List Command) (i : Nat) :
    commandAt xs i = (xs.drop i).head? := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons command xs ih =>
      cases i with
      | zero => rfl
      | succ i => simpa [commandAt] using ih i

theorem drop_succ_eq_tail (xs : List Command) (i : Nat) :
    xs.drop (i + 1) = (xs.drop i).tail := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons command xs ih =>
      cases i with
      | zero => rfl
      | succ i => simpa using ih i

theorem active_suffix (copy : Fin 3) (pc : PC)
    (command : Command) (rest : List Command)
    (hsuffix : (program copy).drop pc.val = command :: rest) :
    commandAt (program copy) pc.val = some command ∧
      (program copy).drop (nextPC pc).val = rest := by
  have hcommand : commandAt (program copy) pc.val = some command := by
    rw [commandAt_eq_head_drop, hsuffix]
    rfl
  refine ⟨hcommand, ?_⟩
  rw [active_command_no_wrap copy pc command hcommand,
    drop_succ_eq_tail, hsuffix]
  rfl

end ShiTMPieceController
