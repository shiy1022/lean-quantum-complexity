import «AMPUNI-layout-machine»
import Theorems.Thm_ShiTM_encNat_parser_block
import Theorems.Thm_ShiTM_copy_loop_transfers_stack

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMLayoutMachine

def scanVar (n : Nat) (v : Sig) : Sig :=
  pop (List.foldl (fun w y => pop w (some y)) v
    (List.replicate n (bit true))) (some (bit false))

/-- CNOT's first operand is saved on stack 12 while the source advances to its second. -/
theorem scan_cnot_first
    (i : Nat) (rest : List Cell) (v : Sig) (S : ∀ k, List (Gam k))
    (hS : S 11 = (ShiBQP.encNat i).map bit ++ rest) :
    (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[i + 1]
        (some { l := some (b .readCnotFirst), var := v, stk := S }) =
      some ({
        l := some (b .readCnotSecond)
        var := scanVar i v
        stk := Function.update (Function.update S 11 rest) 12
          (List.replicate i .mark ++ S 12) } : Cfg Gam Label Sig) := by
  simpa only [scanVar] using
    (ShiTM.encNat_parser_block machine
      (ka := (11 : Fin 14)) (kb := (12 : Fin 14)) (by decide)
      (lc := b .readCnotFirst) (lnext := b .readCnotSecond)
      (fpop := pop) (gtest := isMark) (hpush := cst .mark)
      (e := fun _ => .mark) bit rfl
      (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
      i rest v S hS).1

/-- CNOT's second operand is materialized as the bare layout wire on stack 0. -/
theorem scan_cnot_second
    (j : Nat) (rest : List Cell) (v : Sig) (S : ∀ k, List (Gam k))
    (hS : S 11 = (ShiBQP.encNat j).map bit ++ rest) :
    (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[j + 1]
        (some { l := some (b .readCnotSecond), var := v, stk := S }) =
      some ({
        l := some (b .finishCnotMid)
        var := scanVar j v
        stk := Function.update (Function.update S 11 rest) 0
          (List.replicate j .mark ++ S 0) } : Cfg Gam Label Sig) := by
  simpa only [scanVar] using
    (ShiTM.encNat_parser_block machine
      (ka := (11 : Fin 14)) (kb := (0 : Fin 14)) (by decide)
      (lc := b .readCnotSecond) (lnext := b .finishCnotMid)
      (fpop := pop) (gtest := isMark) (hpush := cst .mark)
      (e := fun _ => .mark) bit rfl
      (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
      j rest v S hS).1

theorem finish_cnot_mid_to_wire (v : Sig) (S : ∀ k, List (Gam k)) :
    (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[1]
        (some { l := some (b .finishCnotMid), var := v, stk := S }) =
      some ({
        l := some (b .wire)
        var := v
        stk := Function.update S 7 (tagCell 0 :: .continueCnotMid :: S 7) } :
          Cfg Gam Label Sig) := by
  change some (stepAux (machine (b .finishCnotMid)) v S) = _
  rw [show machine (b .finishCnotMid) = finishOperand 0 .continueCnotMid from rfl]
  simp [finishOperand, stepAux, cst]

theorem done_to_cnot_strip (v : Sig) (S : ∀ k, List (Gam k)) (tail : List Cell)
    (hS7 : S 7 = .continueCnotMid :: tail) :
    (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[1]
        (some { l := some (b .done), var := v, stk := S }) =
      some ({
        l := some (b .stripCnotZero)
        var := pop v (some .continueCnotMid)
        stk := Function.update S 7 tail } : Cfg Gam Label Sig) := by
  change some (stepAux (machine (b .done)) v S) = _
  rw [show machine (b .done) = Stmt.pop 7 pop (Stmt.goto continuationLabel) from rfl]
  simp [stepAux, hS7, continuationLabel, pop]

theorem strip_cnot_zero (v : Sig) (S : ∀ k, List (Gam k)) (payload : List Cell)
    (hS6 : S 6 = .delim :: payload) :
    (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[1]
        (some { l := some (b .stripCnotZero), var := v, stk := S }) =
      some ({
        l := some (b .clearScratch)
        var := pop v (some .delim)
        stk := Function.update S 6 payload } : Cfg Gam Label Sig) := by
  change some (stepAux (machine (b .stripCnotZero)) v S) = _
  rw [show machine (b .stripCnotZero) =
    Stmt.pop 6 pop (Stmt.goto (fun _ => b .clearScratch)) from rfl]
  simp [stepAux, hS6, pop]

def clearedScratchStacks (garbage : List Cell)
    (S : ∀ k, List (Gam k)) : ∀ k, List (Gam k) :=
  Function.update (Function.update S 3 []) 5 (garbage.reverse ++ S 5)

theorem clear_layout_scratch
    (garbage : List Cell) (v : Sig) (S : ∀ k, List (Gam k)) (hS3 : S 3 = garbage) :
    (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[garbage.length + 1]
        (some { l := some (b .clearScratch), var := v, stk := S }) =
      some ({
        l := some (b .restoreCnotFirst)
        var := pop (garbage.foldl (fun w y => pop w (some y)) v) none
        stk := clearedScratchStacks garbage S } : Cfg Gam Label Sig) := by
  simpa [clearedScratchStacks] using
    (ShiTM.copy_loop_transfers_stack machine
      (ka := (3 : Fin 14)) (kb := (5 : Fin 14)) (by decide)
      (lc := b .clearScratch) (lnext := b .restoreCnotFirst)
      (fpop := pop) (gtest := isSome) (hpush := get) (e := id)
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) garbage v S hS3).1

def restoreVar (saved : List Cell) (v : Sig) : Sig :=
  pop (saved.foldl (fun w y => pop w (some y)) v) none

def restoredStacks (saved : List Cell) (S : ∀ k, List (Gam k)) : ∀ k, List (Gam k) :=
  Function.update (Function.update S 12 []) 0
    ((saved.map fun _ => .mark).reverse ++ S 0)

theorem restore_cnot_first
    (saved : List Cell) (v : Sig) (S : ∀ k, List (Gam k)) (hS12 : S 12 = saved) :
    (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[saved.length + 1]
        (some { l := some (b .restoreCnotFirst), var := v, stk := S }) =
      some ({
        l := some (b .finishCnotEnd)
        var := restoreVar saved v
        stk := restoredStacks saved S } : Cfg Gam Label Sig) := by
  simpa only [restoreVar, restoredStacks] using
    (ShiTM.copy_loop_transfers_stack machine
      (ka := (12 : Fin 14)) (kb := (0 : Fin 14)) (by decide)
      (lc := b .restoreCnotFirst) (lnext := b .finishCnotEnd)
      (fpop := pop) (gtest := isSome) (hpush := cst .mark) (e := fun _ => .mark)
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) saved v S hS12).1

theorem finish_cnot_end_to_wire (v : Sig) (S : ∀ k, List (Gam k)) :
    (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[1]
        (some { l := some (b .finishCnotEnd), var := v, stk := S }) =
      some ({
        l := some (b .wire)
        var := v
        stk := Function.update S 7 (tagCell 4 :: .continueCnotEnd :: S 7) } :
          Cfg Gam Label Sig) := by
  change some (stepAux (machine (b .finishCnotEnd)) v S) = _
  rw [show machine (b .finishCnotEnd) = finishOperand 4 .continueCnotEnd from rfl]
  simp [finishOperand, stepAux, cst]

end ShiTMLayoutMachine
