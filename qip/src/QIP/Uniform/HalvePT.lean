import QIP.Uniform.TransPT


/-!
# Q36 — the halving description is polynomial time

Every piece of `halveDesc d n` (layout, swaps, controlled forward and backward steps, the
zero test) is polynomial time in `(d, n)`.
-/

namespace ShiQIP.Uniform

open ShiQIP

variable {α : Type} [Rep α] {d : α → Desc} {n k j : α → ℕ}

@[fun_prop] theorem PT.fp_wd (hd : PT d) (hj : PT j) : PT fun x => wd (d x) (j x) := by
  unfold wd; fun_prop

@[fun_prop] theorem PT.fp_hw (hd : PT d) (hn : PT n) (hk : PT k) :
    PT fun x => hw (d x) (n x) (k x) := by unfold hw; fun_prop

@[fun_prop] theorem PT.fp_held0 (hd : PT d) : PT fun x => held0 (d x) := by
  unfold held0; fun_prop

@[fun_prop] theorem PT.fp_hAnc (hd : PT d) : PT fun x => hAnc (d x) := by
  unfold hAnc; fun_prop

@[fun_prop] theorem PT.fp_hPriv (hd : PT d) : PT fun x => hPriv (d x) := by
  unfold hPriv; fun_prop

@[fun_prop] theorem PT.fp_hMsgs (hd : PT d) (hn : PT n) : PT fun x => hMsgs (d x) (n x) := by
  unfold hMsgs; fun_prop

@[fun_prop] theorem PT.fp_hOff (hd : PT d) (hn : PT n) (hk : PT k) :
    PT fun x => hOff (d x) (n x) (k x) := by unfold hOff; fun_prop

@[fun_prop] theorem PT.fp_hPay (hd : PT d) (hn : PT n) (hk : PT k) :
    PT fun x => hPay (d x) (n x) (k x) := by unfold hPay; fun_prop

@[fun_prop] theorem PT.fp_swapMsg (hd : PT d) (hn : PT n) (hk : PT k) (hj : PT j) :
    PT fun x => swapMsg (d x) (n x) (k x) (j x) := by unfold swapMsg; fun_prop

@[fun_prop] theorem PT.fp_onF {gs : α → List Gate} (hd : PT d) (hgs : PT gs) :
    PT fun x => onF (d x) (gs x) := by unfold onF hCoin hCa; fun_prop

@[fun_prop] theorem PT.fp_onB {gs : α → List Gate} (hd : PT d) (hgs : PT gs) :
    PT fun x => onB (d x) (gs x) := by unfold onB hCoin hCa; fun_prop

@[fun_prop] theorem PT.fp_fwdStep (hd : PT d) (hn : PT n) (hk : PT k) :
    PT fun x => fwdStep (d x) (n x) (k x) := by unfold fwdStep; fun_prop

@[fun_prop] theorem PT.fp_bwdStep (hd : PT d) (hn : PT n) (hk : PT k) :
    PT fun x => bwdStep (d x) (n x) (k x) := by unfold bwdStep; fun_prop

@[fun_prop] theorem PT.fp_hBlock (hd : PT d) (hn : PT n) (hk : PT k) :
    PT fun x => hBlock (d x) (n x) (k x) := by unfold hBlock hCoin hOut; fun_prop

@[fun_prop] theorem PT.fp_halveDesc (hd : PT d) (hn : PT n) :
    PT fun x => halveDesc (d x) (n x) := by unfold halveDesc hOut; fun_prop

end ShiQIP.Uniform
