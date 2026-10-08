import ReversibleCounterCopy
import ReversibleCounterRelabel

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

def copyBlock (r dst tmp : R) (s : Fin 7 → L) (next : L) (j : Fin 7) : CounterInstr R L :=
  match j.val with
  | 0 => .branch r (s 4) (s 1)
  | 1 => .dec r (s 2)
  | 2 => .inc dst (s 3)
  | 3 => .inc tmp (s 0)
  | 4 => .branch tmp next (s 5)
  | 5 => .dec tmp (s 6)
  | _ => .inc r (s 4)

theorem copy_block_run (code : L → CounterInstr R L) (r dst tmp : R)
    (hrd : r ≠ dst) (hrt : r ≠ tmp) (hdt : dst ≠ tmp)
    (s : Fin 7 → L) (next : L) (hc : ∀ j, code (s j) = copyBlock r dst tmp s next j)
    (base : CounterCfg R L) (n m : Nat) :
    CounterRun code (copyState base r dst tmp n m 0 (s 0)) (7 * n + 2)
      (copyState base r dst tmp n (m + n) 0 next) :=
  copy_counter_run code r dst tmp hrd hrt hdt (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) next
    (hc 0) (hc 1) (hc 2) (hc 3) (hc 4) (hc 5) (hc 6) base n m

theorem copy_fragment_span (code : L → CounterInstr R L) (r dst tmp : R)
    (hrd : r ≠ dst) (hrt : r ≠ tmp) (hdt : dst ≠ tmp)
    (b : Nat) (stage : Fin b → Fin 7 → L) (entry : Nat → L)
    (hf : ∀ i : Fin b, entry i.val = stage i 0)
    (hc : ∀ i j, code (stage i j) = copyBlock r dst tmp (stage i) (entry (i.val + 1)) j)
    (base : CounterCfg R L) (k i n m : Nat) (hi : i + k ≤ b) :
    CounterRun code (copyState base r dst tmp n m 0 (entry i)) (k * (7 * n + 2))
      (copyState base r dst tmp n (m + k * n) 0 (entry (i + k))) := by
  induction k generalizing i m with
  | zero => simpa using CounterRun.refl (copyState base r dst tmp n m 0 (entry i))
  | succ k ih =>
    have hil : i < b := by omega
    have hs := copy_block_run code r dst tmp hrd hrt hdt
      (stage ⟨i, hil⟩) (entry (i + 1)) (hc ⟨i, hil⟩) base n m
    have hr := ih (i + 1) (m + n) (by omega)
    have h := CounterRun.trans code hs hr
    rw [hf ⟨i, hil⟩]
    have hid : i + (k + 1) = i + 1 + k := by omega
    rw [hid]
    convert h using 1 <;> simp [copyState, Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> ring

abbrev CopyLabel (b : Nat) (L : Type) := (Fin b × Fin 7) ⊕ L

def copyFrom (b : Nat) (stop : L) (i : Nat) : CopyLabel b L :=
  if h : i < b then .inl (⟨i, h⟩, 0) else .inr stop

def copyFragmentCode (code : L → CounterInstr R L) (b : Nat) (r dst tmp : R) (stop : L) :
    CopyLabel b L → CounterInstr R (CopyLabel b L)
  | .inl (i, j) => copyBlock r dst tmp (fun j => .inl (i, j)) (copyFrom b stop (i.val + 1)) j
  | .inr l => (code l).relabel Sum.inr

theorem copyFragmentCode_run (code : L → CounterInstr R L) (b : Nat) (r dst tmp : R) (stop : L)
    (hrd : r ≠ dst) (hrt : r ≠ tmp) (hdt : dst ≠ tmp)
    (base : CounterCfg R (CopyLabel b L)) (n m : Nat) :
    CounterRun (copyFragmentCode code b r dst tmp stop)
      (copyState base r dst tmp n m 0 (copyFrom b stop 0)) (b * (7 * n + 2))
      (copyState base r dst tmp n (m + b * n) 0 (.inr stop)) := by
  have h := copy_fragment_span (copyFragmentCode code b r dst tmp stop) r dst tmp hrd hrt hdt
    b (fun i j => .inl (i, j)) (copyFrom b stop)
    (fun i => by simp [copyFrom, i.isLt]) (fun _ _ => rfl) base b 0 n m (by omega)
  simpa [copyFrom, Nat.lt_irrefl] using h

end ShiReversibleGenerator
