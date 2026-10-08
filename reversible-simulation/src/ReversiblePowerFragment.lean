import ReversibleUnaryPower
import ReversibleCounterRelabel

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

/-- A twelve-instruction multiplication/transfer block with an explicit continuation. -/
def powerBlock (r q dst tmp : R) (s : Fin 12 → L) (next : L) (j : Fin 12) : CounterInstr R L :=
  match j.val with
  | 0 => .branch r (s 9) (s 1)
  | 1 => .dec r (s 2)
  | 2 => .branch q (s 6) (s 3)
  | 3 => .dec q (s 4)
  | 4 => .inc dst (s 5)
  | 5 => .inc tmp (s 2)
  | 6 => .branch tmp (s 0) (s 7)
  | 7 => .dec tmp (s 8)
  | 8 => .inc q (s 6)
  | 9 => .branch dst next (s 10)
  | 10 => .dec dst (s 11)
  | _ => .inc r (s 9)

@[simp] theorem multiplyState_transfer (base : CounterCfg R L) (r q dst tmp : R)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrt : r ≠ tmp) (hqd : q ≠ dst) (hqt : q ≠ tmp) (hdt : dst ≠ tmp)
    (k n m v u : Nat) (p pc : L) :
    transferState (multiplyState base r q dst tmp k n m p) dst r v u pc =
      multiplyState base r q dst tmp u n v pc := by
  apply CounterCfg.ext
  · rfl
  · funext j
    by_cases ht : j = tmp
    · subst j; simp [transferState, multiplyState, copyState, withCounter, Ne.symm hrt, Ne.symm hdt]
    · by_cases hr : j = r
      · subst j; simp [transferState, multiplyState, copyState, withCounter, hrd, hrq, hrt]
      · by_cases hd : j = dst
        · subst j; simp [transferState, multiplyState, copyState, withCounter, Ne.symm hrd, hdt]
        · by_cases hq : j = q
          · subst j; simp [transferState, multiplyState, copyState, withCounter, Ne.symm hrq, hqd, hqt]
          · simp [transferState, multiplyState, copyState, withCounter, ht, hr, hd, hq]
  · rfl

/-- The arithmetic block preserves every register outside its four explicit operands. -/
theorem power_block_run (code : L → CounterInstr R L) (r q dst tmp : R)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrt : r ≠ tmp) (hqd : q ≠ dst) (hqt : q ≠ tmp) (hdt : dst ≠ tmp)
    (s : Fin 12 → L) (next : L) (hc : ∀ j, code (s j) = powerBlock r q dst tmp s next j)
    (base : CounterCfg R L) (a n : Nat) :
    CounterRun code (multiplyState base r q dst tmp a n 0 (s 0)) (a * (10 * n + 4) + 2)
      (multiplyState base r q dst tmp (a * n) n 0 next) := by
  have hm := multiply_counter_run code r q dst tmp hrq hrd hrt hqd hqt hdt
    (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) (s 7) (s 8) (s 9)
    (hc 0) (hc 1) (hc 2) (hc 3) (hc 4) (hc 5) (hc 6) (hc 7) (hc 8) base a n 0
  simp only [Nat.zero_add] at hm
  have ht := transfer_counter_run code dst r (Ne.symm hrd) (s 9) (s 10) (s 11) next
    (hc 9) (hc 10) (hc 11) (multiplyState base r q dst tmp 0 n 0 (s 9)) (a * n) 0
  simp only [multiplyState_transfer base r q dst tmp hrq hrd hrt hqd hqt hdt, Nat.zero_add] at ht
  have h := CounterRun.trans code hm ht
  convert h using 1 <;> ring

/-- An arbitrary suffix of explicit arithmetic blocks, with no assumptions on the continuation code. -/
theorem power_fragment_span (code : L → CounterInstr R L) (r q dst tmp : R)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrt : r ≠ tmp) (hqd : q ≠ dst) (hqt : q ≠ tmp) (hdt : dst ≠ tmp)
    (d : Nat) (stage : Fin d → Fin 12 → L) (entry : Nat → L)
    (hf : ∀ i : Fin d, entry i.val = stage i 0)
    (hc : ∀ i j, code (stage i j) = powerBlock r q dst tmp (stage i) (entry (i.val + 1)) j)
    (base : CounterCfg R L) (k i a n : Nat) (hi : i + k ≤ d) :
    CounterRun code (multiplyState base r q dst tmp a n 0 (entry i)) (a * powerWork n k + 2 * k)
      (multiplyState base r q dst tmp (a * n ^ k) n 0 (entry (i + k))) := by
  induction k generalizing i a with
  | zero => simpa [powerWork] using CounterRun.refl (multiplyState base r q dst tmp a n 0 (entry i))
  | succ k ih =>
    have hil : i < d := by omega
    have hs := power_block_run code r q dst tmp hrq hrd hrt hqd hqt hdt
      (stage ⟨i, hil⟩) (entry (i + 1)) (hc ⟨i, hil⟩) base a n
    have hr := ih (i + 1) (a * n) (by omega)
    have h := CounterRun.trans code hs hr
    rw [hf ⟨i, hil⟩]
    have hid : i + (k + 1) = i + 1 + k := by omega
    rw [hid]
    convert h using 1 <;> simp [powerWork, pow_succ, multiplyState, copyState, withCounter] <;> ring

abbrev FragmentLabel (d : Nat) (L : Type) := (Fin d × Fin 12) ⊕ L

def fragmentFrom (d : Nat) (stop : L) (i : Nat) : FragmentLabel d L :=
  if h : i < d then .inl (⟨i, h⟩, 0) else .inr stop

def fragmentCode (code : L → CounterInstr R L) (d : Nat) (r q dst tmp : R) (stop : L) :
    FragmentLabel d L → CounterInstr R (FragmentLabel d L)
  | .inl (i, j) => powerBlock r q dst tmp (fun j => .inl (i, j)) (fragmentFrom d stop (i.val + 1)) j
  | .inr l => (code l).relabel Sum.inr

/-- A concrete finite control graph computes the power and returns to the caller's label.
The surrounding generator's other counters and current output are preserved. -/
theorem fragmentCode_run (code : L → CounterInstr R L) (d : Nat) (r q dst tmp : R) (stop : L)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrt : r ≠ tmp) (hqd : q ≠ dst) (hqt : q ≠ tmp) (hdt : dst ≠ tmp)
    (base : CounterCfg R (FragmentLabel d L)) (a n : Nat) :
    CounterRun (fragmentCode code d r q dst tmp stop)
      (multiplyState base r q dst tmp a n 0 (fragmentFrom d stop 0)) (a * powerWork n d + 2 * d)
      (multiplyState base r q dst tmp (a * n ^ d) n 0 (.inr stop)) := by
  have h := power_fragment_span (fragmentCode code d r q dst tmp stop) r q dst tmp
    hrq hrd hrt hqd hqt hdt d (fun i j => .inl (i, j)) (fragmentFrom d stop)
    (fun i => by simp [fragmentFrom, i.isLt]) (fun _ _ => rfl) base d 0 a n (by omega)
  simpa [fragmentFrom, Nat.lt_irrefl] using h

end ShiReversibleGenerator
