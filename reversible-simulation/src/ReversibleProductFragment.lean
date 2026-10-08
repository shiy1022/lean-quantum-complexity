import ReversibleCounterMultiply
import ReversibleCopyFragment

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

abbrev ProductLabel (L : Type) := Fin 9 ⊕ L

def productCode (caller : L → CounterInstr R L) (r q dst tmp : R) (stop : L) :
    ProductLabel L → CounterInstr R (ProductLabel L)
  | .inr l => (caller l).relabel Sum.inr
  | .inl j => match j.val with
    | 0 => .branch r (.inr stop) (.inl 1)
    | 1 => .dec r (.inl 2)
    | 2 => .branch q (.inl 6) (.inl 3)
    | 3 => .dec q (.inl 4)
    | 4 => .inc dst (.inl 5)
    | 5 => .inc tmp (.inl 2)
    | 6 => .branch tmp (.inl 0) (.inl 7)
    | 7 => .dec tmp (.inl 8)
    | _ => .inc q (.inl 6)

/-- A fixed nine-label multiplication graph with an explicit caller continuation. -/
theorem productCode_run (caller : L → CounterInstr R L) (r q dst tmp : R) (stop : L)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrt : r ≠ tmp)
    (hqd : q ≠ dst) (hqt : q ≠ tmp) (hdt : dst ≠ tmp)
    (base : CounterCfg R (ProductLabel L)) (k n m : Nat) :
    CounterRun (productCode caller r q dst tmp stop)
      (multiplyState base r q dst tmp k n m (.inl 0)) (k * (7 * n + 4) + 1)
      (multiplyState base r q dst tmp 0 n (m + k * n) (.inr stop)) :=
  multiply_counter_run _ r q dst tmp hrq hrd hrt hqd hqt hdt
    (.inl 0) (.inl 1) (.inl 2) (.inl 3) (.inl 4) (.inl 5) (.inl 6) (.inl 7) (.inl 8) (.inr stop)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl base k n m

/-- Counter values at the beginning and end of a nonconsuming product. -/
def productState (base : CounterCfg R L) (r q dst buf tmp : R)
    (k n m z : Nat) (pc : L) : CounterCfg R L :=
  multiplyState (withCounter base r k pc) buf q dst tmp z n m pc

abbrev PreservedProductLabel (L : Type) := CopyLabel 1 (ProductLabel L)

def preservedProductCode (caller : L → CounterInstr R L) (r q dst buf tmp : R) (stop : L) :
    PreservedProductLabel L → CounterInstr R (PreservedProductLabel L) :=
  copyFragmentCode (productCode caller buf q dst tmp stop) 1 r buf tmp (.inl 0)

@[simp] theorem productState_copy (base : CounterCfg R L) (r q dst buf tmp : R)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrb : r ≠ buf) (hrt : r ≠ tmp)
    (hqb : q ≠ buf) (hdb : dst ≠ buf) (k n m z v w : Nat) (pc next : L) :
    copyState (productState base r q dst buf tmp k n m z pc) r buf tmp v w 0 next =
      productState base r q dst buf tmp v n m w next := by
  apply CounterCfg.ext
  · rfl
  · funext j
    by_cases ht : j = tmp
    · subst j; simp [productState, copyState, multiplyState, withCounter]
    · by_cases hb : j = buf
      · subst j; simp [productState, copyState, multiplyState, withCounter, ht, Ne.symm hqb, Ne.symm hdb]
      · by_cases hd : j = dst
        · subst j; simp [productState, copyState, multiplyState, withCounter, hb, ht, hrb, hrd, Ne.symm hrd]
        · by_cases hq : j = q
          · subst j; simp [productState, copyState, multiplyState, withCounter, hb, hd, ht, hrq, Ne.symm hrq]
          · by_cases hr : j = r
            · subst j; simp [productState, copyState, multiplyState, withCounter, hrb, hrq, hrd, hrt]
            · simp [productState, copyState, multiplyState, withCounter, ht, hb, hd, hq, hr]
  · rfl

/-- Add k*n to the accumulator while preserving both factors and clearing copy scratch. -/
theorem preservedProductCode_run (caller : L → CounterInstr R L) (r q dst buf tmp : R) (stop : L)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrb : r ≠ buf) (hrt : r ≠ tmp)
    (hqd : q ≠ dst) (hqb : q ≠ buf) (hqt : q ≠ tmp)
    (hdb : dst ≠ buf) (hdt : dst ≠ tmp) (hbt : buf ≠ tmp)
    (base : CounterCfg R (PreservedProductLabel L)) (k n m : Nat) :
    CounterRun (preservedProductCode caller r q dst buf tmp stop)
      (productState base r q dst buf tmp k n m 0 (copyFrom 1 (.inl 0) 0))
      ((7 * k + 2) + (k * (7 * n + 4) + 1))
      (productState base r q dst buf tmp k n (m + k * n) 0 (.inr (.inr stop))) := by
  let inner := productCode caller buf q dst tmp stop
  let outer := preservedProductCode caller r q dst buf tmp stop
  have hc := copyFragmentCode_run inner 1 r buf tmp (.inl 0) hrb hrt hbt
    (productState base r q dst buf tmp k n m 0 (copyFrom 1 (.inl 0) 0)) k 0
  simp only [productState_copy base r q dst buf tmp hrq hrd hrb hrt hqb hdb,
    Nat.one_mul, Nat.zero_add] at hc
  let bi : CounterCfg R (ProductLabel L) := ⟨none, base.counters, base.output⟩
  have hm := productCode_run caller buf q dst tmp stop (Ne.symm hqb) (Ne.symm hdb) hbt
    hqd hqt hdt (withCounter bi r k (.inl 0)) k n m
  have hm' := CounterRun.relabel inner outer Sum.inr (fun _ => rfl) hm
  change CounterRun outer
    (productState base r q dst buf tmp k n m k (.inr (.inl 0)))
    (k * (7 * n + 4) + 1)
    (productState base r q dst buf tmp k n (m + k * n) 0 (.inr (.inr stop))) at hm'
  have h := CounterRun.trans outer hc hm'
  simpa only [outer, inner, preservedProductCode] using h


/-- Frame-normalized product state, suitable for composition with arbitrary counters. -/
theorem productState_from_counters (r q dst buf tmp : R)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrb : r ≠ buf) (hrt : r ≠ tmp)
    (hqd : q ≠ dst) (hqb : q ≠ buf) (hqt : q ≠ tmp)
    (hdb : dst ≠ buf) (hdt : dst ≠ tmp) (hbt : buf ≠ tmp)
    (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) (m : Nat) (pc : L) :
    productState ⟨none, cs, ys⟩ r q dst buf tmp (cs r) (cs q) m 0 pc =
      ⟨some pc, Function.update cs dst m, ys⟩ := by
  apply CounterCfg.ext
  · rfl
  · funext j
    by_cases hjt : j = tmp <;> by_cases hjb : j = buf <;> by_cases hjd : j = dst <;>
      by_cases hjq : j = q <;> by_cases hjr : j = r
    all_goals simp_all [productState, multiplyState, copyState, withCounter, ne_comm]
  · rfl

/-- Nonconsuming multiply/add over the caller's complete runtime register file. -/
theorem preservedProductCode_run_preserved (caller : L → CounterInstr R L)
    (r q dst buf tmp : R) (stop : L)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrb : r ≠ buf) (hrt : r ≠ tmp)
    (hqd : q ≠ dst) (hqb : q ≠ buf) (hqt : q ≠ tmp)
    (hdb : dst ≠ buf) (hdt : dst ≠ tmp) (hbt : buf ≠ tmp)
    (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) :
    CounterRun (preservedProductCode caller r q dst buf tmp stop)
      ⟨some (copyFrom 1 (.inl 0) 0), cs, ys⟩
      ((7 * cs r + 2) + (cs r * (7 * cs q + 4) + 1))
      ⟨some (.inr (.inr stop)), Function.update cs dst (cs dst + cs r * cs q), ys⟩ := by
  let base : CounterCfg R (PreservedProductLabel L) := ⟨none, cs, ys⟩
  have h := preservedProductCode_run caller r q dst buf tmp stop
    hrq hrd hrb hrt hqd hqb hqt hdb hdt hbt base (cs r) (cs q) (cs dst)
  simp only [base, productState_from_counters r q dst buf tmp hrq hrd hrb hrt hqd hqb hqt hdb hdt hbt cs hb ht] at h
  simpa using h

theorem preservedProductCode_clock_polynomial (left right : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      (7 * left.eval n + 2) + (left.eval n * (7 * right.eval n + 4) + 1) = p.eval n := by
  refine ⟨(Polynomial.C 7 * left + Polynomial.C 2) +
    (left * (Polynomial.C 7 * right + Polynomial.C 4) + Polynomial.C 1), ?_⟩
  intro n
  simp

end ShiReversibleGenerator
