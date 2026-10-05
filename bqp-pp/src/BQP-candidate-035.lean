import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.Ring
import Theorems.Thm_ShiBQP_digit_by_digit_integer_square_root_and_bit_serial_subtractor
import Theorems.Thm_ShiTM_initList_haltList_laws
import Theorems.Thm_ShiTM_integer_square_root_machine_for_the_router_thresholds
import Theorems.Thm_ShiTM_outputsInTime_of_run_to_halt

namespace BQPReferenceValidation.Source35
/-
SQRTMACHINE.  THE INTEGER-SQUARE-ROOT MACHINE FOR THE ROUTER, AS A CONCRETE `FinTM2`.

WHAT IS MISSING AND WHY.  `RF-BUILDc`'s threshold ladder is built from
`S = Nat.sqrt (2 * 4 ^ (h + 3)) = ⌊2 ^ (h + 3) * √2⌋`, and `ROUTER-1b` expands that `S` to
`h + 7` bits and compares against it -- but takes `S` as GIVEN.  Nothing computes it on a
machine.  Repeated subtraction of odd numbers needs `S ≈ 2 ^ (h + 3)` steps, which is
exponential in `h` and fatal for the poly-time claim.

THE MACHINE.  Seven `Bool` stacks (`kin`, the output port `kS`, the remainder `kR`, three
sweep holds `kSh` / `kD` / `kRh`, and an iteration counter `kC`), THIRTEEN nullary labels,
register `Bool × Option Bool × Option Bool` -- a borrow flag and two symbol slots, so a
single `Stmt` can pop two stacks and push three IN ONE STEP.  Both slots are reloaded to
`none` on every exit arm, so the register between steps is always `(borrow, none, none)` and
the final `var = tm.initialState` obligation costs no reset block.

ALGORITHM: digit-by-digit (restoring) square root, in fixed width `h + 7`.  `sq` and `rm`
start at `1` and each iteration performs ONE left-to-right borrow-subtract sweep of `sq` from
`rm`; the sweep's borrow-OUT is simultaneously the verdict of the test `sq < rm` and its digit
stream is the difference, so the compare and the subtract are the SAME pass.  A second pass
writes back, discarding the top bit of `sq` and the top two of `rm` and pushing the new low
bits -- `push` IS the shift.  `h + 3` iterations of `2 * (h + 7) + 4` steps each: the whole
run is EXACTLY `2 * h * h + 27 * h + 66` steps, POLYNOMIAL in `h`.

REJECT PATH (gotcha 223).  Every input is scanned first; anything that is not
`1 ^ h ++ [0]` -- no terminator, or junk after it -- drains both live stacks and halts with
EMPTY output inside `2 * |w| + 4` steps.  The machine is total.

`Nat.sqrt` IS NEVER REWRITTEN UNDER: the identification of the recurrence with `Nat.sqrt` is
imported from `digit_by_digit_integer_square_root_and_bit_serial_subtractor`, which makes it
once through `Nat.le_sqrt` / `Nat.sqrt_lt` on a bracketing pair.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Turing.TM2

/-! ### 1.  The arithmetic layer, imported and specialised -/

private def bvalC : List Bool → ℕ
  | [] => 0
  | b :: t => (bif b then 1 else 0) + 2 * bvalC t

private def bitsC : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n => (n % 2 == 1) :: bitsC k (n / 2)

private def sbdC : Bool → List Bool → List Bool → List Bool
  | _, [], _ => []
  | _, _ :: _, [] => []
  | c, x :: r, y :: s => (xor x (xor y c)) :: sbdC (bif x then y && c else y || c) r s

private def sboC : Bool → List Bool → List Bool → Bool
  | c, [], _ => c
  | c, _ :: _, [] => c
  | c, x :: r, y :: s => sboC (bif x then y && c else y || c) r s

private def sqrmC : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 =>
      (2 * (sqrmC k).1 + (if (sqrmC k).1 < (sqrmC k).2 then 1 else 0),
        if (sqrmC k).1 < (sqrmC k).2 then 4 * ((sqrmC k).2 - (sqrmC k).1 - 1) + 3
        else 4 * (sqrmC k).2)

private def sqf (k : ℕ) : ℕ := (sqrmC k).1

private def rmf (k : ℕ) : ℕ := (sqrmC k).2

private lemma arith :
    (∀ k n : ℕ, (bitsC k n).length = k)
  ∧ (∀ k n : ℕ, n < 2 ^ k → bvalC (bitsC k n) = n)
  ∧ (∀ l : List Bool, bvalC l < 2 ^ l.length)
  ∧ (∀ (l : List Bool) (k : ℕ), l.length = k → bitsC k (bvalC l) = l)
  ∧ (∀ k n : ℕ, ∃ b : Bool, bitsC (k + 1) n = bitsC k n ++ [b])
  ∧ (∀ (b : Bool) (k v : ℕ),
        b :: bitsC k v = bitsC (k + 1) (2 * v + (bif b then 1 else 0)))
  ∧ (∀ (c : Bool) (r s : List Bool),
        r.length = s.length → (sbdC c r s).length = r.length)
  ∧ (∀ W S R : ℕ, S < 2 ^ W → R < 2 ^ W → S < R →
        sboC true (bitsC W R) (bitsC W S) = false
      ∧ sbdC true (bitsC W R) (bitsC W S) = bitsC W (R - S - 1))
  ∧ (∀ W S R : ℕ, S < 2 ^ W → R < 2 ^ W → R ≤ S →
        sboC true (bitsC W R) (bitsC W S) = true) := by
  obtain ⟨-, hII, -, -, -⟩ :=
    ShiBQP.digit_by_digit_integer_square_root_and_bit_serial_subtractor
  exact hII bvalC bitsC sbdC sboC rfl (fun b t => rfl) (fun n => rfl) (fun k n => rfl)
    (fun c s => rfl) (fun c x r => rfl) (fun c x y r s => rfl)
    (fun c s => rfl) (fun c x r => rfl) (fun c x y r s => rfl)

private lemma recC : ∀ k : ℕ, sqf k * sqf k + rmf k = 2 * 4 ^ k
    ∧ rmf k ≤ 2 * sqf k ∧ Nat.sqrt (2 * 4 ^ k) = sqf k ∧ sqf k < 2 ^ (k + 1) :=
  (ShiBQP.digit_by_digit_integer_square_root_and_bit_serial_subtractor).1
    sqf rmf rfl rfl (fun k => rfl) (fun k => rfl)

private lemma bitsLen : ∀ k n : ℕ, (bitsC k n).length = k := arith.1

private lemma bitsSnocL : ∀ k n : ℕ, ∃ b : Bool, bitsC (k + 1) n = bitsC k n ++ [b] :=
  arith.2.2.2.2.1

private lemma bitsConsL : ∀ (b : Bool) (k v : ℕ),
    b :: bitsC k v = bitsC (k + 1) (2 * v + (bif b then 1 else 0)) := arith.2.2.2.2.2.1

private lemma sbdLen : ∀ (c : Bool) (r s : List Bool),
    r.length = s.length → (sbdC c r s).length = r.length := arith.2.2.2.2.2.2.1

private lemma dec1 : ∀ W S R : ℕ, S < 2 ^ W → R < 2 ^ W → S < R →
    sboC true (bitsC W R) (bitsC W S) = false
  ∧ sbdC true (bitsC W R) (bitsC W S) = bitsC W (R - S - 1) := arith.2.2.2.2.2.2.2.1

private lemma dec2 : ∀ W S R : ℕ, S < 2 ^ W → R < 2 ^ W → R ≤ S →
    sboC true (bitsC W R) (bitsC W S) = true := arith.2.2.2.2.2.2.2.2

private lemma bitsZero : ∀ k : ℕ, bitsC k 0 = List.replicate k false := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      show false :: bitsC k 0 = false :: List.replicate k false
      rw [ih]

private lemma bitsOne : ∀ n : ℕ, bitsC (n + 7) 1
    = true :: false :: false :: false :: false :: false :: false
      :: List.replicate n false := by
  intro n
  have e1 : bitsC (n + 7) 1 = true :: bitsC (n + 6) 0 := rfl
  have e2 : bitsC (n + 6) 0 = List.replicate (n + 6) false := bitsZero (n + 6)
  have e3 : (List.replicate (n + 6) false : List Bool)
      = false :: false :: false :: false :: false :: false :: List.replicate n false := rfl
  rw [e1, e2, e3]

private lemma twoPowPos : ∀ n : ℕ, 0 < (2 : ℕ) ^ n := by
  intro n
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
      rw [pow_succ]
      omega

private lemma powMono : ∀ a b : ℕ, a ≤ b → (2 : ℕ) ^ a ≤ 2 ^ b := by
  intro a b hab
  obtain ⟨c, hc⟩ : ∃ c : ℕ, b = a + c := ⟨b - a, by omega⟩
  rw [hc, pow_add]
  have h3 : (1 : ℕ) ≤ 2 ^ c := twoPowPos c
  have h4 : (2 : ℕ) ^ a * 1 ≤ 2 ^ a * 2 ^ c := Nat.mul_le_mul (Nat.le_refl _) h3
  rw [Nat.mul_one] at h4
  exact h4

private lemma repSnoc : ∀ (x : Bool) (n : ℕ) (acc : List Bool),
    List.replicate n x ++ (x :: acc) = List.replicate (n + 1) x ++ acc := by
  intro x n
  induction n with
  | zero => intro acc; rfl
  | succ n ih =>
      intro acc
      show x :: (List.replicate n x ++ (x :: acc)) = x :: (List.replicate (n + 1) x ++ acc)
      rw [ih]

private lemma snocSplit : ∀ (l : List Bool) (n : ℕ), l.length = n + 1 →
    ∃ (t : List Bool) (a : Bool), l = t ++ [a] ∧ t.length = n := by
  intro l
  induction l with
  | nil =>
      intro n hn
      exfalso
      rw [List.length_nil] at hn
      omega
  | cons x t ih =>
      intro n hn
      cases n with
      | zero =>
          cases t with
          | nil => exact ⟨[], x, rfl, rfl⟩
          | cons y t2 =>
              exfalso
              rw [List.length_cons, List.length_cons] at hn
              omega
      | succ n =>
          have hl : t.length = n + 1 := by
            rw [List.length_cons] at hn
            omega
          obtain ⟨t0, a, h1, h2⟩ := ih n hl
          refine ⟨x :: t0, a, ?_, ?_⟩
          · rw [h1]
            rfl
          · rw [List.length_cons, h2]

private lemma classify : ∀ w : List Bool,
    (∃ (p : ℕ) (rest : List Bool), w = List.replicate p true ++ false :: rest)
  ∨ (∃ n : ℕ, w = List.replicate n true) := by
  intro w
  induction w with
  | nil => exact Or.inr ⟨0, rfl⟩
  | cons x t ih =>
      cases x
      · exact Or.inl ⟨0, t, rfl⟩
      · rcases ih with ⟨p, rest, h⟩ | ⟨n, h⟩
        · refine Or.inl ⟨p + 1, rest, ?_⟩
          show true :: t = true :: (List.replicate p true ++ false :: rest)
          rw [h]
        · refine Or.inr ⟨n + 1, ?_⟩
          show true :: t = true :: List.replicate n true
          rw [h]

/-! ### 2.  The machine -/

private inductive Stk : Type
  | kin | kS | kR | kSh | kD | kRh | kC
  deriving DecidableEq

private instance : Fintype Stk where
  elems := ⟨[Stk.kin, Stk.kS, Stk.kR, Stk.kSh, Stk.kD, Stk.kRh, Stk.kC], by decide⟩
  complete := fun x => by cases x <;> decide

private inductive Lbl : Type
  | lV0 | lV1 | lRJ | lRH | lBD | lIT | lP1 | lPA | lPB | lPC | lPE | lDR | lH
  deriving DecidableEq

private instance : Fintype Lbl where
  elems := ⟨[Lbl.lV0, Lbl.lV1, Lbl.lRJ, Lbl.lRH, Lbl.lBD, Lbl.lIT, Lbl.lP1, Lbl.lPA,
    Lbl.lPB, Lbl.lPC, Lbl.lPE, Lbl.lDR, Lbl.lH], by decide⟩
  complete := fun x => by cases x <;> decide

@[reducible] private def Gam : Stk → Type := fun _ => Bool

private abbrev Sg : Type := Bool × Option Bool × Option Bool

private abbrev rg (b : Bool) : Sg := (b, Option.none, Option.none)

private abbrev clr : Sg → Sg := fun v => (v.1, Option.none, Option.none)

private def Mw : Lbl → Stmt Gam Lbl Sg
  | Lbl.lV0 =>
      Stmt.pop Stk.kin (fun v o => (v.1, o, v.2.2))
        (Stmt.branch (fun v => v.2.1.isSome)
          (Stmt.branch (fun v => v.2.1.getD false)
            (Stmt.push Stk.kD (fun _ => true)
              (Stmt.load clr (Stmt.goto (fun _ => Lbl.lV0))))
            (Stmt.load clr (Stmt.goto (fun _ => Lbl.lV1))))
          (Stmt.load clr (Stmt.goto (fun _ => Lbl.lRH))))
  | Lbl.lV1 =>
      Stmt.pop Stk.kin (fun v o => (v.1, o, v.2.2))
        (Stmt.branch (fun v => v.2.1.isSome)
          (Stmt.load clr (Stmt.goto (fun _ => Lbl.lRJ)))
          (Stmt.load clr (Stmt.goto (fun _ => Lbl.lBD))))
  | Lbl.lRJ =>
      Stmt.pop Stk.kin (fun v o => (v.1, o, v.2.2))
        (Stmt.branch (fun v => v.2.1.isSome)
          (Stmt.load clr (Stmt.goto (fun _ => Lbl.lRJ)))
          (Stmt.load clr (Stmt.goto (fun _ => Lbl.lRH))))
  | Lbl.lRH =>
      Stmt.pop Stk.kD (fun v o => (v.1, o, v.2.2))
        (Stmt.branch (fun v => v.2.1.isSome)
          (Stmt.load clr (Stmt.goto (fun _ => Lbl.lRH)))
          (Stmt.load (fun _ => rg false) (Stmt.goto (fun _ => Lbl.lH))))
  | Lbl.lBD =>
      Stmt.pop Stk.kD (fun v o => (v.1, o, v.2.2))
        (Stmt.branch (fun v => v.2.1.isSome)
          (Stmt.push Stk.kS (fun _ => false)
            (Stmt.push Stk.kR (fun _ => false)
              (Stmt.push Stk.kC (fun _ => true)
                (Stmt.load clr (Stmt.goto (fun _ => Lbl.lBD))))))
          (Stmt.push Stk.kS (fun _ => false) (Stmt.push Stk.kS (fun _ => false)
            (Stmt.push Stk.kS (fun _ => false) (Stmt.push Stk.kS (fun _ => false)
            (Stmt.push Stk.kS (fun _ => false) (Stmt.push Stk.kS (fun _ => false)
            (Stmt.push Stk.kS (fun _ => true)
            (Stmt.push Stk.kR (fun _ => false) (Stmt.push Stk.kR (fun _ => false)
            (Stmt.push Stk.kR (fun _ => false) (Stmt.push Stk.kR (fun _ => false)
            (Stmt.push Stk.kR (fun _ => false) (Stmt.push Stk.kR (fun _ => false)
            (Stmt.push Stk.kR (fun _ => true)
            (Stmt.push Stk.kC (fun _ => true) (Stmt.push Stk.kC (fun _ => true)
            (Stmt.push Stk.kC (fun _ => true)
              (Stmt.load clr (Stmt.goto (fun _ => Lbl.lIT))))))))))))))))))))
            )
  | Lbl.lIT =>
      Stmt.pop Stk.kC (fun v o => (v.1, o, v.2.2))
        (Stmt.branch (fun v => v.2.1.isSome)
          (Stmt.load (fun _ => rg true) (Stmt.goto (fun _ => Lbl.lP1)))
          (Stmt.load (fun _ => rg false) (Stmt.goto (fun _ => Lbl.lDR))))
  | Lbl.lP1 =>
      Stmt.pop Stk.kR (fun v o => (v.1, o, v.2.2))
        (Stmt.branch (fun v => v.2.1.isSome)
          (Stmt.pop Stk.kS (fun v o => (v.1, v.2.1, o))
            (Stmt.push Stk.kRh (fun v => v.2.1.getD false)
              (Stmt.push Stk.kSh (fun v => v.2.2.getD false)
                (Stmt.push Stk.kD
                  (fun v => xor (v.2.1.getD false) (xor (v.2.2.getD false) v.1))
                  (Stmt.load (fun v =>
                      rg (bif (v.2.1.getD false)
                        then ((v.2.2.getD false) && v.1)
                        else ((v.2.2.getD false) || v.1)))
                    (Stmt.goto (fun _ => Lbl.lP1)))))))
          (Stmt.load clr (Stmt.goto (fun _ => Lbl.lPA))))
  | Lbl.lPA =>
      Stmt.pop Stk.kSh (fun v _ => v)
        (Stmt.pop Stk.kD (fun v _ => v)
          (Stmt.pop Stk.kRh (fun v _ => v) (Stmt.goto (fun _ => Lbl.lPB))))
  | Lbl.lPB =>
      Stmt.pop Stk.kSh (fun v o => (v.1, o, v.2.2))
        (Stmt.push Stk.kS (fun v => v.2.1.getD false)
          (Stmt.pop Stk.kD (fun v _ => v)
            (Stmt.pop Stk.kRh (fun v _ => v)
              (Stmt.load clr (Stmt.goto (fun _ => Lbl.lPC))))))
  | Lbl.lPC =>
      Stmt.pop Stk.kSh (fun v o => (v.1, o, v.2.2))
        (Stmt.branch (fun v => v.2.1.isSome)
          (Stmt.push Stk.kS (fun v => v.2.1.getD false)
            (Stmt.pop Stk.kD (fun v o => (v.1, v.2.1, o))
              (Stmt.pop Stk.kRh (fun v o => (v.1, o, v.2.2))
                (Stmt.push Stk.kR
                  (fun v => bif v.1 then (v.2.1.getD false) else (v.2.2.getD false))
                  (Stmt.load clr (Stmt.goto (fun _ => Lbl.lPC)))))))
          (Stmt.load clr (Stmt.goto (fun _ => Lbl.lPE))))
  | Lbl.lPE =>
      Stmt.push Stk.kS (fun v => !v.1)
        (Stmt.push Stk.kR (fun v => !v.1)
          (Stmt.push Stk.kR (fun v => !v.1)
            (Stmt.load (fun _ => rg false) (Stmt.goto (fun _ => Lbl.lIT)))))
  | Lbl.lDR =>
      Stmt.pop Stk.kR (fun v o => (v.1, o, v.2.2))
        (Stmt.branch (fun v => v.2.1.isSome)
          (Stmt.load clr (Stmt.goto (fun _ => Lbl.lDR)))
          (Stmt.load (fun _ => rg false) (Stmt.goto (fun _ => Lbl.lH))))
  | Lbl.lH => Stmt.halt

private abbrev tmW : Turing.FinTM2 :=
  { K := Stk, k₀ := Stk.kin, k₁ := Stk.kS, Γ := Gam, Λ := Lbl, main := Lbl.lV0,
    σ := Sg, initialState := rg false, m := Mw }

private def mk (a b c d e f g : List Bool) : ∀ k : Stk, List (Gam k)
  | Stk.kin => a
  | Stk.kS => b
  | Stk.kR => c
  | Stk.kSh => d
  | Stk.kD => e
  | Stk.kRh => f
  | Stk.kC => g

private abbrev stepW : Option (Cfg Gam Lbl Sg) → Option (Cfg Gam Lbl Sg) :=
  fun cc => cc.bind (step Mw)

/-! ### 3.  Stack-update normalisation -/

private lemma uIn (a b c d e f g x : List Bool) :
    Function.update (mk a b c d e f g) Stk.kin x = mk x b c d e f g := by
  funext k
  cases k
  · exact Function.update_self _ _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _

private lemma uS (a b c d e f g x : List Bool) :
    Function.update (mk a b c d e f g) Stk.kS x = mk a x c d e f g := by
  funext k
  cases k
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_self _ _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _

private lemma uR (a b c d e f g x : List Bool) :
    Function.update (mk a b c d e f g) Stk.kR x = mk a b x d e f g := by
  funext k
  cases k
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_self _ _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _

private lemma uSh (a b c d e f g x : List Bool) :
    Function.update (mk a b c d e f g) Stk.kSh x = mk a b c x e f g := by
  funext k
  cases k
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_self _ _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _

private lemma uD (a b c d e f g x : List Bool) :
    Function.update (mk a b c d e f g) Stk.kD x = mk a b c d x f g := by
  funext k
  cases k
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_self _ _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _

private lemma uRh (a b c d e f g x : List Bool) :
    Function.update (mk a b c d e f g) Stk.kRh x = mk a b c d e x g := by
  funext k
  cases k
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_self _ _ _
  · exact Function.update_of_ne (by decide) _ _

private lemma uC (a b c d e f g x : List Bool) :
    Function.update (mk a b c d e f g) Stk.kC x = mk a b c d e f x := by
  funext k
  cases k
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_of_ne (by decide) _ _
  · exact Function.update_self _ _ _

/-! ### 4.  Run composition -/

private lemma chainN' {x y z : Option (Cfg Gam Lbl Sg)} {m n t : ℕ} (ht : t = m + n)
    (h1 : stepW^[m] x = y) (h2 : stepW^[n] y = z) : stepW^[t] x = z := by
  subst ht
  rw [Nat.add_comm m n, Function.iterate_add_apply, h1]
  exact h2

private lemma chain1' {c c2 : Cfg Gam Lbl Sg} {y : Option (Cfg Gam Lbl Sg)} {n t : ℕ}
    (ht : t = n + 1) (h1 : step Mw c = Option.some c2)
    (h2 : stepW^[n] (Option.some c2) = y) : stepW^[t] (Option.some c) = y := by
  subst ht
  rw [Function.iterate_succ_apply]
  show stepW^[n] (step Mw c) = y
  rw [h1]
  exact h2

/-! ### 5.  The single steps -/

private lemma stV0T (β : Bool) (t b c d e f g : List Bool) :
    step Mw (⟨Option.some Lbl.lV0, rg β, mk (true :: t) b c d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lV0, rg β, mk t b c d (true :: e) f g⟩
          : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lV0, rg β, mk (true :: t) b c d e f g⟩
        : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lV0, rg β,
          Function.update (Function.update (mk (true :: t) b c d e f g) Stk.kin t)
            Stk.kD (true :: e)⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lV0) (rg β) (mk (true :: t) b c d e f g)) = _
    rfl
  rw [h, uIn, uD]

private lemma stV0F (β : Bool) (t b c d e f g : List Bool) :
    step Mw (⟨Option.some Lbl.lV0, rg β, mk (false :: t) b c d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lV1, rg β, mk t b c d e f g⟩ : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lV0, rg β, mk (false :: t) b c d e f g⟩
        : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lV1, rg β,
          Function.update (mk (false :: t) b c d e f g) Stk.kin t⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lV0) (rg β) (mk (false :: t) b c d e f g)) = _
    rfl
  rw [h, uIn]

private lemma stV0N (β : Bool) (b c d e f g : List Bool) :
    step Mw (⟨Option.some Lbl.lV0, rg β, mk [] b c d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lRH, rg β, mk [] b c d e f g⟩ : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lV0, rg β, mk [] b c d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lRH, rg β,
          Function.update (mk [] b c d e f g) Stk.kin []⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lV0) (rg β) (mk [] b c d e f g)) = _
    rfl
  rw [h, uIn]

private lemma stV1S (β x : Bool) (t b c d e f g : List Bool) :
    step Mw (⟨Option.some Lbl.lV1, rg β, mk (x :: t) b c d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lRJ, rg β, mk t b c d e f g⟩ : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lV1, rg β, mk (x :: t) b c d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lRJ, rg β,
          Function.update (mk (x :: t) b c d e f g) Stk.kin t⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lV1) (rg β) (mk (x :: t) b c d e f g)) = _
    rfl
  rw [h, uIn]

private lemma stV1N (β : Bool) (b c d e f g : List Bool) :
    step Mw (⟨Option.some Lbl.lV1, rg β, mk [] b c d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lBD, rg β, mk [] b c d e f g⟩ : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lV1, rg β, mk [] b c d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lBD, rg β,
          Function.update (mk [] b c d e f g) Stk.kin []⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lV1) (rg β) (mk [] b c d e f g)) = _
    rfl
  rw [h, uIn]

private lemma stRJS (β x : Bool) (t b c d e f g : List Bool) :
    step Mw (⟨Option.some Lbl.lRJ, rg β, mk (x :: t) b c d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lRJ, rg β, mk t b c d e f g⟩ : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lRJ, rg β, mk (x :: t) b c d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lRJ, rg β,
          Function.update (mk (x :: t) b c d e f g) Stk.kin t⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lRJ) (rg β) (mk (x :: t) b c d e f g)) = _
    rfl
  rw [h, uIn]

private lemma stRJN (β : Bool) (b c d e f g : List Bool) :
    step Mw (⟨Option.some Lbl.lRJ, rg β, mk [] b c d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lRH, rg β, mk [] b c d e f g⟩ : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lRJ, rg β, mk [] b c d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lRH, rg β,
          Function.update (mk [] b c d e f g) Stk.kin []⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lRJ) (rg β) (mk [] b c d e f g)) = _
    rfl
  rw [h, uIn]

private lemma stRHS (β x : Bool) (a b c d t f g : List Bool) :
    step Mw (⟨Option.some Lbl.lRH, rg β, mk a b c d (x :: t) f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lRH, rg β, mk a b c d t f g⟩ : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lRH, rg β, mk a b c d (x :: t) f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lRH, rg β,
          Function.update (mk a b c d (x :: t) f g) Stk.kD t⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lRH) (rg β) (mk a b c d (x :: t) f g)) = _
    rfl
  rw [h, uD]

private lemma stRHN (β : Bool) (a b c d f g : List Bool) :
    step Mw (⟨Option.some Lbl.lRH, rg β, mk a b c d [] f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lH, rg false, mk a b c d [] f g⟩
          : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lRH, rg β, mk a b c d [] f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lH, rg false,
          Function.update (mk a b c d [] f g) Stk.kD []⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lRH) (rg β) (mk a b c d [] f g)) = _
    rfl
  rw [h, uD]

private lemma stBDS (β x : Bool) (a b c d t f g : List Bool) :
    step Mw (⟨Option.some Lbl.lBD, rg β, mk a b c d (x :: t) f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lBD, rg β,
          mk a (false :: b) (false :: c) d t f (true :: g)⟩ : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lBD, rg β, mk a b c d (x :: t) f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lBD, rg β,
          Function.update (Function.update (Function.update
            (Function.update (mk a b c d (x :: t) f g) Stk.kD t)
              Stk.kS (false :: b)) Stk.kR (false :: c)) Stk.kC (true :: g)⟩
          : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lBD) (rg β) (mk a b c d (x :: t) f g)) = _
    rfl
  rw [h, uD, uS, uR, uC]

private lemma stITS (β x : Bool) (a b c d e f g : List Bool) :
    step Mw (⟨Option.some Lbl.lIT, rg β, mk a b c d e f (x :: g)⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lP1, rg true, mk a b c d e f g⟩
          : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lIT, rg β, mk a b c d e f (x :: g)⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lP1, rg true,
          Function.update (mk a b c d e f (x :: g)) Stk.kC g⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lIT) (rg β) (mk a b c d e f (x :: g))) = _
    rfl
  rw [h, uC]

private lemma stITN (β : Bool) (a b c d e f : List Bool) :
    step Mw (⟨Option.some Lbl.lIT, rg β, mk a b c d e f []⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lDR, rg false, mk a b c d e f []⟩
          : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lIT, rg β, mk a b c d e f []⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lDR, rg false,
          Function.update (mk a b c d e f []) Stk.kC []⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lIT) (rg β) (mk a b c d e f [])) = _
    rfl
  rw [h, uC]

private lemma stP1S (β r s : Bool) (a st rt d e f g : List Bool) :
    step Mw (⟨Option.some Lbl.lP1, rg β, mk a (s :: st) (r :: rt) d e f g⟩
        : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lP1,
          rg (bif r then s && β else s || β),
          mk a st rt (s :: d) (xor r (xor s β) :: e) (r :: f) g⟩ : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lP1, rg β, mk a (s :: st) (r :: rt) d e f g⟩
        : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lP1,
          rg (bif r then s && β else s || β),
          Function.update (Function.update (Function.update (Function.update
            (Function.update (mk a (s :: st) (r :: rt) d e f g) Stk.kR rt)
              Stk.kS st) Stk.kRh (r :: f)) Stk.kSh (s :: d))
                Stk.kD (xor r (xor s β) :: e)⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lP1) (rg β) (mk a (s :: st) (r :: rt) d e f g)) = _
    rfl
  rw [h, uR, uS, uRh, uSh, uD]

private lemma stP1N (β : Bool) (a b d e f g : List Bool) :
    step Mw (⟨Option.some Lbl.lP1, rg β, mk a b [] d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lPA, rg β, mk a b [] d e f g⟩ : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lP1, rg β, mk a b [] d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lPA, rg β,
          Function.update (mk a b [] d e f g) Stk.kR []⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lP1) (rg β) (mk a b [] d e f g)) = _
    rfl
  rw [h, uR]

private lemma stPA (β s d1 r1 : Bool) (a b c sh dd rh g : List Bool) :
    step Mw (⟨Option.some Lbl.lPA, rg β,
        mk a b c (s :: sh) (d1 :: dd) (r1 :: rh) g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lPB, rg β, mk a b c sh dd rh g⟩
          : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lPA, rg β,
        mk a b c (s :: sh) (d1 :: dd) (r1 :: rh) g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lPB, rg β,
          Function.update (Function.update (Function.update
            (mk a b c (s :: sh) (d1 :: dd) (r1 :: rh) g) Stk.kSh sh) Stk.kD dd)
              Stk.kRh rh⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lPA) (rg β)
      (mk a b c (s :: sh) (d1 :: dd) (r1 :: rh) g)) = _
    rfl
  rw [h, uSh, uD, uRh]

private lemma stPB (β s d1 r1 : Bool) (a b c sh dd rh g : List Bool) :
    step Mw (⟨Option.some Lbl.lPB, rg β,
        mk a b c (s :: sh) (d1 :: dd) (r1 :: rh) g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lPC, rg β, mk a (s :: b) c sh dd rh g⟩
          : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lPB, rg β,
        mk a b c (s :: sh) (d1 :: dd) (r1 :: rh) g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lPC, rg β,
          Function.update (Function.update (Function.update (Function.update
            (mk a b c (s :: sh) (d1 :: dd) (r1 :: rh) g) Stk.kSh sh) Stk.kS (s :: b))
              Stk.kD dd) Stk.kRh rh⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lPB) (rg β)
      (mk a b c (s :: sh) (d1 :: dd) (r1 :: rh) g)) = _
    rfl
  rw [h, uSh, uS, uD, uRh]

private lemma stPCS (β s d1 r1 : Bool) (a b c sh dd rh g : List Bool) :
    step Mw (⟨Option.some Lbl.lPC, rg β,
        mk a b c (s :: sh) (d1 :: dd) (r1 :: rh) g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lPC, rg β,
          mk a (s :: b) ((bif β then r1 else d1) :: c) sh dd rh g⟩
            : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lPC, rg β,
        mk a b c (s :: sh) (d1 :: dd) (r1 :: rh) g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lPC, rg β,
          Function.update (Function.update (Function.update (Function.update
            (Function.update (mk a b c (s :: sh) (d1 :: dd) (r1 :: rh) g) Stk.kSh sh)
              Stk.kS (s :: b)) Stk.kD dd) Stk.kRh rh)
                Stk.kR ((bif β then r1 else d1) :: c)⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lPC) (rg β)
      (mk a b c (s :: sh) (d1 :: dd) (r1 :: rh) g)) = _
    rfl
  rw [h, uSh, uS, uD, uRh, uR]

private lemma stPCN (β : Bool) (a b c e f g : List Bool) :
    step Mw (⟨Option.some Lbl.lPC, rg β, mk a b c [] e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lPE, rg β, mk a b c [] e f g⟩ : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lPC, rg β, mk a b c [] e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lPE, rg β,
          Function.update (mk a b c [] e f g) Stk.kSh []⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lPC) (rg β) (mk a b c [] e f g)) = _
    rfl
  rw [h, uSh]

private lemma stPE (β : Bool) (a b c d e f g : List Bool) :
    step Mw (⟨Option.some Lbl.lPE, rg β, mk a b c d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lIT, rg false,
          mk a ((!β) :: b) ((!β) :: (!β) :: c) d e f g⟩ : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lPE, rg β, mk a b c d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lIT, rg false,
          Function.update (Function.update (Function.update
            (mk a b c d e f g) Stk.kS ((!β) :: b)) Stk.kR ((!β) :: c))
              Stk.kR ((!β) :: (!β) :: c)⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lPE) (rg β) (mk a b c d e f g)) = _
    rfl
  rw [h, uS, uR, uR]

private lemma stDRS (β x : Bool) (a b c d e f g : List Bool) :
    step Mw (⟨Option.some Lbl.lDR, rg β, mk a b (x :: c) d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lDR, rg β, mk a b c d e f g⟩ : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lDR, rg β, mk a b (x :: c) d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lDR, rg β,
          Function.update (mk a b (x :: c) d e f g) Stk.kR c⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lDR) (rg β) (mk a b (x :: c) d e f g)) = _
    rfl
  rw [h, uR]

private lemma stDRN (β : Bool) (a b d e f g : List Bool) :
    step Mw (⟨Option.some Lbl.lDR, rg β, mk a b [] d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lH, rg false, mk a b [] d e f g⟩
          : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lDR, rg β, mk a b [] d e f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lH, rg false,
          Function.update (mk a b [] d e f g) Stk.kR []⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lDR) (rg β) (mk a b [] d e f g)) = _
    rfl
  rw [h, uR]

private lemma stBDN (β : Bool) (a b c d f g : List Bool) :
    step Mw (⟨Option.some Lbl.lBD, rg β, mk a b c d [] f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lIT, rg β,
          mk a (true :: false :: false :: false :: false :: false :: false :: b)
            (true :: false :: false :: false :: false :: false :: false :: c)
            d [] f (true :: true :: true :: g)⟩ : Cfg Gam Lbl Sg) := by
  have h : step Mw (⟨Option.some Lbl.lBD, rg β, mk a b c d [] f g⟩ : Cfg Gam Lbl Sg)
      = Option.some (⟨Option.some Lbl.lIT, rg β,
          Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update
            (mk a b c d [] f g) Stk.kD [])
            Stk.kS (false :: b))
            Stk.kS (false :: false :: b))
            Stk.kS (false :: false :: false :: b))
            Stk.kS (false :: false :: false :: false :: b))
            Stk.kS (false :: false :: false :: false :: false :: b))
            Stk.kS (false :: false :: false :: false :: false :: false :: b))
            Stk.kS (true :: false :: false :: false :: false :: false :: false :: b))
            Stk.kR (false :: c))
            Stk.kR (false :: false :: c))
            Stk.kR (false :: false :: false :: c))
            Stk.kR (false :: false :: false :: false :: c))
            Stk.kR (false :: false :: false :: false :: false :: c))
            Stk.kR (false :: false :: false :: false :: false :: false :: c))
            Stk.kR (true :: false :: false :: false :: false :: false :: false :: c))
            Stk.kC (true :: g))
            Stk.kC (true :: true :: g))
            Stk.kC (true :: true :: true :: g)⟩ : Cfg Gam Lbl Sg) := by
    show Option.some (stepAux (Mw Lbl.lBD) (rg β) (mk a b c d [] f g)) = _
    rfl
  rw [h, uD, uS, uS, uS, uS, uS, uS, uS, uR, uR, uR, uR, uR, uR, uR, uC, uC, uC]

/-! ### 6.  The phases -/

private lemma runV0F : ∀ (p : ℕ) (rest b c d acc f g : List Bool) (β : Bool),
    stepW^[p + 1] (Option.some (⟨Option.some Lbl.lV0, rg β,
        mk (List.replicate p true ++ false :: rest) b c d acc f g⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lV1, rg β,
          mk rest b c d (List.replicate p true ++ acc) f g⟩ : Cfg Gam Lbl Sg) := by
  intro p
  induction p with
  | zero =>
      intro rest b c d acc f g β
      exact chain1' rfl (stV0F β rest b c d acc f g) rfl
  | succ p ih =>
      intro rest b c d acc f g β
      rw [← repSnoc true p acc]
      refine chain1' (n := p + 1) (by omega) ?_ (ih rest b c d (true :: acc) f g β)
      show step Mw (⟨Option.some Lbl.lV0, rg β,
          mk (true :: (List.replicate p true ++ false :: rest)) b c d acc f g⟩
            : Cfg Gam Lbl Sg) = _
      exact stV0T β (List.replicate p true ++ false :: rest) b c d acc f g

private lemma runV0T : ∀ (n : ℕ) (b c d acc f g : List Bool) (β : Bool),
    stepW^[n + 1] (Option.some (⟨Option.some Lbl.lV0, rg β,
        mk (List.replicate n true) b c d acc f g⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lRH, rg β,
          mk [] b c d (List.replicate n true ++ acc) f g⟩ : Cfg Gam Lbl Sg) := by
  intro n
  induction n with
  | zero =>
      intro b c d acc f g β
      exact chain1' rfl (stV0N β b c d acc f g) rfl
  | succ n ih =>
      intro b c d acc f g β
      rw [← repSnoc true n acc]
      refine chain1' (n := n + 1) (by omega) ?_ (ih b c d (true :: acc) f g β)
      show step Mw (⟨Option.some Lbl.lV0, rg β,
          mk (true :: List.replicate n true) b c d acc f g⟩ : Cfg Gam Lbl Sg) = _
      exact stV0T β (List.replicate n true) b c d acc f g

private lemma runRJ : ∀ (l b c d e f g : List Bool) (β : Bool),
    stepW^[l.length + 1] (Option.some (⟨Option.some Lbl.lRJ, rg β,
        mk l b c d e f g⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lRH, rg β, mk [] b c d e f g⟩
          : Cfg Gam Lbl Sg) := by
  intro l
  induction l with
  | nil =>
      intro b c d e f g β
      exact chain1' rfl (stRJN β b c d e f g) rfl
  | cons x t ih =>
      intro b c d e f g β
      refine chain1' (n := t.length + 1) (by simp only [List.length_cons]) ?_
        (ih b c d e f g β)
      exact stRJS β x t b c d e f g

private lemma runRH : ∀ (l a b c d f g : List Bool) (β : Bool),
    stepW^[l.length + 1] (Option.some (⟨Option.some Lbl.lRH, rg β,
        mk a b c d l f g⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lH, rg false, mk a b c d [] f g⟩
          : Cfg Gam Lbl Sg) := by
  intro l
  induction l with
  | nil =>
      intro a b c d f g β
      exact chain1' rfl (stRHN β a b c d f g) rfl
  | cons x t ih =>
      intro a b c d f g β
      refine chain1' (n := t.length + 1) (by simp only [List.length_cons]) ?_
        (ih a b c d f g β)
      exact stRHS β x a b c d t f g

private lemma runDR : ∀ (l a b d e f g : List Bool) (β : Bool),
    stepW^[l.length + 1] (Option.some (⟨Option.some Lbl.lDR, rg β,
        mk a b l d e f g⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lH, rg false, mk a b [] d e f g⟩
          : Cfg Gam Lbl Sg) := by
  intro l
  induction l with
  | nil =>
      intro a b d e f g β
      exact chain1' rfl (stDRN β a b d e f g) rfl
  | cons x t ih =>
      intro a b d e f g β
      refine chain1' (n := t.length + 1) (by simp only [List.length_cons]) ?_
        (ih a b d e f g β)
      exact stDRS β x a b t d e f g

private lemma runBD : ∀ (n : ℕ) (a b c d f g : List Bool) (β : Bool),
    stepW^[n + 1] (Option.some (⟨Option.some Lbl.lBD, rg β,
        mk a b c d (List.replicate n true) f g⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lIT, rg β,
          mk a (true :: false :: false :: false :: false :: false :: false
              :: (List.replicate n false ++ b))
            (true :: false :: false :: false :: false :: false :: false
              :: (List.replicate n false ++ c))
            d [] f (true :: true :: true :: (List.replicate n true ++ g))⟩
          : Cfg Gam Lbl Sg) := by
  intro n
  induction n with
  | zero =>
      intro a b c d f g β
      exact chain1' rfl (stBDN β a b c d f g) rfl
  | succ n ih =>
      intro a b c d f g β
      rw [← repSnoc false n b, ← repSnoc false n c, ← repSnoc true n g]
      refine chain1' (n := n + 1) (by omega) ?_
        (ih a (false :: b) (false :: c) d f (true :: g) β)
      show step Mw (⟨Option.some Lbl.lBD, rg β,
          mk a b c d (true :: List.replicate n true) f g⟩ : Cfg Gam Lbl Sg) = _
      exact stBDS β true a b c d (List.replicate n true) f g

/-! ### 7.  The subtract sweep and the write-back sweep -/

private lemma runP1 : ∀ (rl sl : List Bool), rl.length = sl.length →
    ∀ (c : Bool) (a d e f g : List Bool),
    stepW^[rl.length + 1] (Option.some (⟨Option.some Lbl.lP1, rg c,
        mk a sl rl d e f g⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lPA, rg (sboC c rl sl),
          mk a [] [] (sl.reverse ++ d) ((sbdC c rl sl).reverse ++ e)
            (rl.reverse ++ f) g⟩ : Cfg Gam Lbl Sg) := by
  intro rl
  induction rl with
  | nil =>
      intro sl hlen c a d e f g
      cases sl with
      | cons y ys =>
          exfalso
          rw [List.length_nil, List.length_cons] at hlen
          omega
      | nil => exact chain1' rfl (stP1N c a [] d e f g) rfl
  | cons r rt ih =>
      intro sl hlen c a d e f g
      cases sl with
      | nil =>
          exfalso
          rw [List.length_cons, List.length_nil] at hlen
          omega
      | cons s st =>
          have hl : rt.length = st.length := by
            rw [List.length_cons, List.length_cons] at hlen
            omega
          have hsbo : sboC c (r :: rt) (s :: st)
              = sboC (bif r then s && c else s || c) rt st := rfl
          have hsbd : sbdC c (r :: rt) (s :: st)
              = xor r (xor s c) :: sbdC (bif r then s && c else s || c) rt st := rfl
          rw [hsbo, hsbd]
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
            List.length_cons]
          refine chain1' (n := rt.length + 1) (by omega) ?_
            (ih st hl (bif r then s && c else s || c) a (s :: d)
              (xor r (xor s c) :: e) (r :: f) g)
          exact stP1S c r s a st rt d e f g

private lemma condRev (β r1 d1 : Bool) (rr dd c : List Bool) :
    (bif β then (r1 :: rr) else (d1 :: dd)).reverse ++ c
      = (bif β then rr else dd).reverse ++ ((bif β then r1 else d1) :: c) := by
  cases β <;> simp

private lemma condRev2 (β : Bool) (RB DB : List Bool) :
    (bif β then RB.reverse else DB.reverse).reverse ++ [] = bif β then RB else DB := by
  cases β <;> simp

private lemma runPC : ∀ (u dd rr : List Bool), u.length = dd.length →
    dd.length = rr.length → ∀ (β : Bool) (a b c g : List Bool),
    stepW^[u.length + 1] (Option.some (⟨Option.some Lbl.lPC, rg β,
        mk a b c u dd rr g⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lPE, rg β,
          mk a (u.reverse ++ b) ((bif β then rr else dd).reverse ++ c) [] [] [] g⟩
            : Cfg Gam Lbl Sg) := by
  intro u
  induction u with
  | nil =>
      intro dd rr h1 h2 β a b c g
      cases dd with
      | cons y ys =>
          exfalso
          rw [List.length_nil, List.length_cons] at h1
          omega
      | nil =>
          cases rr with
          | cons z zs =>
              exfalso
              rw [List.length_nil, List.length_cons] at h2
              omega
          | nil =>
              cases β
              · exact chain1' rfl (stPCN false a b c [] [] g) rfl
              · exact chain1' rfl (stPCN true a b c [] [] g) rfl
  | cons s u' ih =>
      intro dd rr h1 h2 β a b c g
      cases dd with
      | nil =>
          exfalso
          rw [List.length_cons, List.length_nil] at h1
          omega
      | cons d1 dd' =>
          cases rr with
          | nil =>
              exfalso
              rw [List.length_cons, List.length_nil] at h2
              omega
          | cons r1 rr' =>
              have hl1 : u'.length = dd'.length := by
                rw [List.length_cons, List.length_cons] at h1
                omega
              have hl2 : dd'.length = rr'.length := by
                rw [List.length_cons, List.length_cons] at h2
                omega
              rw [condRev β r1 d1 rr' dd' c]
              simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
                List.length_cons]
              refine chain1' (n := u'.length + 1) (by omega) ?_
                (ih dd' rr' hl1 hl2 β a (s :: b) ((bif β then r1 else d1) :: c) g)
              exact stPCS β s d1 r1 a b c u' dd' rr' g

private lemma runCore : ∀ (m : ℕ) (SB DB RB : List Bool),
    SB.length = m → DB.length = m → RB.length = m →
    ∀ (s1 s2 d1 d2 r1 r2 β : Bool) (a g : List Bool),
    stepW^[m + 4] (Option.some (⟨Option.some Lbl.lPA, rg β,
        mk a [] [] (s2 :: s1 :: SB.reverse) (d2 :: d1 :: DB.reverse)
          (r2 :: r1 :: RB.reverse) g⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lIT, rg false,
          mk a ((!β) :: (SB ++ [s1])) ((!β) :: (!β) :: (bif β then RB else DB))
            [] [] [] g⟩ : Cfg Gam Lbl Sg) := by
  intro m SB DB RB hs hd hr s1 s2 d1 d2 r1 r2 β a g
  have hlen1 : (SB.reverse).length = (DB.reverse).length := by
    rw [List.length_reverse, List.length_reverse, hs, hd]
  have hlen2 : (DB.reverse).length = (RB.reverse).length := by
    rw [List.length_reverse, List.length_reverse, hd, hr]
  have hPC0 := runPC SB.reverse DB.reverse RB.reverse hlen1 hlen2 β a [s1] [] g
  rw [List.length_reverse, hs, List.reverse_reverse, condRev2] at hPC0
  have hPC : stepW^[m + 1] (Option.some (⟨Option.some Lbl.lPC, rg β,
      mk a [s1] [] SB.reverse DB.reverse RB.reverse g⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lPE, rg β,
          mk a (SB ++ [s1]) (bif β then RB else DB) [] [] [] g⟩
            : Cfg Gam Lbl Sg) := hPC0
  refine chain1' (n := m + 3) (by omega)
    (stPA β s2 d2 r2 a [] [] (s1 :: SB.reverse) (d1 :: DB.reverse) (r1 :: RB.reverse) g) ?_
  refine chain1' (n := m + 2) (by omega)
    (stPB β s1 d1 r1 a [] [] SB.reverse DB.reverse RB.reverse g) ?_
  refine chainN' (m := m + 1) (n := 1) (by omega) hPC ?_
  exact chain1' rfl (stPE β a (SB ++ [s1]) (bif β then RB else DB) [] [] [] g) rfl

/-! ### 8.  Shift laws, one iteration, and the loop -/

private lemma bitsT1 (k v : ℕ) : true :: bitsC k v = bitsC (k + 1) (2 * v + 1) :=
  bitsConsL true k v

private lemma bitsF1 (k v : ℕ) : false :: bitsC k v = bitsC (k + 1) (2 * v) :=
  bitsConsL false k v

private lemma bitsTT (k v : ℕ) :
    true :: true :: bitsC k v = bitsC (k + 2) (4 * v + 3) := by
  rw [bitsT1 k v, bitsT1 (k + 1) (2 * v + 1)]
  exact congrArg (bitsC (k + 2)) (by omega : 2 * (2 * v + 1) + 1 = 4 * v + 3)

private lemma bitsFF (k v : ℕ) :
    false :: false :: bitsC k v = bitsC (k + 2) (4 * v) := by
  rw [bitsF1 k v, bitsF1 (k + 1) (2 * v)]
  exact congrArg (bitsC (k + 2)) (by omega : 2 * (2 * v) = 4 * v)

private lemma runIter : ∀ (m Sv Rv : ℕ), Sv < 2 ^ (m + 2) → Rv < 2 ^ (m + 2) →
    ∀ (x : Bool) (a g : List Bool),
    stepW^[2 * m + 8] (Option.some (⟨Option.some Lbl.lIT, rg false,
        mk a (bitsC (m + 2) Sv) (bitsC (m + 2) Rv) [] [] [] (x :: g)⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lIT, rg false,
          mk a (bitsC (m + 2) (2 * Sv + (if Sv < Rv then 1 else 0)))
            (bitsC (m + 2) (if Sv < Rv then 4 * (Rv - Sv - 1) + 3 else 4 * Rv))
            [] [] [] g⟩ : Cfg Gam Lbl Sg) := by
  intro m Sv Rv hS hR x a g
  obtain ⟨s2, hs2⟩ := bitsSnocL (m + 1) Sv
  obtain ⟨s1, hs1⟩ := bitsSnocL m Sv
  obtain ⟨r2, hr2⟩ := bitsSnocL (m + 1) Rv
  obtain ⟨r1, hr1⟩ := bitsSnocL m Rv
  have hsrev : (bitsC (m + 2) Sv).reverse = s2 :: s1 :: (bitsC m Sv).reverse := by
    rw [hs2, hs1]
    simp
  have hrrev : (bitsC (m + 2) Rv).reverse = r2 :: r1 :: (bitsC m Rv).reverse := by
    rw [hr2, hr1]
    simp
  have hlenRS : (bitsC (m + 2) Rv).length = (bitsC (m + 2) Sv).length := by
    rw [bitsLen, bitsLen]
  have hP10 := runP1 (bitsC (m + 2) Rv) (bitsC (m + 2) Sv) hlenRS true a [] [] [] g
  rw [bitsLen] at hP10
  simp only [List.append_nil] at hP10
  rw [hsrev, hrrev] at hP10
  by_cases hlt : Sv < Rv
  · obtain ⟨hbo, hbd⟩ := dec1 (m + 2) Sv Rv hS hR hlt
    obtain ⟨d2, hd2⟩ := bitsSnocL (m + 1) (Rv - Sv - 1)
    obtain ⟨d1, hd1⟩ := bitsSnocL m (Rv - Sv - 1)
    have hdrev : (sbdC true (bitsC (m + 2) Rv) (bitsC (m + 2) Sv)).reverse
        = d2 :: d1 :: (bitsC m (Rv - Sv - 1)).reverse := by
      rw [hbd, hd2, hd1]
      simp
    rw [hbo, hdrev] at hP10
    have hP1 : stepW^[m + 3] (Option.some (⟨Option.some Lbl.lP1, rg true,
        mk a (bitsC (m + 2) Sv) (bitsC (m + 2) Rv) [] [] [] g⟩ : Cfg Gam Lbl Sg))
        = Option.some (⟨Option.some Lbl.lPA, rg false,
            mk a [] [] (s2 :: s1 :: (bitsC m Sv).reverse)
              (d2 :: d1 :: (bitsC m (Rv - Sv - 1)).reverse)
              (r2 :: r1 :: (bitsC m Rv).reverse) g⟩ : Cfg Gam Lbl Sg) := hP10
    have hC := runCore m (bitsC m Sv) (bitsC m (Rv - Sv - 1)) (bitsC m Rv)
      (bitsLen m Sv) (bitsLen m (Rv - Sv - 1)) (bitsLen m Rv)
      s1 s2 d1 d2 r1 r2 false a g
    have hC2 : stepW^[m + 4] (Option.some (⟨Option.some Lbl.lPA, rg false,
        mk a [] [] (s2 :: s1 :: (bitsC m Sv).reverse)
          (d2 :: d1 :: (bitsC m (Rv - Sv - 1)).reverse)
          (r2 :: r1 :: (bitsC m Rv).reverse) g⟩ : Cfg Gam Lbl Sg))
        = Option.some (⟨Option.some Lbl.lIT, rg false,
            mk a (true :: (bitsC m Sv ++ [s1]))
              (true :: true :: bitsC m (Rv - Sv - 1)) [] [] [] g⟩
              : Cfg Gam Lbl Sg) := hC
    rw [if_pos hlt, if_pos hlt]
    have hgS : bitsC (m + 2) (2 * Sv + 1) = true :: (bitsC m Sv ++ [s1]) := by
      rw [← hs1]
      exact (bitsT1 (m + 1) Sv).symm
    have hgR : bitsC (m + 2) (4 * (Rv - Sv - 1) + 3)
        = true :: true :: bitsC m (Rv - Sv - 1) := (bitsTT m (Rv - Sv - 1)).symm
    rw [hgS, hgR]
    refine chain1' (n := 2 * m + 7) (by omega)
      (stITS false x a (bitsC (m + 2) Sv) (bitsC (m + 2) Rv) [] [] [] g) ?_
    exact chainN' (m := m + 3) (n := m + 4) (by omega) hP1 hC2
  · have hRS : Rv ≤ Sv := by omega
    have hbo := dec2 (m + 2) Sv Rv hS hR hRS
    have hDlen : (sbdC true (bitsC (m + 2) Rv) (bitsC (m + 2) Sv)).length = m + 1 + 1 := by
      rw [sbdLen true _ _ hlenRS, bitsLen]
    obtain ⟨DL1, d2, hDLe, hDL1len⟩ := snocSplit _ (m + 1) hDlen
    obtain ⟨DB, d1, hDL1e, hDBlen⟩ := snocSplit DL1 m hDL1len
    have hdrev : (sbdC true (bitsC (m + 2) Rv) (bitsC (m + 2) Sv)).reverse
        = d2 :: d1 :: DB.reverse := by
      rw [hDLe, hDL1e]
      simp
    rw [hbo, hdrev] at hP10
    have hP1 : stepW^[m + 3] (Option.some (⟨Option.some Lbl.lP1, rg true,
        mk a (bitsC (m + 2) Sv) (bitsC (m + 2) Rv) [] [] [] g⟩ : Cfg Gam Lbl Sg))
        = Option.some (⟨Option.some Lbl.lPA, rg true,
            mk a [] [] (s2 :: s1 :: (bitsC m Sv).reverse) (d2 :: d1 :: DB.reverse)
              (r2 :: r1 :: (bitsC m Rv).reverse) g⟩ : Cfg Gam Lbl Sg) := hP10
    have hC := runCore m (bitsC m Sv) DB (bitsC m Rv)
      (bitsLen m Sv) hDBlen (bitsLen m Rv) s1 s2 d1 d2 r1 r2 true a g
    have hC2 : stepW^[m + 4] (Option.some (⟨Option.some Lbl.lPA, rg true,
        mk a [] [] (s2 :: s1 :: (bitsC m Sv).reverse) (d2 :: d1 :: DB.reverse)
          (r2 :: r1 :: (bitsC m Rv).reverse) g⟩ : Cfg Gam Lbl Sg))
        = Option.some (⟨Option.some Lbl.lIT, rg false,
            mk a (false :: (bitsC m Sv ++ [s1]))
              (false :: false :: bitsC m Rv) [] [] [] g⟩ : Cfg Gam Lbl Sg) := hC
    rw [if_neg hlt, if_neg hlt]
    have hgS : bitsC (m + 2) (2 * Sv + 0) = false :: (bitsC m Sv ++ [s1]) := by
      rw [← hs1]
      exact (bitsF1 (m + 1) Sv).symm
    have hgR : bitsC (m + 2) (4 * Rv) = false :: false :: bitsC m Rv := (bitsFF m Rv).symm
    rw [hgS, hgR]
    refine chain1' (n := 2 * m + 7) (by omega)
      (stITS false x a (bitsC (m + 2) Sv) (bitsC (m + 2) Rv) [] [] [] g) ?_
    exact chainN' (m := m + 3) (n := m + 4) (by omega) hP1 hC2

private lemma runLoop : ∀ (n k m : ℕ),
    (∀ j : ℕ, j ≤ k + n → sqf j < 2 ^ (m + 2) ∧ rmf j < 2 ^ (m + 2)) →
    ∀ (a g : List Bool),
    stepW^[n * (2 * m + 8)] (Option.some (⟨Option.some Lbl.lIT, rg false,
        mk a (bitsC (m + 2) (sqf k)) (bitsC (m + 2) (rmf k)) [] [] []
          (List.replicate n true ++ g)⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lIT, rg false,
          mk a (bitsC (m + 2) (sqf (k + n))) (bitsC (m + 2) (rmf (k + n)))
            [] [] [] g⟩ : Cfg Gam Lbl Sg) := by
  intro n
  induction n with
  | zero =>
      intro k m hb a g
      have e0 : (0 : ℕ) * (2 * m + 8) = 0 := Nat.zero_mul _
      rw [e0]
      rfl
  | succ n ih =>
      intro k m hb a g
      obtain ⟨hs, hr⟩ := hb k (by omega)
      have hstep := runIter m (sqf k) (rmf k) hs hr true a (List.replicate n true ++ g)
      have e1 : sqf (k + 1) = 2 * sqf k + (if sqf k < rmf k then 1 else 0) := rfl
      have e2 : rmf (k + 1)
          = (if sqf k < rmf k then 4 * (rmf k - sqf k - 1) + 3 else 4 * rmf k) := rfl
      rw [← e1, ← e2] at hstep
      have hb' : ∀ j : ℕ, j ≤ k + 1 + n → sqf j < 2 ^ (m + 2) ∧ rmf j < 2 ^ (m + 2) := by
        intro j hj
        exact hb j (by omega)
      have hIH := ih (k + 1) m hb' a g
      have hk : k + 1 + n = k + (n + 1) := by omega
      rw [hk] at hIH
      exact chainN' (m := 2 * m + 8) (n := n * (2 * m + 8)) (by ring) hstep hIH

/-! ### 9.  Initial configuration, transport, and time weakening -/

private lemma initStk (w : List Bool) :
    (Turing.initList tmW w).stk = mk w [] [] [] [] [] [] := by
  obtain ⟨-, -, h0, hne, -⟩ := ShiTM.initList_haltList_laws tmW w []
  funext k
  cases k
  · exact h0
  · exact hne Stk.kS (by show Stk.kS ≠ Stk.kin; decide)
  · exact hne Stk.kR (by show Stk.kR ≠ Stk.kin; decide)
  · exact hne Stk.kSh (by show Stk.kSh ≠ Stk.kin; decide)
  · exact hne Stk.kD (by show Stk.kD ≠ Stk.kin; decide)
  · exact hne Stk.kRh (by show Stk.kRh ≠ Stk.kin; decide)
  · exact hne Stk.kC (by show Stk.kC ≠ Stk.kin; decide)

private lemma initCfg (w : List Bool) :
    Turing.initList tmW w
      = (⟨Option.some Lbl.lV0, rg false, mk w [] [] [] [] [] []⟩ : Cfg Gam Lbl Sg) :=
  congrArg (fun S => (⟨Option.some Lbl.lV0, rg false, S⟩ : Cfg Gam Lbl Sg)) (initStk w)

private lemma transportIO (tm : Turing.FinTM2) (u u' : List (tm.Γ tm.k₀))
    (o o' : List (tm.Γ tm.k₁)) (n : ℕ) (hu : u = u') (ho : o = o')
    (hh : Nonempty (Turing.TM2OutputsInTime tm u' (Option.some o') n)) :
    Nonempty (Turing.TM2OutputsInTime tm u (Option.some o) n) := by
  subst hu
  subst ho
  exact hh

private lemma weakenT (tm : Turing.FinTM2) (u : List (tm.Γ tm.k₀))
    (o : Option (List (tm.Γ tm.k₁))) (n n' : ℕ) (hn : n ≤ n')
    (hh : Nonempty (Turing.TM2OutputsInTime tm u o n)) :
    Nonempty (Turing.TM2OutputsInTime tm u o n') := by
  obtain ⟨hx⟩ := hh
  obtain ⟨he, hle⟩ := hx
  exact ⟨⟨he, Nat.le_trans hle hn⟩⟩

/-! ### 10.  The full runs -/

private lemma bnds (h : ℕ) : ∀ j : ℕ, j ≤ 0 + (h + 3) →
    sqf j < 2 ^ (h + 5 + 2) ∧ rmf j < 2 ^ (h + 5 + 2) := by
  intro j hj
  obtain ⟨-, hle, -, hlt⟩ := recC j
  have hA : (2 : ℕ) ^ (j + 1) ≤ 2 ^ (h + 5 + 2) := powMono _ _ (by omega)
  have hB : (2 : ℕ) ^ (j + 2) ≤ 2 ^ (h + 5 + 2) := powMono _ _ (by omega)
  have hC : (2 : ℕ) ^ (j + 2) = 2 ^ (j + 1) * 2 := by rw [pow_succ]
  omega

private lemma mainRun (h : ℕ) :
    stepW^[2 * h * h + 27 * h + 66] (Option.some (⟨Option.some Lbl.lV0, rg false,
        mk (List.replicate h true ++ [false]) [] [] [] [] [] []⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lH, rg false,
          mk [] (bitsC (h + 7) (sqf (h + 3))) [] [] [] [] []⟩ : Cfg Gam Lbl Sg) := by
  obtain ⟨P, hP⟩ : ∃ P : ℕ, 2 * h * h = P := ⟨_, rfl⟩
  have hprod : (h + 3) * (2 * (h + 5) + 8) = P + 24 * h + 54 := by
    rw [← hP]
    ring
  rw [hP]
  have h1 := runV0F h [] [] [] [] [] [] [] false
  simp only [List.append_nil] at h1
  have h3x := runBD h [] [] [] [] [] [] false
  simp only [List.append_nil] at h3x
  rw [← bitsOne h] at h3x
  have h3 : stepW^[h + 1] (Option.some (⟨Option.some Lbl.lBD, rg false,
      mk [] [] [] [] (List.replicate h true) [] []⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lIT, rg false,
          mk [] (bitsC (h + 5 + 2) (sqf 0)) (bitsC (h + 5 + 2) (rmf 0)) [] [] []
            (List.replicate (h + 3) true)⟩ : Cfg Gam Lbl Sg) := h3x
  have h4 := runLoop (h + 3) 0 (h + 5) (bnds h) [] []
  rw [Nat.zero_add] at h4
  simp only [List.append_nil] at h4
  have h6 := runDR (bitsC (h + 5 + 2) (rmf (h + 3))) []
    (bitsC (h + 5 + 2) (sqf (h + 3))) [] [] [] [] false
  rw [bitsLen] at h6
  refine chainN' (m := h + 1) (n := 1 + ((h + 1) + ((h + 3) * (2 * (h + 5) + 8)
      + (1 + (h + 5 + 2 + 1))))) (by omega) h1 ?_
  refine chain1' (n := (h + 1) + ((h + 3) * (2 * (h + 5) + 8)
      + (1 + (h + 5 + 2 + 1)))) (by omega)
    (stV1N false [] [] [] (List.replicate h true) [] []) ?_
  refine chainN' (m := h + 1) (n := (h + 3) * (2 * (h + 5) + 8)
      + (1 + (h + 5 + 2 + 1))) (by omega) h3 ?_
  refine chainN' (m := (h + 3) * (2 * (h + 5) + 8)) (n := 1 + (h + 5 + 2 + 1))
    (by omega) h4 ?_
  refine chain1' (n := h + 5 + 2 + 1) (by omega)
    (stITN false [] (bitsC (h + 5 + 2) (sqf (h + 3)))
      (bitsC (h + 5 + 2) (rmf (h + 3))) [] [] []) ?_
  exact h6

private lemma rejA (p : ℕ) (y : Bool) (rest : List Bool) :
    stepW^[(p + 1) + (1 + ((rest.length + 1) + (p + 1)))]
        (Option.some (⟨Option.some Lbl.lV0, rg false,
          mk (List.replicate p true ++ false :: y :: rest) [] [] [] [] [] []⟩
            : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lH, rg false, mk [] [] [] [] [] [] []⟩
          : Cfg Gam Lbl Sg) := by
  have h1 := runV0F p (y :: rest) [] [] [] [] [] [] false
  simp only [List.append_nil] at h1
  refine chainN' (m := p + 1) (n := 1 + ((rest.length + 1) + (p + 1))) (by omega) h1 ?_
  refine chain1' (n := (rest.length + 1) + (p + 1)) (by omega)
    (stV1S false y rest [] [] [] (List.replicate p true) [] []) ?_
  refine chainN' (m := rest.length + 1) (n := p + 1) (by omega)
    (runRJ rest [] [] [] (List.replicate p true) [] [] false) ?_
  have h4 := runRH (List.replicate p true) [] [] [] [] [] [] false
  rw [List.length_replicate] at h4
  exact h4

private lemma rejB (n : ℕ) :
    stepW^[(n + 1) + (n + 1)] (Option.some (⟨Option.some Lbl.lV0, rg false,
        mk (List.replicate n true) [] [] [] [] [] []⟩ : Cfg Gam Lbl Sg))
      = Option.some (⟨Option.some Lbl.lH, rg false, mk [] [] [] [] [] [] []⟩
          : Cfg Gam Lbl Sg) := by
  have h1 := runV0T n [] [] [] [] [] [] false
  simp only [List.append_nil] at h1
  refine chainN' (m := n + 1) (n := n + 1) rfl h1 ?_
  have h2 := runRH (List.replicate n true) [] [] [] [] [] [] false
  rw [List.length_replicate] at h2
  exact h2

/-! ### 11.  The statement -/

theorem _root_.BQPReferenceValidation.candidate35 :
    -- (1) THE INTEGER-SQUARE-ROOT MACHINE.  ONE `FinTM2`, seven `Bool` stacks and
    -- THIRTEEN labels, whose input port carries the unary code of `h` and whose output
    -- port carries the `(h + 7)`-bit little-endian expansion of
    -- `S = Nat.sqrt (2 * 4 ^ (h + 3)) = ⌊2 ^ (h + 3) * √2⌋` -- the quantity from which
    -- `RF-BUILDc`'s five thresholds `A`, `2A`, `2A + 2S`, `2A + 4S`, `2A + 4S + 16` are
    -- built and which `ROUTER-1b` compares against but takes as GIVEN.  The step count is
    -- `2 * h * h + 27 * h + 67`: QUADRATIC in `h`, not `2 ^ h`, because the algorithm is
    -- the digit-by-digit (restoring) square root -- `h + 3` iterations, one output bit
    -- each -- and not repeated subtraction of odd numbers.  The bit encoder is
    -- ∀-QUANTIFIED and pinned only by its two defining equations, so any consumer's own
    -- encoder (in particular `ROUTER-1b`'s `bits`) may be substituted.
    (∃ (tm : Turing.FinTM2) (ei : tm.Γ tm.k₀ ≃ Bool) (eo : tm.Γ tm.k₁ ≃ Bool),
      (∀ bits : ℕ → ℕ → List Bool,
          (∀ n : ℕ, bits 0 n = []) →
          (∀ k n : ℕ, bits (k + 1) n = (n % 2 == 1) :: bits k (n / 2)) →
          ∀ h : ℕ, Nonempty (Turing.TM2OutputsInTime tm
            (List.map ei.invFun (List.replicate h true ++ [false]))
            (Option.some (List.map eo.invFun
              (bits (h + 7) (Nat.sqrt (2 * 4 ^ (h + 3))))))
            (2 * h * h + 27 * h + 67)))
      -- (2) THE REJECT PATH, and with it TOTALITY.  The SAME machine halts on EVERY input
      -- that is not a well-formed unary code -- no terminator, or junk after it -- with
      -- EMPTY output, inside `2 * |w| + 4` steps, every stack drained and the register
      -- back at its initial value.  Nothing is left undefined on malformed input.
    ∧ (∀ w : List Bool, (∀ h : ℕ, w ≠ List.replicate h true ++ [false]) →
          Nonempty (Turing.TM2OutputsInTime tm (List.map ei.invFun w)
            (Option.some ([] : List (tm.Γ tm.k₁))) (2 * w.length + 4))))
    -- (3) NON-VACUITY, INSIDE THE THEOREM.  At `h = 0` and `h = 1` the computed value is
    -- exhibited: `⌊8√2⌋ = 11` on seven bits and `⌊16√2⌋ = 22` on eight, two genuinely
    -- different non-empty strings -- so the accept outputs are neither degenerate nor
    -- confusable with the reject output.
  ∧ (∃ bits : ℕ → ℕ → List Bool,
      (∀ n : ℕ, bits 0 n = [])
    ∧ (∀ k n : ℕ, bits (k + 1) n = (n % 2 == 1) :: bits k (n / 2))
    ∧ Nat.sqrt (2 * 4 ^ (0 + 3)) = 11
    ∧ Nat.sqrt (2 * 4 ^ (1 + 3)) = 22
    ∧ bits (0 + 7) (Nat.sqrt (2 * 4 ^ (0 + 3)))
        = [true, true, false, true, false, false, false]
    ∧ bits (1 + 7) (Nat.sqrt (2 * 4 ^ (1 + 3)))
        = [false, true, true, false, true, false, false, false]
    ∧ bits (0 + 7) (Nat.sqrt (2 * 4 ^ (0 + 3))) ≠ []
    ∧ bits (0 + 7) (Nat.sqrt (2 * 4 ^ (0 + 3)))
        ≠ bits (1 + 7) (Nat.sqrt (2 * 4 ^ (1 + 3)))) := by
  have hs0 : Nat.sqrt (2 * 4 ^ (0 + 3)) = 11 := (recC 3).2.2.1
  have hs1 : Nat.sqrt (2 * 4 ^ (1 + 3)) = 22 := (recC 4).2.2.1
  refine ⟨⟨tmW, Equiv.refl Bool, Equiv.refl Bool, ?_, ?_⟩, ?_⟩
  · intro bits hb0 hbs h
    have hbe : ∀ k n : ℕ, bits k n = bitsC k n := by
      intro k
      induction k with
      | zero => intro n; exact hb0 n
      | succ k ih =>
          intro n
          exact (hbs k n).trans (congrArg (fun l => (n % 2 == 1) :: l) (ih (n / 2)))
    have hsq : Nat.sqrt (2 * 4 ^ (h + 3)) = sqf (h + 3) := (recC (h + 3)).2.2.1
    rw [hbe, hsq]
    refine transportIO tmW _ (List.replicate h true ++ [false]) _
      (bitsC (h + 7) (sqf (h + 3))) _ (List.map_id _) (List.map_id _) ?_
    exact (ShiTM.outputsInTime_of_run_to_halt tmW (List.replicate h true ++ [false])
      (bitsC (h + 7) (sqf (h + 3)))).1 Lbl.lH
      (mk [] (bitsC (h + 7) (sqf (h + 3))) [] [] [] [] []) (2 * h * h + 27 * h + 66)
      rfl (by rw [initCfg]; exact mainRun h) rfl
      (by
        intro k hk
        cases k
        · rfl
        · exact absurd rfl hk
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl)
  · intro w hw
    rcases classify w with ⟨p, rest, hwe⟩ | ⟨n, hwe⟩
    · cases rest with
      | nil => exact absurd hwe (hw p)
      | cons y rest' =>
          subst hwe
          refine transportIO tmW _ (List.replicate p true ++ false :: y :: rest') _ []
            _ (List.map_id _) rfl ?_
          refine weakenT tmW _ _ ((p + 1) + (1 + ((rest'.length + 1) + (p + 1))) + 1)
            (2 * (List.replicate p true ++ false :: y :: rest').length + 4) ?_ ?_
          · simp only [List.length_append, List.length_replicate, List.length_cons]
            omega
          · exact (ShiTM.outputsInTime_of_run_to_halt tmW
              (List.replicate p true ++ false :: y :: rest') []).1 Lbl.lH
              (mk [] [] [] [] [] [] [])
              ((p + 1) + (1 + ((rest'.length + 1) + (p + 1))))
              rfl (by rw [initCfg]; exact rejA p y rest') rfl
              (by
                intro k hk
                cases k <;> rfl)
    · subst hwe
      refine transportIO tmW _ (List.replicate n true) _ [] _ (List.map_id _) rfl ?_
      refine weakenT tmW _ _ ((n + 1) + (n + 1) + 1)
        (2 * (List.replicate n true).length + 4) ?_ ?_
      · rw [List.length_replicate]
        omega
      · exact (ShiTM.outputsInTime_of_run_to_halt tmW (List.replicate n true) []).1
          Lbl.lH (mk [] [] [] [] [] [] []) ((n + 1) + (n + 1))
          rfl (by rw [initCfg]; exact rejB n) rfl
          (by
            intro k hk
            cases k <;> rfl)
  · refine ⟨bitsC, fun n => rfl, fun k n => rfl, hs0, hs1, ?_, ?_, ?_, ?_⟩
    · rw [hs0]
      rfl
    · rw [hs1]
      rfl
    · rw [hs0]
      decide
    · rw [hs0, hs1]
      decide

end BQPReferenceValidation.Source35

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate35
    let target ← getConstInfo ``ShiTM.integer_square_root_machine_for_the_router_thresholds
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiTM.integer_square_root_machine_for_the_router_thresholds"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiTM.integer_square_root_machine_for_the_router_thresholds"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiTM.integer_square_root_machine_for_the_router_thresholds"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate35
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiTM.integer_square_root_machine_for_the_router_thresholds; axioms {axioms}"
