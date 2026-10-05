/-
BRIDGE-SIMi.  PHASE AGREEMENT -- conjunct (5) of the semantic bridge.

BRIDGE-SIMf matched the forward simulation of a gate list with PATH-1b's backward path
sum as a BIJECTION of branches.  This file matches the AMPLITUDES: along the matched
branch, PATH-1b's `A` equals `(√2)⁻¹` to the Hadamard count times `ω = exp (i π / 4)` to
the exponent the classical machine accumulates, read mod 8.

The exponent is produced CONSTRUCTIVELY, as the fold `Pph` of the per-block phase
increments.  This is worth stating plainly: PATH-1b's own clause only asserts that SOME
function `e` of the branch exists with `A = (√2)⁻¹^N ω^(e b)`, and the standing plan was
to skolemise it and then argue that any two witnesses agree mod 8 because `(√2)⁻¹^N ≠ 0`.
That step is UNNECESSARY.  `Pph` is an explicit witness, so the consumer never has to
choose one, and no injectivity of `k ↦ ω^k` is needed anywhere.

Hypotheses: PATH-1b's `N`, `A`, `P` recursions; the forward action `fw` and phase
increment `ph` of BRIDGE-SIMc together with its clauses (B) and (C); and BRIDGE-SIMf's
`Fwd`, `Bk` recursions plus its conjunct (3), that every forward branch is a backward
path landing on the start state.
-/
import Definitions.Def_ShiShallow_Core

namespace BQPBridgeReference

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiShallow

private def hWire {m : ℕ} : Instr m → Option (Fin m)
  | Instr.h i => some i
  | Instr.s _ => none
  | Instr.t _ => none
  | Instr.x _ => none
  | Instr.cnot _ _ _ => none

private def pphL {m : ℕ} (fwm : Instr m → Bool → Bits m → Bits m)
    (phm : Instr m → Bool → Bits m → ZMod 8) :
    List (Instr m) → Bits m → List Bool → ZMod 8
  | [], _, _ => 0
  | g :: gs, z, w =>
      match hWire g with
      | some _ => phm g w.headI z + pphL fwm phm gs (fwm g w.headI z) w.tail
      | none => phm g false z + pphL fwm phm gs (fwm g false z) w

theorem phaseAgreement :
    ∀ (N : ∀ m : ℕ, List (Instr m) → ℕ)
      (A : ∀ m : ℕ, (Instr m → Bits m → ℂ) → (Instr m → Bits m → Bits m) →
            List (Instr m) → Bits m → List Bool → ℂ)
      (P : ∀ m : ℕ, (Instr m → Bits m → Bits m) →
            List (Instr m) → Bits m → List Bool → Bits m)
      (fw : ∀ m : ℕ, Instr m → Bool → Bits m → Bits m)
      (ph : ∀ m : ℕ, Instr m → Bool → Bits m → ZMod 8)
      (Fwd : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → Bits m)
      (Bk : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → List Bool),
      -- PATH-1b: `N` counts the Hadamard gates
      (∀ m : ℕ, N m [] = 0) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)), N m (Instr.h i :: gs) = N m gs + 1) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)), (∀ i, g ≠ Instr.h i) →
          N m (g :: gs) = N m gs) →
      -- PATH-1b: the branch amplitude
      (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m)
          (y : Bits m) (bits : List Bool), A m coef perm [] y bits = 1) →
      (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m)
          (i : Fin m) (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
          A m coef perm (Instr.h i :: gs) y bits
            = A m coef perm gs y bits.tail
                * hMat (P m perm gs y bits.tail i) (bits.headD false)) →
      (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m)
          (g : Instr m) (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
          (∀ i, g ≠ Instr.h i) →
          A m coef perm (g :: gs) y bits
            = A m coef perm gs y bits * coef g (P m perm gs y bits)) →
      -- BRIDGE-SIMc: the Hadamard block writes the witness bit and pays a sign
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          fw m (Instr.h i) a z = Function.update z i a) →
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          ph m (Instr.h i) a z = (if z i && a then 4 else 0)) →
      -- BRIDGE-SIMc (B): the gate coefficient is the block's phase increment
      (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
          (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
              Instr.apply g ψ z = coef g z * ψ (perm g z)) →
          ∀ (g : Instr m), (∀ i, g ≠ Instr.h i) → ∀ (a : Bool) (z : Bits m),
            coef g (fw m g a z)
              = Complex.exp (Complex.I * Real.pi / 4) ^ (ph m g a z).val) →
      -- BRIDGE-SIMc (C): the Hadamard matrix entry
      (∀ a b : Bool, hMat a b
            = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
                * Complex.exp (Complex.I * Real.pi / 4) ^ (if a && b then 4 else 0)) →
      -- BRIDGE-SIMf: the forward state and the destroyed-bit list
      (∀ (m : ℕ) (z : Bits m) (w : List Bool), Fwd m [] z w = z) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          Fwd m (Instr.h i :: gs) z w = Fwd m gs (fw m (Instr.h i) w.headI z) w.tail) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          (∀ i, g ≠ Instr.h i) → Fwd m (g :: gs) z w = Fwd m gs (fw m g false z) w) →
      (∀ (m : ℕ) (z : Bits m) (w : List Bool), Bk m [] z w = []) →
      (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          Bk m (Instr.h i :: gs) z w
            = z i :: Bk m gs (fw m (Instr.h i) w.headI z) w.tail) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
          (∀ i, g ≠ Instr.h i) → Bk m (g :: gs) z w = Bk m gs (fw m g false z) w) →
      -- BRIDGE-SIMf (3): every forward branch is a backward path landing on the start
      (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
          (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
              Instr.apply g ψ z = coef g z * ψ (perm g z)) →
          ∀ (gs : List (Instr m)) (z : Bits m) (w : List Bool),
            P m perm gs (Fwd m gs z w) (Bk m gs z w) = z) →
      ∃ Pph : ∀ m : ℕ, List (Instr m) → Bits m → List Bool → ZMod 8,
        -- the accumulated phase exponent of the classical run
        (∀ (m : ℕ) (z : Bits m) (w : List Bool), Pph m [] z w = 0)
        ∧ (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
            Pph m (Instr.h i :: gs) z w
              = ph m (Instr.h i) w.headI z
                  + Pph m gs (fw m (Instr.h i) w.headI z) w.tail)
        ∧ (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
            (∀ i, g ≠ Instr.h i) →
            Pph m (g :: gs) z w = ph m g false z + Pph m gs (fw m g false z) w)
        -- `ω` has order eight, so the exponent may be read mod 8
        ∧ Complex.exp (Complex.I * Real.pi / 4) ^ 8 = 1
        ∧ (∀ k1 k2 : ZMod 8,
            Complex.exp (Complex.I * Real.pi / 4) ^ ((k1 + k2).val)
              = Complex.exp (Complex.I * Real.pi / 4) ^ (k1.val)
                  * Complex.exp (Complex.I * Real.pi / 4) ^ (k2.val))
        -- (5) PHASE AGREEMENT
        ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
            (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
                Instr.apply g ψ z = coef g z * ψ (perm g z)) →
            ∀ (gs : List (Instr m)) (z : Bits m) (w : List Bool),
              A m coef perm gs (Fwd m gs z w) (Bk m gs z w)
                = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ (N m gs)
                    * Complex.exp (Complex.I * Real.pi / 4)
                        ^ ((Pph m gs z w).val)) := by
  intro N A P fw ph Fwd Bk hN0 hNh hNg hA0 hAh hAg hfwh hphh hcoef hMateq
    hF0 hFh hFg hB0 hBh hBg hpath
  -- `ω` has order eight
  have hw4 : (Complex.exp (Complex.I * Real.pi / 4)) ^ 4 = -1 := by
    have h : (Complex.exp (Complex.I * Real.pi / 4)) ^ 4
        = Complex.exp (Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4
            + Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4) := by
      rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]
      ring
    have h2 : Complex.I * (Real.pi : ℂ) / 4 + Complex.I * (Real.pi : ℂ) / 4
        + Complex.I * (Real.pi : ℂ) / 4 + Complex.I * (Real.pi : ℂ) / 4
        = (Real.pi : ℂ) * Complex.I := by ring
    rw [h, h2, Complex.exp_pi_mul_I]
  have hw8 : (Complex.exp (Complex.I * Real.pi / 4)) ^ 8 = 1 := by
    have h : (Complex.exp (Complex.I * Real.pi / 4)) ^ 8
        = ((Complex.exp (Complex.I * Real.pi / 4)) ^ 4) ^ 2 := by ring
    rw [h, hw4]
    ring
  have hpow : ∀ n : ℕ,
      (Complex.exp (Complex.I * Real.pi / 4)) ^ n
        = (Complex.exp (Complex.I * Real.pi / 4)) ^ (n % 8) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n 8]
    rw [pow_add, pow_mul, hw8, one_pow, one_mul]
  have haddv : ∀ k1 k2 : ZMod 8,
      (Complex.exp (Complex.I * Real.pi / 4)) ^ ((k1 + k2).val)
        = (Complex.exp (Complex.I * Real.pi / 4)) ^ (k1.val)
            * (Complex.exp (Complex.I * Real.pi / 4)) ^ (k2.val) := by
    intro k1 k2
    rw [← pow_add, hpow ((k1 + k2).val), hpow (k1.val + k2.val)]
    congr 1
    rw [ZMod.val_add]
    omega
  have hcase : ∀ c : Bool,
      (Complex.exp (Complex.I * Real.pi / 4)) ^ ((if c then (4 : ZMod 8) else 0)).val
        = (Complex.exp (Complex.I * Real.pi / 4)) ^ (if c then 4 else 0 : ℕ) := by
    intro c
    cases c
    · rw [show ((if false then (4 : ZMod 8) else 0)).val = 0 from by decide]
      rw [show (if false then 4 else 0 : ℕ) = 0 from by decide]
    · rw [show ((if true then (4 : ZMod 8) else 0)).val = 4 from by decide]
      rw [show (if true then 4 else 0 : ℕ) = 4 from by decide]
  -- the recursion clauses of the accumulated phase
  have hP0 : ∀ (m : ℕ) (z : Bits m) (w : List Bool), pphL (fw m) (ph m) [] z w = 0 := by
    intro m z w; first | rfl | simp [pphL]
  have hPh : ∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
      pphL (fw m) (ph m) (Instr.h i :: gs) z w
        = ph m (Instr.h i) w.headI z
            + pphL (fw m) (ph m) gs (fw m (Instr.h i) w.headI z) w.tail := by
    intro m i gs z w; first | rfl | simp [pphL, hWire]
  have hPg : ∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)) (z : Bits m) (w : List Bool),
      (∀ i, g ≠ Instr.h i) →
      pphL (fw m) (ph m) (g :: gs) z w
        = ph m g false z + pphL (fw m) (ph m) gs (fw m g false z) w := by
    intro m g gs z w hg
    cases g with
    | h i => exact absurd rfl (hg i)
    | s i => first | rfl | simp [pphL, hWire]
    | t i => first | rfl | simp [pphL, hWire]
    | x i => first | rfl | simp [pphL, hWire]
    | cnot i j hij => first | rfl | simp [pphL, hWire]
  have hmain : ∀ (m : ℕ) (coef : Instr m → Bits m → ℂ)
      (perm : Instr m → Bits m → Bits m),
      (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
          Instr.apply g ψ z = coef g z * ψ (perm g z)) →
      ∀ (gs : List (Instr m)) (z : Bits m) (w : List Bool),
        A m coef perm gs (Fwd m gs z w) (Bk m gs z w)
          = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ (N m gs)
              * Complex.exp (Complex.I * Real.pi / 4)
                  ^ ((pphL (fw m) (ph m) gs z w).val) := by
   intro m coef perm hdata gs
   induction gs with
   | nil =>
     intro z w
     rw [hF0, hB0, hA0, hN0, hP0]
     rw [show ((0 : ZMod 8)).val = 0 from by decide]
     simp
   | cons g gs ih =>
     intro z w
     by_cases hg : ∀ i, g ≠ Instr.h i
     · rw [hFg m g gs z w hg, hBg m g gs z w hg, hAg m coef perm g gs _ _ hg,
         hpath m coef perm hdata gs (fw m g false z) w, ih (fw m g false z) w,
         hcoef m coef perm hdata g hg false z, hNg m g gs hg, hPg m g gs z w hg,
         haddv]
       ring
     · push_neg at hg
       obtain ⟨i, hi⟩ := hg
       subst hi
       rw [hFh m i gs z w, hBh m i gs z w, hAh m coef perm i gs _ _]
       have ht1 : (z i :: Bk m gs (fw m (Instr.h i) w.headI z) w.tail).tail
           = Bk m gs (fw m (Instr.h i) w.headI z) w.tail := rfl
       have hd1 : (z i :: Bk m gs (fw m (Instr.h i) w.headI z) w.tail).headD false
           = z i := rfl
       rw [ht1, hd1, hpath m coef perm hdata gs (fw m (Instr.h i) w.headI z) w.tail,
         ih (fw m (Instr.h i) w.headI z) w.tail]
       have hz1i : (fw m (Instr.h i) w.headI z) i = w.headI := by
         rw [hfwh m i w.headI z]
         simp
       rw [hz1i, hMateq w.headI (z i), hNh m i gs, hPh m i gs z w,
         hphh m i w.headI z, haddv, hcase]
       have hcomm : (z i && w.headI) = (w.headI && z i) := Bool.and_comm _ _
       rw [hcomm]
       ring

  refine ⟨fun m => pphL (fw m) (ph m), hP0, hPh, hPg, hw8, haddv, hmain⟩

end BQPBridgeReference
