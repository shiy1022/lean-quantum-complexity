/-
BRIDGE-SIMc.  THE SEMANTIC CORRECTNESS OF THE ROUTE-(A) COMPILER'S GATE BLOCKS, AND OF
ITS ADJOINT PASS -- the obligation BRIDGE-C2c left as a HAND CHECK (gotcha 276).

BRIDGE-C2c exhibits the compiler and proves STRUCTURAL facts about it: the doubled
witness budget, head safety, the opcode range, the input prefix.  It proves nothing about
what the emitted blocks MEAN.  BRIDGE-SIMb proved what each block does to the TAPE.  This
file closes the remaining link: that the tape operation each block performs is exactly the
basis-string action of the corresponding `ShiShallow.Instr`, that PATH-1b's backward
permutation `perm` inverts it, that the block's phase increment is exactly the gate's
coefficient as a power of `ω = exp (i π / 4)`, and that the ADJOINT block undoes the
forward one with a cancelling phase.

`fwd m g a z` is the forward basis-string action of the block for `g` (the Bool `a` is the
witness bit, read only by the Hadamard); `pha` and `padj` are the phase increments of the
forward and adjoint blocks.  The CNOT clause is the one that was only hand-checked: it
needs `i ≠ j` in an essential way, since `cnotState i i` is not a permutation at all.

Also here: the `List.ofFn` dictionary translating a basis string `Bits m` to the
compiler's tape, and the closed forms of the compiler's forward and reversed gate sweeps
as flattened lists of blocks.
-/
import Definitions.Def_ShiShallow_Core

namespace BQPBridgeReference

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiShallow

theorem gateData :
    ∃ (fwd : ∀ m : ℕ, Instr m → Bool → Bits m → Bits m)
      (pha padj : ∀ m : ℕ, Instr m → Bool → Bits m → ZMod 8),
      -- the forward basis-string action of each emitted block
      (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          fwd m (Instr.h i) a z = Function.update z i a)
      ∧ (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m), fwd m (Instr.s i) a z = z)
      ∧ (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m), fwd m (Instr.t i) a z = z)
      ∧ (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          fwd m (Instr.x i) a z = Function.update z i (!(z i)))
      ∧ (∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j) (a : Bool) (z : Bits m),
          fwd m (Instr.cnot i j hij) a z = Function.update z j (xor (z j) (z i)))
      -- the phase increment of the forward block
      ∧ (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          pha m (Instr.h i) a z = (if z i && a then 4 else 0))
      ∧ (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          pha m (Instr.s i) a z = (if z i then 2 else 0))
      ∧ (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          pha m (Instr.t i) a z = (if z i then 1 else 0))
      ∧ (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m), pha m (Instr.x i) a z = 0)
      ∧ (∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j) (a : Bool) (z : Bits m),
          pha m (Instr.cnot i j hij) a z = 0)
      -- the phase increment of the ADJOINT block: `T` becomes seven 3s, `S` three 4s
      ∧ (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          padj m (Instr.h i) a z = (if z i && a then 4 else 0))
      ∧ (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          padj m (Instr.s i) a z = (if z i then 6 else 0))
      ∧ (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          padj m (Instr.t i) a z = (if z i then 7 else 0))
      ∧ (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m), padj m (Instr.x i) a z = 0)
      ∧ (∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j) (a : Bool) (z : Bits m),
          padj m (Instr.cnot i j hij) a z = 0)
      -- (A) PATH-1b's backward permutation INVERTS the forward block, gate by gate
      ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
          (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
              Instr.apply g ψ z = coef g z * ψ (perm g z)) →
          ∀ (g : Instr m), (∀ i, g ≠ Instr.h i) → ∀ (a : Bool) (z : Bits m),
            perm g (fwd m g a z) = z)
      -- (B) and the gate's coefficient there is exactly the block's phase increment
      ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
          (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
              Instr.apply g ψ z = coef g z * ψ (perm g z)) →
          ∀ (g : Instr m), (∀ i, g ≠ Instr.h i) → ∀ (a : Bool) (z : Bits m),
            coef g (fwd m g a z)
              = Complex.exp (Complex.I * Real.pi / 4) ^ (pha m g a z).val)
      -- (C) the Hadamard matrix entry, in the same normal form
      ∧ (∀ a b : Bool, hMat a b
            = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
                * Complex.exp (Complex.I * Real.pi / 4) ^ (if a && b then 4 else 0))
      -- (D) THE ADJOINT PASS: every non-Hadamard block is undone by its adjoint, whose
      -- phase increment cancels the forward one mod 8
      ∧ (∀ (m : ℕ) (g : Instr m), (∀ i, g ≠ Instr.h i) → ∀ (a : Bool) (z : Bits m),
          fwd m g a (fwd m g a z) = z)
      ∧ (∀ (m : ℕ) (g : Instr m), (∀ i, g ≠ Instr.h i) → ∀ (a : Bool) (z : Bits m),
          pha m g a z + padj m g a (fwd m g a z) = 0)
      -- (E) the Hadamard block destroys exactly one bit, and it is the recorded one
      ∧ (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m), fwd m (Instr.h i) a z i = a)
      ∧ (∀ (m : ℕ) (i : Fin m) (a : Bool) (z : Bits m),
          Function.update (fwd m (Instr.h i) a z) i (z i) = z)
      ∧ (∀ (m : ℕ) (i : Fin m) (a b : Bool) (z : Bits m),
          fwd m (Instr.h i) b (fwd m (Instr.h i) a z) = fwd m (Instr.h i) b z)
      -- (F) THE TAPE DICTIONARY
      ∧ (∀ (m : ℕ) (z : Bits m), (List.ofFn z).length = m)
      ∧ (∀ (m : ℕ) (z : Bits m) (i : Fin m), ((List.ofFn z).drop (i : ℕ)).headI = z i)
      ∧ (∀ (m : ℕ) (z : Bits m) (i : Fin m) (b : Bool),
          (List.ofFn z).set (i : ℕ) b = List.ofFn (Function.update z i b))
      -- (G) the compiler's forward and reversed gate sweeps, as flattened block lists
      ∧ (∀ (D : ∀ m : ℕ, List (Instr m) → List ℕ) (B : ∀ m : ℕ, Instr m → List ℕ),
          (∀ m : ℕ, D m [] = []) →
          (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)),
              D m (g :: gs) = B m g ++ D m gs) →
          ∀ (m : ℕ) (gs : List (Instr m)), D m gs = (gs.map (B m)).flatten)
      ∧ (∀ (DA : ∀ m : ℕ, List (Instr m) → List ℕ) (BA : ∀ m : ℕ, Instr m → List ℕ),
          (∀ m : ℕ, DA m [] = []) →
          (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)),
              DA m (g :: gs) = DA m gs ++ BA m g) →
          ∀ (m : ℕ) (gs : List (Instr m)),
            DA m gs = ((gs.reverse).map (BA m)).flatten) := by
  classical
  -- `ω = exp (i π / 4)`
  have hw2 : (Complex.exp (Complex.I * Real.pi / 4)) ^ 2 = Complex.I := by
    have h : (Complex.exp (Complex.I * Real.pi / 4)) ^ 2
        = Complex.exp (Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4) := by
      rw [Complex.exp_add]; ring
    have h2 : Complex.I * (Real.pi : ℂ) / 4 + Complex.I * (Real.pi : ℂ) / 4
        = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, h2, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  have hw4 : (Complex.exp (Complex.I * Real.pi / 4)) ^ 4 = -1 := by
    have h : (Complex.exp (Complex.I * Real.pi / 4)) ^ 4
        = ((Complex.exp (Complex.I * Real.pi / 4)) ^ 2) ^ 2 := by ring
    rw [h, hw2, Complex.I_sq]
  -- the two-term expansion of the one-wire sum (BRANCH-1b)
  have expand : ∀ (m : ℕ) (U : Matrix Bool Bool ℂ) (i : Fin m) (ψ : QState m) (x : Bits m),
      apply1 U i ψ x = U (x i) true * ψ (Function.update x i true)
        + U (x i) false * ψ (Function.update x i false) := by
    intro m U i ψ x
    unfold apply1
    exact Fintype.sum_bool fun b => U (x i) b * ψ (Function.update x i b)
  have diag : ∀ (m : ℕ) (U : Matrix Bool Bool ℂ) (i : Fin m) (ψ : QState m),
      (∀ a b : Bool, a ≠ b → U a b = 0) →
      apply1 U i ψ = fun x => U (x i) (x i) * ψ x := by
    intro m U i ψ hU
    funext x
    rw [expand m U i ψ x]
    rcases Bool.eq_false_or_eq_true (x i) with hx | hx
    · have hu : Function.update x i true = x := Function.update_eq_self_iff.2 hx.symm
      rw [hx, hU true false (by decide), hu]; ring
    · have hu : Function.update x i false = x := Function.update_eq_self_iff.2 hx.symm
      rw [hx, hU false true (by decide), hu]; ring
  have anti : ∀ (m : ℕ) (U : Matrix Bool Bool ℂ) (i : Fin m) (ψ : QState m),
      (∀ a : Bool, U a a = 0) →
      apply1 U i ψ = fun x => U (x i) (!(x i)) * ψ (Function.update x i (!(x i))) := by
    intro m U i ψ hU
    funext x
    rw [expand m U i ψ x]
    rcases Bool.eq_false_or_eq_true (x i) with hx | hx
    · rw [hx, hU true]; simp
    · rw [hx, hU false]; simp
  have sEq : ∀ (m : ℕ) (i : Fin m) (ψ : QState m) (z : Bits m),
      Instr.apply (Instr.s i) ψ z = (if z i then Complex.I else 1) * ψ z := by
    intro m i ψ z
    have hs : Instr.apply (Instr.s i) ψ = apply1 sMat i ψ := rfl
    have hoff : ∀ a b : Bool, a ≠ b → sMat a b = 0 := by
      intro a b hab; simp [sMat, hab]
    rw [hs, diag m sMat i ψ hoff]
    simp [sMat]
  have tEq : ∀ (m : ℕ) (i : Fin m) (ψ : QState m) (z : Bits m),
      Instr.apply (Instr.t i) ψ z
        = (if z i then Complex.exp (Complex.I * Real.pi / 4) else 1) * ψ z := by
    intro m i ψ z
    have ht : Instr.apply (Instr.t i) ψ = apply1 tMat i ψ := rfl
    have hoff : ∀ a b : Bool, a ≠ b → tMat a b = 0 := by
      intro a b hab; simp [tMat, hab]
    rw [ht, diag m tMat i ψ hoff]
    simp [tMat]
  have xEq : ∀ (m : ℕ) (i : Fin m) (ψ : QState m) (z : Bits m),
      Instr.apply (Instr.x i) ψ z = 1 * ψ (Function.update z i (!(z i))) := by
    intro m i ψ z
    have hx : Instr.apply (Instr.x i) ψ = apply1 xMat i ψ := rfl
    have hoff : ∀ a : Bool, xMat a a = 0 := by intro a; simp [xMat]
    rw [hx, anti m xMat i ψ hoff]
    cases h : z i <;> simp [xMat, h]
  have cEq : ∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j) (ψ : QState m) (z : Bits m),
      Instr.apply (Instr.cnot i j hij) ψ z
        = 1 * ψ (Function.update z j (xor (z j) (z i))) := by
    intro m i j hij ψ z
    show cnotState i j hij ψ z = 1 * ψ (Function.update z j (xor (z j) (z i)))
    rw [one_mul]
    rfl
  -- a weighted permutation determines its permutation and its weight
  have key : ∀ (m : ℕ) (c c0 : ℂ) (p q : Bits m), c0 ≠ 0 →
      (∀ ψ : QState m, c * ψ p = c0 * ψ q) → p = q ∧ c = c0 := by
    intro m c c0 p q hc0 h
    have hpq : p = q := by
      by_contra hne
      have h1 : c * (if p = q then (1 : ℂ) else 0)
          = c0 * (if q = q then (1 : ℂ) else 0) := h (fun y => if y = q then (1 : ℂ) else 0)
      rw [if_neg hne, if_pos rfl, mul_zero, mul_one] at h1
      exact hc0 h1.symm
    subst hpq
    refine ⟨rfl, ?_⟩
    have h2 : c * (if p = p then (1 : ℂ) else 0) = c0 * (if p = p then (1 : ℂ) else 0) :=
      h (fun y => if y = p then (1 : ℂ) else 0)
    rw [if_pos rfl, mul_one, mul_one] at h2
    exact h2
  have hIne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hone : (1 : ℂ) ≠ 0 := one_ne_zero
  have hwne : Complex.exp (Complex.I * Real.pi / 4) ≠ 0 := Complex.exp_ne_zero _
  -- the four non-Hadamard gates, pinned
  have hgates : ∀ (m : ℕ) (coef : Instr m → Bits m → ℂ)
      (perm : Instr m → Bits m → Bits m),
      (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (z : Bits m),
          Instr.apply g ψ z = coef g z * ψ (perm g z)) →
      (∀ (i : Fin m) (z : Bits m), perm (Instr.s i) z = z
          ∧ coef (Instr.s i) z = (if z i then Complex.I else 1))
      ∧ (∀ (i : Fin m) (z : Bits m), perm (Instr.t i) z = z
          ∧ coef (Instr.t i) z
              = (if z i then Complex.exp (Complex.I * Real.pi / 4) else 1))
      ∧ (∀ (i : Fin m) (z : Bits m), perm (Instr.x i) z = Function.update z i (!(z i))
          ∧ coef (Instr.x i) z = 1)
      ∧ (∀ (i j : Fin m) (hij : i ≠ j) (z : Bits m),
          perm (Instr.cnot i j hij) z = Function.update z j (xor (z j) (z i))
          ∧ coef (Instr.cnot i j hij) z = 1) := by
    intro m coef perm hNH
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i z
      have hne : (if z i then Complex.I else 1) ≠ 0 := by
        cases h : z i <;> simp [h, hIne]
      have hk := key m (coef (Instr.s i) z) (if z i then Complex.I else 1)
        (perm (Instr.s i) z) z hne
        (fun ψ => by rw [← hNH (Instr.s i) (by intro i' hcon; cases hcon) ψ z,
          sEq m i ψ z])
      exact ⟨hk.1, hk.2⟩
    · intro i z
      have hne : (if z i then Complex.exp (Complex.I * Real.pi / 4) else 1) ≠ 0 := by
        cases h : z i <;> simp [h, hwne]
      have hk := key m (coef (Instr.t i) z)
        (if z i then Complex.exp (Complex.I * Real.pi / 4) else 1)
        (perm (Instr.t i) z) z hne
        (fun ψ => by rw [← hNH (Instr.t i) (by intro i' hcon; cases hcon) ψ z,
          tEq m i ψ z])
      exact ⟨hk.1, hk.2⟩
    · intro i z
      have hk := key m (coef (Instr.x i) z) 1
        (perm (Instr.x i) z) (Function.update z i (!(z i))) hone
        (fun ψ => by rw [← hNH (Instr.x i) (by intro i' hcon; cases hcon) ψ z,
          xEq m i ψ z])
      exact ⟨hk.1, hk.2⟩
    · intro i j hij z
      have hk2 := key m (coef (Instr.cnot i j hij) z) 1
        (perm (Instr.cnot i j hij) z) (Function.update z j (xor (z j) (z i))) hone
        (fun ψ => by
          rw [← hNH (Instr.cnot i j hij) (by intro i' hcon; cases hcon) ψ z,
            cEq m i j hij ψ z])
      exact ⟨hk2.1, hk2.2⟩
  -- Boolean algebra
  have hxx : ∀ a b : Bool, xor (xor a b) b = a := by decide
  -- the CNOT block is a permutation, and its own inverse -- gotcha 276
  have hcnotInv : ∀ (m : ℕ) (i j : Fin m), i ≠ j → ∀ z : Bits m,
      Function.update (Function.update z j (xor (z j) (z i))) j
          (xor ((Function.update z j (xor (z j) (z i))) j)
               ((Function.update z j (xor (z j) (z i))) i)) = z := by
    intro m i j hij z
    have hi : (Function.update z j (xor (z j) (z i))) i = z i := by
      simp [Function.update_apply, hij]
    have hj : (Function.update z j (xor (z j) (z i))) j = xor (z j) (z i) := by
      simp
    rw [hi, hj, hxx (z j) (z i)]
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Function.update_apply, hk]
  have hxInv : ∀ (m : ℕ) (i : Fin m) (z : Bits m),
      Function.update (Function.update z i (!(z i))) i
          (!((Function.update z i (!(z i))) i)) = z := by
    intro m i z
    have hi : (Function.update z i (!(z i))) i = !(z i) := by simp
    rw [hi, Bool.not_not]
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_apply, hk]
  -- the tape dictionary
  have hdh : ∀ (i : ℕ) (l : List Bool) (h : i < l.length), (l.drop i).headI = l[i] := by
    intro i
    induction i with
    | zero =>
      intro l h
      cases l with
      | nil => simp at h
      | cons a s => simp
    | succ i ih =>
      intro l h
      cases l with
      | nil => simp at h
      | cons a s =>
        have hs : i < s.length := by simpa using h
        simpa using ih s hs
  have hcell : ∀ (m : ℕ) (z : Bits m) (i : Fin m),
      ((List.ofFn z).drop (i : ℕ)).headI = z i := by
    intro m z i
    have h : (i : ℕ) < (List.ofFn z).length := by simp
    rw [hdh (i : ℕ) (List.ofFn z) h]
    simp
  have hset : ∀ (m : ℕ) (z : Bits m) (i : Fin m) (b : Bool),
      (List.ofFn z).set (i : ℕ) b = List.ofFn (Function.update z i b) := by
    intro m z i b
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      have hk : k < m := by simpa using h2
      rw [List.getElem_set]
      by_cases hik : (i : ℕ) = k
      · rw [if_pos hik]
        have hfi : (⟨k, hk⟩ : Fin m) = i := by
          apply Fin.ext; exact hik.symm
        simp [List.getElem_ofFn, Function.update_apply, hfi]
      · rw [if_neg hik]
        have hfi : (⟨k, hk⟩ : Fin m) ≠ i := by
          intro hc
          apply hik
          rw [← hc]
        simp [List.getElem_ofFn, Function.update_apply, hfi]
  -- the two gate sweeps
  have hD : ∀ (D : ∀ m : ℕ, List (Instr m) → List ℕ) (B : ∀ m : ℕ, Instr m → List ℕ),
      (∀ m : ℕ, D m [] = []) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)), D m (g :: gs) = B m g ++ D m gs) →
      ∀ (m : ℕ) (gs : List (Instr m)), D m gs = (gs.map (B m)).flatten := by
    intro D B h0 hc m gs
    induction gs with
    | nil => simpa using h0 m
    | cons g gs ih => rw [hc m g gs, ih]; simp
  have hDA : ∀ (DA : ∀ m : ℕ, List (Instr m) → List ℕ) (BA : ∀ m : ℕ, Instr m → List ℕ),
      (∀ m : ℕ, DA m [] = []) →
      (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)),
          DA m (g :: gs) = DA m gs ++ BA m g) →
      ∀ (m : ℕ) (gs : List (Instr m)),
        DA m gs = ((gs.reverse).map (BA m)).flatten := by
    intro DA BA h0 hc m gs
    induction gs with
    | nil => simpa using h0 m
    | cons g gs ih => rw [hc m g gs, ih]; simp
  refine ⟨fun m g a z =>
      match g with
      | Instr.h i => Function.update z i a
      | Instr.s _ => z
      | Instr.t _ => z
      | Instr.x i => Function.update z i (!(z i))
      | Instr.cnot i j _ => Function.update z j (xor (z j) (z i)),
    fun m g a z =>
      match g with
      | Instr.h i => (if z i && a then 4 else 0)
      | Instr.s i => (if z i then 2 else 0)
      | Instr.t i => (if z i then 1 else 0)
      | Instr.x _ => 0
      | Instr.cnot _ _ _ => 0,
    fun m g a z =>
      match g with
      | Instr.h i => (if z i && a then 4 else 0)
      | Instr.s i => (if z i then 6 else 0)
      | Instr.t i => (if z i then 7 else 0)
      | Instr.x _ => 0
      | Instr.cnot _ _ _ => 0,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (fun m z => by simp), hcell, hset, hD, hDA⟩
  -- (A) `perm` inverts the forward block
  · intro m coef perm hNH g hg a z
    obtain ⟨hs, ht, hx, hc⟩ := hgates m coef perm hNH
    cases g with
    | h i => exact absurd rfl (hg i)
    | s i => exact (hs i z).1
    | t i => exact (ht i z).1
    | x i =>
      show perm (Instr.x i) (Function.update z i (!(z i))) = z
      rw [(hx i (Function.update z i (!(z i)))).1]
      exact hxInv m i z
    | cnot i j hij =>
      show perm (Instr.cnot i j hij) (Function.update z j (xor (z j) (z i))) = z
      rw [(hc i j hij (Function.update z j (xor (z j) (z i)))).1]
      exact hcnotInv m i j hij z
  -- (B) the coefficient is the phase increment
  · intro m coef perm hNH g hg a z
    obtain ⟨hs, ht, hx, hc⟩ := hgates m coef perm hNH
    cases g with
    | h i => exact absurd rfl (hg i)
    | s i =>
      show coef (Instr.s i) z
          = Complex.exp (Complex.I * Real.pi / 4) ^ ((if z i then (2 : ZMod 8) else 0)).val
      rw [(hs i z).2]
      cases h : z i
      · show (1 : ℂ) = Complex.exp (Complex.I * Real.pi / 4) ^ ((0 : ZMod 8)).val
        rw [show ((0 : ZMod 8)).val = 0 from by decide, pow_zero]
      · show (Complex.I : ℂ)
            = Complex.exp (Complex.I * Real.pi / 4) ^ ((2 : ZMod 8)).val
        rw [show ((2 : ZMod 8)).val = 2 from by decide]
        exact hw2.symm
    | t i =>
      show coef (Instr.t i) z
          = Complex.exp (Complex.I * Real.pi / 4) ^ ((if z i then (1 : ZMod 8) else 0)).val
      rw [(ht i z).2]
      cases h : z i
      · show (1 : ℂ) = Complex.exp (Complex.I * Real.pi / 4) ^ ((0 : ZMod 8)).val
        rw [show ((0 : ZMod 8)).val = 0 from by decide, pow_zero]
      · show Complex.exp (Complex.I * Real.pi / 4)
            = Complex.exp (Complex.I * Real.pi / 4) ^ ((1 : ZMod 8)).val
        rw [show ((1 : ZMod 8)).val = 1 from by decide, pow_one]
    | x i =>
      show coef (Instr.x i) (Function.update z i (!(z i)))
          = Complex.exp (Complex.I * Real.pi / 4) ^ ((0 : ZMod 8)).val
      rw [(hx i (Function.update z i (!(z i)))).2]
      rw [show ((0 : ZMod 8)).val = 0 from by decide, pow_zero]
    | cnot i j hij =>
      show coef (Instr.cnot i j hij) (Function.update z j (xor (z j) (z i)))
          = Complex.exp (Complex.I * Real.pi / 4) ^ ((0 : ZMod 8)).val
      rw [(hc i j hij (Function.update z j (xor (z j) (z i)))).2]
      rw [show ((0 : ZMod 8)).val = 0 from by decide, pow_zero]
  -- (C) the Hadamard matrix entry
  · intro a b
    cases a <;> cases b <;> simp [hMat, hw4]
  -- (D1) the adjoint undoes the forward block
  · intro m g hg a z
    cases g with
    | h i => exact absurd rfl (hg i)
    | s i => rfl
    | t i => rfl
    | x i => exact hxInv m i z
    | cnot i j hij => exact hcnotInv m i j hij z
  -- (D2) the phases cancel
  · intro m g hg a z
    cases g with
    | h i => exact absurd rfl (hg i)
    | s i =>
      show (if z i then (2 : ZMod 8) else 0) + (if z i then (6 : ZMod 8) else 0) = 0
      cases h : z i
      · decide
      · decide
    | t i =>
      show (if z i then (1 : ZMod 8) else 0) + (if z i then (7 : ZMod 8) else 0) = 0
      cases h : z i
      · decide
      · decide
    | x i => show (0 : ZMod 8) + 0 = 0
             decide
    | cnot i j hij =>
      show (0 : ZMod 8) + 0 = 0
      decide
  -- (E1) the Hadamard writes the witness bit
  · intro m i a z
    show (Function.update z i a) i = a
    simp
  -- (E2) and the destroyed value is recoverable
  · intro m i a z
    show Function.update (Function.update z i a) i (z i) = z
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_apply, hk]
  -- (E3) a second Hadamard write on the same wire overwrites the first
  · intro m i a b z
    show Function.update (Function.update z i a) i b = Function.update z i b
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_apply, hk]

end BQPBridgeReference
