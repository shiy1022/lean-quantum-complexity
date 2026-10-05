/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Mathlib

/-!
# Q02 — finite registers

A register is a finite nonempty basis type. An `n`-qubit register has basis `Qubits n = Fin n → Bool`,
definitionally the `ShiShallow.Bits n` of the BQP development. A zero-qubit register has exactly
one basis state (dimension one, never zero).

**Tensor-factor order.** The register `α × β` is "`α` then `β`": `α` is the left Kronecker factor,
matching `Matrix.kronecker`. Every other view of a composite register is reached through one of the
named equivalences below, never by notation:

* `regAssoc : (α × β) × γ ≃ α × (β × γ)`;
* `regSwap : α × β ≃ β × α`;
* `regUnitRight : α × Unit ≃ α`, `regUnitLeft : Unit × α ≃ α`;
* `qubitsAppend : Qubits m × Qubits n ≃ Qubits (m + n)`, with the first `m` wires on the left;
* `qubitsZero : Qubits 0 ≃ Unit`.
-/

namespace ShiQuantum

/-- The basis of an `n`-qubit register: one Boolean per wire. -/
abbrev Qubits (n : ℕ) := Fin n → Bool

theorem card_qubits (n : ℕ) : Fintype.card (Qubits n) = 2 ^ n := by simp

instance (n : ℕ) : Nonempty (Qubits n) := ⟨fun _ => false⟩

/-- The all-zero basis state. -/
def Qubits.zero (n : ℕ) : Qubits n := fun _ => false

/-- A zero-qubit register has a single basis state. -/
instance : Unique (Qubits 0) := Pi.uniqueOfIsEmpty _

theorem card_qubits_zero : Fintype.card (Qubits 0) = 1 := by simp

/-- A zero-qubit register is a one-dimensional register. -/
def qubitsZero : Qubits 0 ≃ Unit := Equiv.ofUnique _ _

/-! ## Named equivalences of composite registers -/

/-- Reassociate `(α ⊗ β) ⊗ γ` to `α ⊗ (β ⊗ γ)`. -/
def regAssoc (α β γ : Type*) : (α × β) × γ ≃ α × (β × γ) := Equiv.prodAssoc α β γ

/-- Exchange the two factors of `α ⊗ β`. -/
def regSwap (α β : Type*) : α × β ≃ β × α := Equiv.prodComm α β

/-- Remove a trivial register on the right. -/
def regUnitRight (α : Type*) : α × Unit ≃ α := Equiv.prodPUnit α

/-- Remove a trivial register on the left. -/
def regUnitLeft (α : Type*) : Unit × α ≃ α := Equiv.punitProd α

/-- Concatenate an `m`-qubit and an `n`-qubit register; the `m` wires come first. -/
def qubitsAppend (m n : ℕ) : Qubits m × Qubits n ≃ Qubits (m + n) := Fin.appendEquiv m n

@[simp] theorem regAssoc_apply {α β γ : Type*} (a : α) (b : β) (c : γ) :
    regAssoc α β γ ((a, b), c) = (a, (b, c)) := rfl

@[simp] theorem regSwap_apply {α β : Type*} (a : α) (b : β) : regSwap α β (a, b) = (b, a) := rfl

@[simp] theorem regUnitRight_apply {α : Type*} (a : α) (u : Unit) : regUnitRight α (a, u) = a :=
  rfl

@[simp] theorem regUnitLeft_apply {α : Type*} (a : α) (u : Unit) : regUnitLeft α (u, a) = a :=
  rfl

theorem qubitsAppend_apply_left {m n : ℕ} (a : Qubits m) (b : Qubits n) (i : Fin m) :
    qubitsAppend m n (a, b) (Fin.castAdd n i) = a i := Fin.append_left a b i

theorem qubitsAppend_apply_right {m n : ℕ} (a : Qubits m) (b : Qubits n) (j : Fin n) :
    qubitsAppend m n (a, b) (Fin.natAdd m j) = b j := Fin.append_right a b j

/-! ## The required exact identities -/

theorem regAssoc_symm_trans (α β γ : Type*) :
    (regAssoc α β γ).symm.trans (regAssoc α β γ) = Equiv.refl _ := Equiv.symm_trans_self _

theorem regAssoc_trans_symm (α β γ : Type*) :
    (regAssoc α β γ).trans (regAssoc α β γ).symm = Equiv.refl _ := Equiv.self_trans_symm _

/-- Swapping twice is the identity. -/
theorem regSwap_trans_regSwap (α β : Type*) :
    (regSwap α β).trans (regSwap β α) = Equiv.refl _ := by
  ext ⟨a, b⟩ <;> rfl

theorem regSwap_symm (α β : Type*) : (regSwap α β).symm = regSwap β α := rfl

/-- Adding a trivial register and removing it again is the identity, in both orders. -/
theorem regUnitRight_symm_trans (α : Type*) :
    (regUnitRight α).symm.trans (regUnitRight α) = Equiv.refl _ := Equiv.symm_trans_self _

theorem regUnitRight_trans_symm (α : Type*) :
    (regUnitRight α).trans (regUnitRight α).symm = Equiv.refl _ := Equiv.self_trans_symm _

/-- Appending a zero-qubit register on the right does not change the basis state. -/
theorem qubitsAppend_zero_right {n : ℕ} (a : Qubits n) (b : Qubits 0) :
    qubitsAppend n 0 (a, b) = a := by
  funext i
  exact Fin.append_left a b i

/-- Appending a zero-qubit register on the left does not change the basis state (up to the
cast `0 + n = n`, which is an equality of index types, not an identification of registers). -/
theorem qubitsAppend_zero_left {n : ℕ} (a : Qubits 0) (b : Qubits n) (i : Fin n) :
    qubitsAppend 0 n (a, b) (Fin.natAdd 0 i) = b i := Fin.append_right a b i

/-- Appending a zero-qubit register on the right agrees with removing a trivial register. -/
theorem qubitsAppend_zero_right_eq (n : ℕ) :
    qubitsAppend n 0 = ((Equiv.refl (Qubits n)).prodCongr qubitsZero).trans
      (regUnitRight (Qubits n)) := by
  ext ⟨a, b⟩ i
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    regUnitRight_apply]
  rw [qubitsAppend_zero_right]

/-- Qubit blocks are associative, up to the index cast `(l + m) + n = l + (m + n)`. -/
theorem qubitsAppend_assoc {l m n : ℕ} (a : Qubits l) (b : Qubits m) (c : Qubits n) :
    qubitsAppend (l + m) n (qubitsAppend l m (a, b), c) =
      qubitsAppend l (m + n) (a, qubitsAppend m n (b, c)) ∘ Fin.cast (Nat.add_assoc l m n) :=
  Fin.append_assoc a b c

end ShiQuantum
