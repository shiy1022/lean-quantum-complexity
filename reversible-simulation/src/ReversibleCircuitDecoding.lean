import ReversibleEstablishedBQP
import Mathlib.Tactic

set_option autoImplicit false
namespace ShiReversibleEncoding

/-- Parse a terminated unary natural, retaining the unconsumed suffix. -/
def readNat : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: xs => some (0, xs)
  | true :: xs => (readNat xs).map (fun p => (p.1 + 1, p.2))

@[simp] theorem readNat_encNat (n : Nat) (ys : List Bool) :
    readNat (ShiBQP.encNat n ++ ys) = some (n, ys) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (readNat (ShiBQP.encNat n ++ ys)).map (fun p => (p.1 + 1, p.2)) = some (n + 1, ys)
      rw [ih]
      rfl

def readWire (m : Nat) (xs : List Bool) : Option (Fin m × List Bool) := do
  let (n, ys) ← readNat xs
  if h : n < m then some (⟨n, h⟩, ys) else none

@[simp] theorem readWire_encNat {m : Nat} (i : Fin m) (ys : List Bool) :
    readWire m (ShiBQP.encNat i.val ++ ys) = some (i, ys) := by
  simp [readWire, i.isLt]

def readInstr (m : Nat) (xs : List Bool) : Option (ShiShallow.Instr m × List Bool) := do
  let (tag, ys) ← readNat xs
  let (i, zs) ← readWire m ys
  match tag with
  | 0 => some (.h i, zs)
  | 1 => some (.s i, zs)
  | 2 => some (.t i, zs)
  | 3 => some (.x i, zs)
  | 4 => do
      let (j, rest) ← readWire m zs
      if h : i ≠ j then some (.cnot i j h, rest) else none
  | _ => none

@[simp] theorem readInstr_encInstr {m : Nat} (g : ShiShallow.Instr m) (ys : List Bool) :
    readInstr m (ShiBQP.encInstr g ++ ys) = some (g, ys) := by
  cases g <;> simp [ShiBQP.encInstr, List.append_assoc, readInstr, *]

/-- Length-framed parsing is independent of element representation. -/
def readMany {A : Type} (parse : List Bool → Option (A × List Bool)) :
    Nat → List Bool → Option (List A × List Bool)
  | 0, xs => some ([], xs)
  | n + 1, xs => do
      let (a, ys) ← parse xs
      let (as, zs) ← readMany parse n ys
      some (a :: as, zs)

theorem readMany_encoded {A : Type} (encode : A → List Bool)
    (parse : List Bool → Option (A × List Bool))
    (hp : ∀ a ys, parse (encode a ++ ys) = some (a, ys)) (as : List A) (ys : List Bool) :
    readMany parse as.length ((as.map encode).flatten ++ ys) = some (as, ys) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [readMany, List.append_assoc, hp, ih]

def readList {A : Type} (parse : List Bool → Option (A × List Bool))
    (xs : List Bool) : Option (List A × List Bool) := do
  let (n, ys) ← readNat xs
  readMany parse n ys

theorem readList_encoded {A : Type} (encode : A → List Bool)
    (parse : List Bool → Option (A × List Bool))
    (hp : ∀ a ys, parse (encode a ++ ys) = some (a, ys)) (as : List A) (ys : List Bool) :
    readList parse (ShiBQP.encStr (as.map encode) ++ ys) = some (as, ys) := by
  simp [ShiBQP.encStr, List.append_assoc, readList, readMany_encoded encode parse hp]

def readLayer (m : Nat) := readList (readInstr m)
def readCirc (m : Nat) := readList (readLayer m)

@[simp] theorem readLayer_encLayer {m : Nat} (l : List (ShiShallow.Instr m)) (ys : List Bool) :
    readLayer m (ShiBQP.encLayer l ++ ys) = some (l, ys) :=
  readList_encoded ShiBQP.encInstr (readInstr m) readInstr_encInstr l ys

@[simp] theorem readCirc_encCirc {m : Nat} (c : ShiShallow.Layered m) (ys : List Bool) :
    readCirc m (ShiBQP.encCirc c ++ ys) = some (c, ys) :=
  readList_encoded ShiBQP.encLayer (readLayer m) readLayer_encLayer c ys

/-- Serialization loses neither gates nor layer boundaries. -/
theorem encCirc_injective (m : Nat) : Function.Injective (@ShiBQP.encCirc m) := by
  intro c d h
  have e := congrArg (fun xs => readCirc m (xs ++ [])) h
  simpa only [readCirc_encCirc, Option.some.injEq, Prod.mk.injEq, and_true] using e

end ShiReversibleEncoding
