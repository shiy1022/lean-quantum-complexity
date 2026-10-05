/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Encoding

/-!
# Q14 — the strict decoder

Each parser has type `Str → Option (α × Str)` and returns the unread suffix. The parsers are
proved

* **complete**: `parse (enc a ++ r) = some (a, r)` for every suffix `r`;
* **sound**: `parse s = some (a, r)` only when `s = enc a ++ r`.

`decode` additionally rejects trailing input. Consequently `decode s = some d ↔ s = encode d`
(`decode_eq_some_iff`): the only accepted strings are encodings, and the encoding is injective.
Malformed inputs — the empty string, truncated unary numerals, unknown gate tags, trailing bits
and every proper prefix of an encoding — are rejected (`none`). The decoder does not check
wire ranges or ownership; `decodeChecked` additionally runs `Desc.check`.
-/

namespace ShiQIP

/-! ## Parsers -/

def decNat : Str → Option (ℕ × Str)
  | [] => none
  | false :: r => some (0, r)
  | true :: r => (decNat r).map fun p => (p.1 + 1, p.2)

def decDir : Str → Option (Dir × Str)
  | [] => none
  | true :: r => some (.toVerifier, r)
  | false :: r => some (.toProver, r)

def decMsg (s : Str) : Option (Message × Str) :=
  (decDir s).bind fun p => (decNat p.2).map fun q => (⟨p.1, q.1⟩, q.2)

/-- The arguments of a gate with unary tag `tag`. Tags above `4` are rejected. -/
def decGateArgs : ℕ → Str → Option (Gate × Str)
  | 0, r => (decNat r).map fun p => (.h p.1, p.2)
  | 1, r => (decNat r).map fun p => (.s p.1, p.2)
  | 2, r => (decNat r).map fun p => (.t p.1, p.2)
  | 3, r => (decNat r).map fun p => (.x p.1, p.2)
  | 4, r => (decNat r).bind fun p => (decNat p.2).map fun q => (.cnot p.1 q.1, q.2)
  | _ + 5, _ => none

def decGate (s : Str) : Option (Gate × Str) := (decNat s).bind fun p => decGateArgs p.1 p.2

/-- Exactly `n` items. -/
def decMany {α : Type*} (p : Str → Option (α × Str)) : ℕ → Str → Option (List α × Str)
  | 0, s => some ([], s)
  | n + 1, s => (p s).bind fun q => (decMany p n q.2).map fun t => (q.1 :: t.1, t.2)

/-- A length, then that many items. -/
def decList {α : Type*} (p : Str → Option (α × Str)) (s : Str) : Option (List α × Str) :=
  (decNat s).bind fun q => decMany p q.1 q.2

def decBlock (s : Str) : Option (List Gate × Str) := decList decGate s

def decDesc (s : Str) : Option (Desc × Str) :=
  (decNat s).bind fun a => (decNat a.2).bind fun b => (decList decMsg b.2).bind fun c =>
    (decList decBlock c.2).map fun e => (⟨a.1, b.1, c.1, e.1⟩, e.2)

/-- The strict decoder: the whole input must be consumed. -/
def decode (s : Str) : Option Desc :=
  match decDesc s with
  | some (d, []) => some d
  | _ => none

/-- Decode, then require a well-formed description. -/
def decodeChecked (s : Str) : Option Desc := (decode s).filter Desc.check

/-! ## Completeness: parsers read their encodings and keep any suffix -/

theorem decNat_replicate (k : ℕ) (r : Str) :
    decNat (List.replicate k true ++ false :: r) = some (k, r) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, decNat, ih]

theorem decNat_encNat (k : ℕ) (r : Str) : decNat (encNat k ++ r) = some (k, r) := by
  simpa [encNat] using decNat_replicate k r

theorem decMsg_encMsg (m : Message) (r : Str) : decMsg (encMsg m ++ r) = some (m, r) := by
  rcases m with ⟨dir, w⟩
  cases dir <;> simp [decMsg, encMsg, encDir, decDir, decNat_encNat]

theorem decGate_encGate (g : Gate) (r : Str) : decGate (encGate g ++ r) = some (g, r) := by
  cases g <;> simp [decGate, encGate, List.append_assoc, decNat_encNat, decGateArgs]

theorem decMany_enc {α : Type*} {f : α → Str} {p : Str → Option (α × Str)}
    (hp : ∀ a r, p (f a ++ r) = some (a, r)) (l : List α) (r : Str) :
    decMany p l.length ((l.map f).flatten ++ r) = some (l, r) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [decMany, List.append_assoc, hp, ih]

theorem decList_encList {α : Type*} {f : α → Str} {p : Str → Option (α × Str)}
    (hp : ∀ a r, p (f a ++ r) = some (a, r)) (l : List α) (r : Str) :
    decList p (encList f l ++ r) = some (l, r) := by
  simp [decList, encList, List.append_assoc, decNat_encNat, decMany_enc hp]

theorem decBlock_encBlock (b : List Gate) (r : Str) :
    decBlock (encBlock b ++ r) = some (b, r) :=
  decList_encList decGate_encGate b r

theorem decDesc_encode (d : Desc) (r : Str) : decDesc (encode d ++ r) = some (d, r) := by
  simp [decDesc, encode, List.append_assoc, decNat_encNat, decList_encList decMsg_encMsg,
    decList_encList decBlock_encBlock]

/-- **Round trip.** -/
theorem decode_encode (d : Desc) : decode (encode d) = some d := by
  have := decDesc_encode d []
  rw [List.append_nil] at this
  simp [decode, this]

theorem encode_injective : Function.Injective encode := by
  intro d d' h
  have := decode_encode d
  rw [h, decode_encode] at this
  exact (Option.some.inj this).symm

theorem decodeChecked_encode {d : Desc} (h : d.Valid) : decodeChecked (encode d) = some d := by
  simp only [decodeChecked, decode_encode, Option.filter_some]
  rw [if_pos (show d.check = true from h)]

/-! ## Soundness: parsers accept only encodings -/

theorem decNat_sound : ∀ {s : Str} {k : ℕ} {r : Str}, decNat s = some (k, r) →
    s = encNat k ++ r
  | [], _, _, h => by simp [decNat] at h
  | false :: s, k, r, h => by
    simp only [decNat, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | true :: s, k, r, h => by
    simp only [decNat, Option.map_eq_some_iff] at h
    obtain ⟨⟨k', r'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rw [decNat_sound h1]
    simp [encNat, List.replicate_succ]

theorem decDir_sound {s : Str} {d : Dir} {r : Str} (h : decDir s = some (d, r)) :
    s = encDir d ++ r := by
  match s, h with
  | true :: s, h => simp only [decDir, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h; rfl
  | false :: s, h => simp only [decDir, Option.some.injEq, Prod.mk.injEq] at h
                     obtain ⟨rfl, rfl⟩ := h; rfl

theorem decMsg_sound {s : Str} {m : Message} {r : Str} (h : decMsg s = some (m, r)) :
    s = encMsg m ++ r := by
  simp only [decMsg, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨d, r1⟩, h1, ⟨w, r2⟩, h2, h3⟩ := h
  simp only [Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  dsimp only at h2
  rw [decDir_sound h1, decNat_sound h2]
  simp [encMsg]

theorem decGate_sound {s : Str} {g : Gate} {r : Str} (h : decGate s = some (g, r)) :
    s = encGate g ++ r := by
  simp only [decGate, Option.bind_eq_some_iff] at h
  obtain ⟨⟨tag, r1⟩, h1, h2⟩ := h
  rw [decNat_sound h1]
  match tag, h2 with
  | 0, h2 | 1, h2 | 2, h2 | 3, h2 =>
    simp only [decGateArgs, Option.map_eq_some_iff] at h2
    obtain ⟨⟨i, r2⟩, h3, h4⟩ := h2
    simp only [Prod.mk.injEq] at h4
    obtain ⟨rfl, rfl⟩ := h4
    rw [decNat_sound h3]
    simp [encGate]
  | 4, h2 =>
    simp only [decGateArgs, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h2
    obtain ⟨⟨i, r2⟩, h3, ⟨j, r3⟩, h4, h5⟩ := h2
    simp only [Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    dsimp only at h4
    rw [decNat_sound h3, decNat_sound h4]
    simp [encGate]
  | _ + 5, h2 => simp [decGateArgs] at h2

theorem decMany_sound {α : Type*} {f : α → Str} {p : Str → Option (α × Str)}
    (hp : ∀ {s a r}, p s = some (a, r) → s = f a ++ r) :
    ∀ (n : ℕ) {s : Str} {l : List α} {r : Str}, decMany p n s = some (l, r) →
      l.length = n ∧ s = (l.map f).flatten ++ r
  | 0, s, l, r, h => by
    simp only [decMany, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | n + 1, s, l, r, h => by
    simp only [decMany, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨a, r1⟩, h1, ⟨l', r2⟩, h2, h3⟩ := h
    simp only [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    dsimp only at h2
    obtain ⟨hl, hs⟩ := decMany_sound hp n h2
    refine ⟨by simp [hl], ?_⟩
    rw [hp h1, hs]
    simp

theorem decList_sound {α : Type*} {f : α → Str} {p : Str → Option (α × Str)}
    (hp : ∀ {s a r}, p s = some (a, r) → s = f a ++ r) {s : Str} {l : List α} {r : Str}
    (h : decList p s = some (l, r)) : s = encList f l ++ r := by
  simp only [decList, Option.bind_eq_some_iff] at h
  obtain ⟨⟨n, r1⟩, h1, h2⟩ := h
  dsimp only at h2
  obtain ⟨hl, hs⟩ := decMany_sound hp n h2
  rw [decNat_sound h1, hs, ← hl]
  simp [encList]

theorem decBlock_sound {s : Str} {b : List Gate} {r : Str} (h : decBlock s = some (b, r)) :
    s = encBlock b ++ r :=
  decList_sound decGate_sound h

theorem decDesc_sound {s : Str} {d : Desc} {r : Str} (h : decDesc s = some (d, r)) :
    s = encode d ++ r := by
  simp only [decDesc, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨p, r1⟩, h1, ⟨o, r2⟩, h2, ⟨ms, r3⟩, h3, ⟨bs, r4⟩, h4, h5⟩ := h
  simp only [Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  dsimp only at h2 h3 h4
  rw [decNat_sound h1, decNat_sound h2, decList_sound decMsg_sound h3,
    decList_sound decBlock_sound h4]
  simp [encode]

/-- **The decoder accepts exactly the encodings.** -/
theorem decode_eq_some_iff {s : Str} {d : Desc} : decode s = some d ↔ s = encode d := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · rename_i d' heq
      simp only [Option.some.injEq] at h
      subst h
      simpa using decDesc_sound heq
    · simp at h
  · rintro rfl
    exact decode_encode d

theorem decodeChecked_eq_some_iff {s : Str} {d : Desc} :
    decodeChecked s = some d ↔ s = encode d ∧ d.Valid := by
  simp [decodeChecked, Option.filter_eq_some_iff, decode_eq_some_iff, Desc.Valid]

/-! ## Malformed inputs -/

theorem decode_nil : decode [] = none := rfl

/-- A truncated unary numeral (no terminating `false`) is rejected. -/
theorem decNat_replicate_true (n : ℕ) : decNat (List.replicate n true) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, decNat, ih]

/-- Gate tags above `4` are rejected. -/
theorem decGate_bad_tag (k : ℕ) (r : Str) : decGate (encNat (k + 5) ++ r) = none := by
  simp [decGate, decNat_encNat, decGateArgs]

/-- Trailing bits after an encoding are rejected. -/
theorem decode_encode_append {d : Desc} {t : Str} (ht : t ≠ []) : decode (encode d ++ t) = none := by
  unfold decode
  rw [decDesc_encode]
  cases t with
  | nil => exact absurd rfl ht
  | cons _ _ => rfl

/-- Every proper prefix of an encoding is rejected. -/
theorem decode_proper_prefix {s t : Str} {d : Desc} (hst : s ++ t = encode d) (ht : t ≠ []) :
    decode s = none := by
  cases h : decode s with
  | none => rfl
  | some d' =>
    rw [decode_eq_some_iff] at h
    subst h
    have h1 := decDesc_encode d' t
    rw [hst, ← List.append_nil (encode d), decDesc_encode] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    exact absurd h1.2.symm ht

/-- The edge cases of the acceptance criterion round-trip: zero messages, empty blocks and
zero-width message registers. -/
example : decode (encode ⟨1, 0, [], [[]]⟩) = some ⟨1, 0, [], [[]]⟩ := decode_encode _
example : decodeChecked (encode Examples.threeMsg) = some Examples.threeMsg :=
  decodeChecked_encode (by decide)

end ShiQIP
