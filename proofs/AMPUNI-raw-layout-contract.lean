import Definitions.Def_ShiClassQMAAmp
import Theorems.Thm_ShiTM_encInstr_of_embedInstr_tag_preserved_index_remapped

set_option autoImplicit false

open ShiShallow ShiClassQMAAmp

namespace ShiTMRawLayout

abbrev Str := PvsNP.Str

/-- Untyped instruction data recovered by the total retained-description parser. -/
inductive RawInstr where
  | one (tag index : ℕ)
  | cnot (left right : ℕ)
deriving DecidableEq, Repr

def encode : RawInstr → Str
  | .one tag index => ShiBQP.encNat tag ++ ShiBQP.encNat index
  | .cnot left right =>
      ShiBQP.encNat 4 ++ ShiBQP.encNat left ++ ShiBQP.encNat right

def ofInstr {m : ℕ} : Instr m → RawInstr
  | .h i => .one 0 i
  | .s i => .one 1 i
  | .t i => .one 2 i
  | .x i => .one 3 i
  | .cnot i j _ => .cnot i j

/-- Apply the thirteen-piece wire-layout evaluator to every operand, preserving the tag. -/
def mapOperands (D : List (ℕ × ℕ) → ℕ → ℕ) (ps : List (ℕ × ℕ))
    (off : ℕ) : RawInstr → RawInstr
  | .one tag i => .one tag (D ps (off + i))
  | .cnot i j => .cnot (D ps (off + i)) (D ps (off + j))

def ampPieces (n wit anc : ℕ) : List (ℕ × ℕ) :=
  [(n, 0), (wit, n), (anc, n + 3 * wit), (1, n + 3 * wit + anc),
   (n, n + 3 * wit + anc + 1), (wit, n + wit),
   (anc, 2 * n + 3 * wit + anc + 1), (1, 2 * n + 3 * wit + 2 * anc + 1),
   (n, 2 * n + 3 * wit + 2 * anc + 2), (wit, n + 2 * wit),
   (anc, 3 * n + 3 * wit + 2 * anc + 2), (1, 3 * n + 3 * wit + 3 * anc + 2),
   (1, 3 * n + 3 * wit + 3 * anc + 3)]

def encodeLayer (l : List RawInstr) : Str :=
  ShiBQP.encNat l.length ++ (l.map encode).flatten

def encodeCirc (c : List (List RawInstr)) : Str :=
  ShiBQP.encNat c.length ++ (c.map encodeLayer).flatten

def mapLayer (D : List (ℕ × ℕ) → ℕ → ℕ) (ps : List (ℕ × ℕ))
    (off : ℕ) (l : List RawInstr) : List RawInstr :=
  l.map (mapOperands D ps off)

def mapCirc (D : List (ℕ × ℕ) → ℕ → ℕ) (ps : List (ℕ × ℕ))
    (off : ℕ) (c : List (List RawInstr)) : List (List RawInstr) :=
  c.map (mapLayer D ps off)

theorem encode_ofInstr {m : ℕ} (g : Instr m) :
    encode (ofInstr g) = ShiBQP.encInstr g := by
  cases g <;> rfl

/-- The single raw operation implemented by the one-index arm and the two-pass CNOT arm is
exactly `ShiEmbed.embedInstr` on every one of the five source constructors.  Bounds and CNOT
distinctness are supplied by the typed source instruction; the runtime parser need not
reconstruct proofs of either fact. -/
theorem encode_mapOperands_eq_embedInstr
    (D : List (ℕ × ℕ) → ℕ → ℕ)
    (n wit anc off : ℕ)
    (hoff : off + (n + (wit + (anc + 1))) ≤ 3 * (n + (wit + (anc + 1))))
    (he : Function.Injective (ampE n wit anc off hoff))
    (hmap : ∀ i : Fin (n + (wit + (anc + 1))),
      D (ampPieces n wit anc) (off + i.val) =
        ((ampE n wit anc off hoff) i).val)
    (g : Instr (n + (wit + (anc + 1)))) :
    encode (mapOperands D (ampPieces n wit anc) off (ofInstr g)) =
      ShiBQP.encInstr (ShiEmbed.embedInstr (ampE n wit anc off hoff) he g) := by
  have hc := ShiTM.encInstr_of_embedInstr_tag_preserved_index_remapped.1
    (n + (wit + (anc + 1)))
    (n + (3 * wit + ((2 * n + 3 * anc + 3) + 1)))
    (ampE n wit anc off hoff) he
  cases g with
  | h i => simp only [ofInstr, mapOperands, encode, hc.1, hmap]
  | s i => simp only [ofInstr, mapOperands, encode, hc.2.1, hmap]
  | t i => simp only [ofInstr, mapOperands, encode, hc.2.2.1, hmap]
  | x i => simp only [ofInstr, mapOperands, encode, hc.2.2.2.1, hmap]
  | cnot i j hij => simp only [ofInstr, mapOperands, encode, hc.2.2.2.2.1, hmap]

/-- Lifting the five-constructor contract through both encoding length prefixes yields the
exact encoding of a complete embedded circuit copy.  This is the contract consumed by the
outer nested iterator. -/
theorem encode_mapCirc_eq_embedCirc
    (D : List (ℕ × ℕ) → ℕ → ℕ)
    (n wit anc off : ℕ)
    (hoff : off + (n + (wit + (anc + 1))) ≤ 3 * (n + (wit + (anc + 1))))
    (he : Function.Injective (ampE n wit anc off hoff))
    (hmap : ∀ i : Fin (n + (wit + (anc + 1))),
      D (ampPieces n wit anc) (off + i.val) =
        ((ampE n wit anc off hoff) i).val)
    (c : Layered (n + (wit + (anc + 1)))) :
    encodeCirc
        (mapCirc D (ampPieces n wit anc) off (c.map (List.map ofInstr))) =
      ShiBQP.encCirc (ShiEmbed.embedCirc (ampE n wit anc off hoff) he c) := by
  have hLayer (l : List (Instr (n + (wit + (anc + 1))))) :
      encodeLayer (mapLayer D (ampPieces n wit anc) off (l.map ofInstr)) =
        ShiBQP.encLayer (ShiEmbed.embedLayer (ampE n wit anc off hoff) he l) := by
    have hGate :
        l.map (fun g => encode (mapOperands D (ampPieces n wit anc) off (ofInstr g))) =
          l.map (fun g => ShiBQP.encInstr
            (ShiEmbed.embedInstr (ampE n wit anc off hoff) he g)) := by
      apply List.map_congr_left
      intro g _
      exact encode_mapOperands_eq_embedInstr D n wit anc off hoff he hmap g
    unfold encodeLayer mapLayer ShiBQP.encLayer ShiBQP.encStr ShiEmbed.embedLayer
    simp only [List.length_map, List.map_map]
    simpa only [Function.comp_def] using
      congrArg (fun xs : List (List Bool) => ShiBQP.encNat l.length ++ xs.flatten) hGate
  have hLayers :
      c.map (fun l => encodeLayer
        (mapLayer D (ampPieces n wit anc) off (l.map ofInstr))) =
        c.map (fun l => ShiBQP.encLayer
          (ShiEmbed.embedLayer (ampE n wit anc off hoff) he l)) := by
    apply List.map_congr_left
    intro l _
    exact hLayer l
  unfold encodeCirc mapCirc ShiBQP.encCirc ShiBQP.encStr ShiEmbed.embedCirc
  simp only [List.length_map, List.map_map]
  simpa only [Function.comp_def] using
    congrArg (fun xs : List (List Bool) => ShiBQP.encNat c.length ++ xs.flatten) hLayers

end ShiTMRawLayout
