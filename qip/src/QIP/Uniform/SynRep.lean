import QIP.Uniform.Lib
import QIP.Encoding


/-!
# Q34 — tree representations of verifier syntax

`Dir` as a Boolean, `Message` as `(dir, width)`, `Gate` as `(tag, (i, j))` (tags `0 … 4` for
`h, s, t, x, cnot`; `j = 0` for one-qubit gates), `Desc` as `(priv, (out, (msgs, blocks)))`.
Projections, constructors and case analysis are polynomial time.
-/

namespace ShiQIP.Uniform

open ShiQIP

/-- A function that reads its input through a re-encoding with the same code is `PT`. -/
theorem PT.reenc {α β γ : Type} [Rep α] [Rep β] [Rep γ] {f : α → β} {e : α → γ} {g : γ → β}
    (hg : PT g) (he : ∀ a, enc (e a) = enc a) (hf : ∀ a, f a = g (e a)) : PT f := by
  obtain ⟨B, p, hp⟩ := hg
  refine ⟨B, p, fun a => ?_⟩
  obtain ⟨hl, t, ht, hB⟩ := hp (e a)
  rw [he] at hl ht hB
  rw [hf]
  exact ⟨hl, t, ht, hB⟩

/-! ### Directions -/

/-- `toVerifier ↦ true`. -/
def _root_.ShiQIP.Dir.toB : Dir → Bool
  | .toVerifier => true
  | .toProver => false

/-- `true ↦ toVerifier`. -/
def _root_.ShiQIP.Dir.ofB (b : Bool) : Dir := if b then .toVerifier else .toProver

theorem _root_.ShiQIP.Dir.ofB_toB (d : Dir) : Dir.ofB d.toB = d := by cases d <;> rfl

instance : Rep Dir := ⟨fun d => Rep.toV d.toB⟩

theorem PT.dirToB : PT Dir.toB := PT.ofEnc fun _ => rfl

theorem PT.dirOfB : PT Dir.ofB := PT.ofEnc fun b => by cases b <;> rfl

@[fun_prop] theorem PT.fp_dirToB {α : Type} [Rep α] {f : α → Dir} (hf : PT f) :
    PT fun x => (f x).toB := PT.comp hf PT.dirToB

@[fun_prop] theorem PT.fp_dirOfB {α : Type} [Rep α] {f : α → Bool} (hf : PT f) :
    PT fun x => Dir.ofB (f x) := PT.comp hf PT.dirOfB

/-! ### Messages -/

instance : Rep Message := ⟨fun m => Rep.toV (m.dir, m.width)⟩

theorem PT.msgDir : PT Message.dir :=
  PT.reenc (e := fun m : Message => (m.dir, m.width)) PT.fst (fun _ => rfl) fun _ => rfl

theorem PT.msgWidth : PT Message.width :=
  PT.reenc (e := fun m : Message => (m.dir, m.width)) PT.snd (fun _ => rfl) fun _ => rfl

theorem PT.msgMk : PT fun p : Dir × ℕ => (⟨p.1, p.2⟩ : Message) := PT.ofEnc fun _ => rfl

@[fun_prop] theorem PT.fp_msgDir {α : Type} [Rep α] {f : α → Message} (hf : PT f) :
    PT fun x => (f x).dir := PT.comp hf PT.msgDir

@[fun_prop] theorem PT.fp_msgWidth {α : Type} [Rep α] {f : α → Message} (hf : PT f) :
    PT fun x => (f x).width := PT.comp hf PT.msgWidth

@[fun_prop] theorem PT.fp_msgMk {α : Type} [Rep α] {f : α → Dir} {g : α → ℕ} (hf : PT f)
    (hg : PT g) : PT fun x => (⟨f x, g x⟩ : Message) := PT.comp (PT.pair hf hg) PT.msgMk

/-! ### Gates -/

/-- The code of a gate: tag and wires. -/
def _root_.ShiQIP.Gate.cd : Gate → ℕ × (ℕ × ℕ)
  | .h i => (0, i, 0)
  | .s i => (1, i, 0)
  | .t i => (2, i, 0)
  | .x i => (3, i, 0)
  | .cnot i j => (4, i, j)

/-- The gate of a code (tag `≥ 4` is a CNOT). -/
def _root_.ShiQIP.Gate.ofCd (c : ℕ × (ℕ × ℕ)) : Gate :=
  if c.1 = 0 then .h c.2.1 else if c.1 = 1 then .s c.2.1 else if c.1 = 2 then .t c.2.1 else
    if c.1 = 3 then .x c.2.1 else .cnot c.2.1 c.2.2

theorem _root_.ShiQIP.Gate.ofCd_cd (g : Gate) : Gate.ofCd g.cd = g := by cases g <;> rfl

instance : Rep Gate := ⟨fun g => Rep.toV g.cd⟩

theorem PT.gateCd : PT Gate.cd := PT.ofEnc fun _ => rfl

/-- Gates are built from codes by nested selection over trees of codes. -/
theorem PT.gateOfCd : PT Gate.ofCd := by
  have h : PT fun c : ℕ × (ℕ × ℕ) => (if c.1 = 0 then (0, c.2.1, 0) else if c.1 = 1 then
      (1, c.2.1, 0) else if c.1 = 2 then (2, c.2.1, 0) else if c.1 = 3 then (3, c.2.1, 0) else
        (4, c.2.1, c.2.2) : ℕ × (ℕ × ℕ)) := by fun_prop
  refine PT.congrOut h fun c => ?_
  unfold Gate.ofCd
  split_ifs <;> rfl

@[fun_prop] theorem PT.fp_gateCd {α : Type} [Rep α] {f : α → Gate} (hf : PT f) :
    PT fun x => (f x).cd := PT.comp hf PT.gateCd

@[fun_prop] theorem PT.fp_gateOfCd {α : Type} [Rep α] {f : α → ℕ × (ℕ × ℕ)} (hf : PT f) :
    PT fun x => Gate.ofCd (f x) := PT.comp hf PT.gateOfCd

@[fun_prop] theorem PT.fp_gate_h {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) :
    PT fun x => Gate.h (f x) :=
  PT.congrOut (show PT fun x => ((0 : ℕ), f x, (0 : ℕ)) by fun_prop) fun _ => rfl

@[fun_prop] theorem PT.fp_gate_s {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) :
    PT fun x => Gate.s (f x) :=
  PT.congrOut (show PT fun x => ((1 : ℕ), f x, (0 : ℕ)) by fun_prop) fun _ => rfl

@[fun_prop] theorem PT.fp_gate_t {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) :
    PT fun x => Gate.t (f x) :=
  PT.congrOut (show PT fun x => ((2 : ℕ), f x, (0 : ℕ)) by fun_prop) fun _ => rfl

@[fun_prop] theorem PT.fp_gate_x {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) :
    PT fun x => Gate.x (f x) :=
  PT.congrOut (show PT fun x => ((3 : ℕ), f x, (0 : ℕ)) by fun_prop) fun _ => rfl

@[fun_prop] theorem PT.fp_gate_cnot {α : Type} [Rep α] {f g : α → ℕ} (hf : PT f) (hg : PT g) :
    PT fun x => Gate.cnot (f x) (g x) :=
  PT.congrOut (show PT fun x => ((4 : ℕ), f x, g x) by fun_prop) fun _ => rfl

/-! ### Descriptions -/

instance : Rep Desc := ⟨fun d => Rep.toV (d.priv, d.out, d.msgs, d.blocks)⟩

/-- The tuple of a description. -/
def _root_.ShiQIP.Desc.tup (d : Desc) : ℕ × (ℕ × (List Message × List (List Gate))) :=
  (d.priv, d.out, d.msgs, d.blocks)

theorem PT.descTup : PT Desc.tup := PT.ofEnc fun _ => rfl

theorem PT.descMk : PT fun p : ℕ × (ℕ × (List Message × List (List Gate))) =>
    (⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩ : Desc) := PT.ofEnc fun _ => rfl

@[fun_prop] theorem PT.fp_descTup {α : Type} [Rep α] {f : α → Desc} (hf : PT f) :
    PT fun x => (f x).tup := PT.comp hf PT.descTup

@[fun_prop] theorem PT.fp_priv {α : Type} [Rep α] {f : α → Desc} (hf : PT f) :
    PT fun x => (f x).priv := PT.fp_fst (PT.fp_descTup hf)

@[fun_prop] theorem PT.fp_out {α : Type} [Rep α] {f : α → Desc} (hf : PT f) :
    PT fun x => (f x).out := PT.fp_fst (PT.fp_snd (PT.fp_descTup hf))

@[fun_prop] theorem PT.fp_msgs {α : Type} [Rep α] {f : α → Desc} (hf : PT f) :
    PT fun x => (f x).msgs := PT.fp_fst (PT.fp_snd (PT.fp_snd (PT.fp_descTup hf)))

@[fun_prop] theorem PT.fp_blocks {α : Type} [Rep α] {f : α → Desc} (hf : PT f) :
    PT fun x => (f x).blocks := PT.fp_snd (PT.fp_snd (PT.fp_snd (PT.fp_descTup hf)))

@[fun_prop] theorem PT.fp_descMk {α : Type} [Rep α] {a b : α → ℕ} {c : α → List Message}
    {e : α → List (List Gate)} (ha : PT a) (hb : PT b) (hc : PT c) (he : PT e) :
    PT fun x => (⟨a x, b x, c x, e x⟩ : Desc) :=
  PT.comp (show PT fun x => (a x, b x, c x, e x) by fun_prop) PT.descMk

example : PT fun d : Desc => d.priv + d.msgs.length := by fun_prop

end ShiQIP.Uniform
