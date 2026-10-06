import QIP.Uniform.Bridge
import Mathlib.Tactic.FunProp


/-!
# Q34 — a library of polynomial-time functions

Total tree primitives `vfst`, `vsnd`, `isNode` (each a concrete machine), re-encoding lemmas
(`PT.ofV`), and derived functions on naturals and lists, each obtained from the closure
combinators of `QIP.Uniform.PT`.
-/

namespace ShiQIP.Uniform

open Turing

/-! ### Total tree primitives -/

@[simp] theorem toV_V (v : V) : Rep.toV v = v := rfl

@[simp] theorem enc_V (v : V) : enc v = v.code := rfl

/-- The left subtree (a leaf for a leaf). -/
def vfst : V → V
  | .leaf => .leaf
  | .node a _ => a

/-- The right subtree (a leaf for a leaf). -/
def vsnd : V → V
  | .leaf => .leaf
  | .node _ b => b

/-- Whether a tree is a node. -/
def isNode : V → Bool
  | .leaf => false
  | .node _ _ => true

theorem constM_runs' (o : Option Bool) (w : V) (x : List Bool) :
    Runs (constM w) (o, ()) (reg4 x [] [] []) (none, ()) (reg4 [] [] w.code [])
      (1 + (2 * x.length + 2)) := by
  have r₁ := runs_discard (τ := Unit) Reg.a o () (reg4 x [] [] [])
  have r₂ := runs_basic (σ := Option Bool × Unit) (pushL Reg.c w.code.reverse .halt) (none, ())
    (reg4 [] [] [] []) (by rw [stepAux_pushL]; rfl)
  simp only [stepAux_pushL, TM2.stepAux] at r₂
  exact runs_seq (r₁.of_eq rfl (show _ = reg4 [] [] [] [] by reg_tac) rfl)
    (r₂.of_eq rfl (show _ = reg4 [] [] w.code [] by reg_tac) rfl)

/-- Peek register `a` into the scratch register. -/
def peekR : BS Reg Unit (Option Bool × Unit) := .peek .a (fun v x => (x, v.2)) .halt

/-- Branch on the root of the input: node (`M₁`) or leaf (`M₂`). -/
def caseM (M₁ M₂ : Mach Reg (Option Bool × Unit)) : Mach Reg (Option Bool × Unit) :=
  seq (basic peekR) (ite (fun v => v.1.getD false) M₁ M₂)

theorem caseM_node {M₁ M₂ : Mach Reg (Option Bool × Unit)} (a b : V) {y : List Bool} {t : ℕ}
    (h : Runs M₁ (some true, ()) (reg4 (V.node a b).code [] [] []) (none, ()) (reg4 [] [] y []) t) :
    Runs (caseM M₁ M₂) (none, ()) (reg4 (V.node a b).code [] [] []) (none, ()) (reg4 [] [] y [])
      (t + 1 + 1) := by
  have r₁ := runs_basic peekR (none, ()) (reg4 (V.node a b).code [] [] []) rfl
  simp only [peekR, TM2.stepAux, reg4, V.code, List.head?_cons] at r₁
  exact runs_seq r₁ (runs_ite_true (c := fun v : Option Bool × Unit => v.1.getD false) rfl h)

theorem caseM_leaf {M₁ M₂ : Mach Reg (Option Bool × Unit)} {y : List Bool} {t : ℕ}
    (h : Runs M₂ (some false, ()) (reg4 V.leaf.code [] [] []) (none, ()) (reg4 [] [] y []) t) :
    Runs (caseM M₁ M₂) (none, ()) (reg4 V.leaf.code [] [] []) (none, ()) (reg4 [] [] y [])
      (t + 1 + 1) := by
  have r₁ := runs_basic peekR (none, ()) (reg4 V.leaf.code [] [] []) rfl
  simp only [peekR, TM2.stepAux, reg4, V.code, List.head?_cons] at r₁
  exact runs_seq r₁ (runs_ite_false (c := fun v : Option Bool × Unit => v.1.getD false) rfl h)

theorem PT.vfstU : PT vfst := by
  refine ⟨regB (caseM fstM (constM .leaf)), 6 * Polynomial.X + 9, fun v => ?_⟩
  cases v with
  | leaf =>
    refine ⟨by simp [ShiQIP.Uniform.vfst, V.code], _, ?_, regB_computes (caseM_leaf (constM_runs' _ _ _))⟩
    simp [V.code]
  | node a b =>
    refine ⟨?_, _, ?_, regB_computes (caseM_node a b (fstM_runs _ a b))⟩
    · simp only [ShiQIP.Uniform.vfst, enc_V, V.code, List.length_cons, List.length_append, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega
    · simp only [enc_V, V.code, List.length_cons, List.length_append, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega

theorem PT.vsndU : PT vsnd := by
  refine ⟨regB (caseM sndM (constM .leaf)), 8 * Polynomial.X + 9, fun v => ?_⟩
  cases v with
  | leaf =>
    refine ⟨by simp [ShiQIP.Uniform.vsnd, V.code], _, ?_, regB_computes (caseM_leaf (constM_runs' _ _ _))⟩
    simp [V.code]
  | node a b =>
    refine ⟨?_, _, ?_, regB_computes (caseM_node a b (sndM_runs _ a b))⟩
    · simp only [ShiQIP.Uniform.vsnd, enc_V, V.code, List.length_cons, List.length_append, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega
    · simp only [enc_V, V.code, List.length_cons, List.length_append, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega

theorem PT.isNodeU : PT isNode := by
  refine ⟨regB (caseM (constM (Rep.toV true)) (constM (Rep.toV false))), 2 * Polynomial.X + 9,
    fun v => ?_⟩
  cases v with
  | leaf =>
    refine ⟨by simp [ShiQIP.Uniform.isNode, enc, Rep.toV, V.code], _, ?_,
      regB_computes (caseM_leaf (constM_runs' _ _ _))⟩
    simp [V.code]
  | node a b =>
    refine ⟨?_, _, ?_, regB_computes (caseM_node a b (constM_runs' _ _ _))⟩
    · simp only [ShiQIP.Uniform.isNode, enc, Rep.toV, V.code, if_true, List.length_cons,
        List.length_nil, List.length_append, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat]
      omega
    · simp only [enc_V, V.code, List.length_cons, List.length_append, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega

/-! ### Re-encodings -/

/-- A function that acts on representations through a `PT` function of trees is `PT`. -/
theorem PT.ofV {α β γ : Type} [Rep α] [Rep β] [Rep γ] {f : α → β} {F : V → γ} (hF : PT F)
    (h : ∀ a, enc (f a) = enc (F (Rep.toV a))) : PT f := by
  obtain ⟨B, p, hp⟩ := hF
  refine ⟨B, p, fun a => ?_⟩
  obtain ⟨hl, t, ht, hB⟩ := hp (Rep.toV a)
  exact ⟨by rw [h]; exact hl, t, ht, by rw [h]; exact hB⟩

/-- The tree of a value, as a function. -/
theorem PT.toV {α : Type} [Rep α] : PT (Rep.toV : α → V) := PT.ofEnc fun _ => rfl

theorem PT.of_eq {α β : Type} [Rep α] [Rep β] {f g : α → β} (hf : PT f) (h : ∀ a, f a = g a) :
    PT g := by
  rwa [show g = f from funext fun a => (h a).symm]

/-- A function whose outputs have the same codes as those of a `PT` function is `PT`. -/
theorem PT.congrOut {α β γ : Type} [Rep α] [Rep β] [Rep γ] {f : α → β} {g : α → γ} (hf : PT f)
    (h : ∀ a, enc (g a) = enc (f a)) : PT g := by
  obtain ⟨B, p, hp⟩ := hf
  refine ⟨B, p, fun a => ?_⟩
  obtain ⟨hl, t, ht, hB⟩ := hp a
  exact ⟨by rw [h]; exact hl, t, ht, by rw [h]; exact hB⟩

/-- Composition with two arguments. -/
theorem PT.comp₂ {α β γ δ : Type} [Rep α] [Rep β] [Rep γ] [Rep δ] {g : β × γ → δ} {f₁ : α → β}
    {f₂ : α → γ} (hg : PT g) (h₁ : PT f₁) (h₂ : PT f₂) : PT fun a => g (f₁ a, f₂ a) :=
  PT.comp (PT.pair h₁ h₂) hg

/-! ### Code lengths -/

theorem enc_nat_length (n : ℕ) : (enc n).length = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [enc_succ]; simp [ih]; ring

theorem enc_pair_length {α β : Type} [Rep α] [Rep β] (a : α) (b : β) :
    (enc (a, b)).length = (enc a).length + (enc b).length + 1 := by
  simp [enc_pair]

theorem enc_cons_length {α : Type} [Rep α] (a : α) (l : List α) :
    (enc (a :: l)).length = (enc a).length + (enc l).length + 1 := by
  simp [enc_cons]

theorem enc_bool_length (b : Bool) : (enc b).length ≤ 3 := by
  cases b <;> simp [enc_true, enc_false]

theorem enc_unit (u : Unit) : enc u = [false] := rfl

/-! ### Folds with bounded growth -/

theorem foldS_take_le {α β : Type} [Rep α] [Rep β] (step : β × α → β) (D : ℕ) (s : β)
    (xs : List α) (hD : ∀ k x, xs[k]? = some x → (enc (step (foldS step s (xs.take k), x))).length ≤
      (enc (foldS step s (xs.take k))).length + D) :
    ∀ k, (enc (foldS step s (xs.take k))).length ≤ (enc s).length + min k xs.length * D := by
  intro k
  induction k with
  | zero => simp [foldS]
  | succ k ih =>
    rcases hx : xs[k]? with _ | x
    · have hk : xs.length ≤ k := by simpa using hx
      rw [List.take_of_length_le (by omega), min_eq_right (by omega)]
      rw [List.take_of_length_le hk, min_eq_right hk] at ih
      exact ih
    · have hk : k < xs.length := by
        by_contra h; simp [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hx
      rw [foldS_take_succ step s xs k x hx, min_eq_left (by omega)]
      have := hD k x hx
      rw [min_eq_left (by omega)] at ih
      nlinarith

/-- **Folds with polynomially bounded growth per step.** -/
theorem PT.foldl_add {α β : Type} [Rep α] [Rep β] {step : β × α → β} (hstep : PT step)
    (D : Polynomial ℕ) (hD : ∀ (s : β) (xs : List α) (k : ℕ) (x : α), xs[k]? = some x →
      (enc (step (foldS step s (xs.take k), x))).length ≤
        (enc (foldS step s (xs.take k))).length + D.eval (enc (s, xs)).length) :
    PT fun p : β × List α => foldS step p.1 p.2 := by
  refine PT.foldl hstep ⟨Polynomial.X + Polynomial.X * D, fun s xs k => ?_⟩
  have h := foldS_take_le step _ s xs (fun k x hx => hD s xs k x hx) k
  have h₁ := length_lt_enc_list xs
  have h₂ : (enc s).length ≤ (enc (s, xs)).length := by rw [enc_pair_length]; omega
  have h₃ : min k xs.length ≤ (enc (s, xs)).length := by rw [enc_pair_length]; omega
  have h₄ := Nat.mul_le_mul_right (D.eval (enc (s, xs)).length) h₃
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul]
  omega

/-- **Folds with uniformly bounded additive growth.** -/
theorem PT.foldl_unif {α β : Type} [Rep α] [Rep β] {step : β × α → β} (hstep : PT step) (c : ℕ)
    (hc : ∀ s x, (enc (step (s, x))).length ≤ (enc s).length + (enc x).length + c) :
    PT fun p : β × List α => foldS step p.1 p.2 := by
  refine PT.foldl_add hstep (Polynomial.X + Polynomial.C c) fun s xs k x hx => ?_
  have h₁ := enc_get_lt xs k x hx
  have h₂ : (enc xs).length ≤ (enc (s, xs)).length := by rw [enc_pair_length]; omega
  have := hc (foldS step s (xs.take k)) x
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  omega

/-! ### `fun_prop` set-up -/

attribute [fun_prop] PT

@[fun_prop] theorem PT.fp_id {α : Type} [Rep α] : PT fun x : α => x := PT.id

@[fun_prop] theorem PT.fp_const {α β : Type} [Rep α] [Rep β] (c : β) : PT fun _ : α => c :=
  PT.const c

@[fun_prop] theorem PT.fp_comp {α β γ : Type} [Rep α] [Rep β] [Rep γ] {f : β → γ} {g : α → β}
    (hf : PT f) (hg : PT g) : PT fun x => f (g x) := PT.comp hg hf

@[fun_prop] theorem PT.fp_pair {α β γ : Type} [Rep α] [Rep β] [Rep γ] {f : α → β} {g : α → γ}
    (hf : PT f) (hg : PT g) : PT fun x => (f x, g x) := PT.pair hf hg

@[fun_prop] theorem PT.fp_fst {α β γ : Type} [Rep α] [Rep β] [Rep γ] {f : α → β × γ}
    (hf : PT f) : PT fun x => (f x).1 := PT.comp hf PT.fst

@[fun_prop] theorem PT.fp_snd {α β γ : Type} [Rep α] [Rep β] [Rep γ] {f : α → β × γ}
    (hf : PT f) : PT fun x => (f x).2 := PT.comp hf PT.snd

@[fun_prop] theorem PT.fp_ite {α β : Type} [Rep α] [Rep β] {c : α → Bool} {f g : α → β}
    (hc : PT c) (hf : PT f) (hg : PT g) : PT fun x => if c x then f x else g x := PT.ite hc hf hg

@[fun_prop] theorem PT.fp_ite' {α β : Type} [Rep α] [Rep β] {p : α → Prop} [DecidablePred p]
    {f g : α → β} (hp : PT fun x => decide (p x)) (hf : PT f) (hg : PT g) :
    PT fun x => if p x then f x else g x :=
  (PT.ite hp hf hg).of_eq fun x => by by_cases h : p x <;> simp [h]

/-! ### Naturals -/

theorem enc_replicate_unit (n : ℕ) : enc (List.replicate n ()) = enc n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, enc_cons, ih, enc_succ]; rfl

theorem PT.units : PT fun n : ℕ => List.replicate n () := PT.ofEnc enc_replicate_unit

theorem PT.succU : PT fun n : ℕ => n + 1 :=
  PT.congrOut (PT.pair (PT.const ()) PT.id : PT fun n : ℕ => ((), n)) fun _ => rfl

theorem PT.predU : PT fun n : ℕ => n - 1 := PT.ofV PT.vsndU fun n => by cases n <;> rfl

theorem PT.posU : PT fun n : ℕ => decide (0 < n) :=
  PT.ofV PT.isNodeU fun n => by cases n <;> rfl

@[fun_prop] theorem PT.fp_succ {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) : PT fun x => f x + 1 :=
  PT.comp hf PT.succU

@[fun_prop] theorem PT.fp_pred {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) : PT fun x => f x - 1 :=
  PT.comp hf PT.predU

@[fun_prop] theorem PT.fp_pos {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) :
    PT fun x => decide (0 < f x) := PT.comp hf PT.posU

theorem PT.notU : PT fun b : Bool => !b :=
  (PT.ite PT.id (PT.const false) (PT.const true)).of_eq fun b => by cases b <;> rfl

@[fun_prop] theorem PT.fp_not {α : Type} [Rep α] {f : α → Bool} (hf : PT f) : PT fun x => !f x :=
  PT.comp hf PT.notU

@[fun_prop] theorem PT.fp_and {α : Type} [Rep α] {f g : α → Bool} (hf : PT f) (hg : PT g) :
    PT fun x => f x && g x :=
  (PT.ite hf hg (PT.const false)).of_eq fun x => by cases f x <;> rfl

@[fun_prop] theorem PT.fp_or {α : Type} [Rep α] {f g : α → Bool} (hf : PT f) (hg : PT g) :
    PT fun x => f x || g x :=
  (PT.ite hf (PT.const true) hg).of_eq fun x => by cases f x <;> rfl

/-- Iterating `s ↦ s + 1` along a list of units adds its length. -/
theorem foldS_succ (m n : ℕ) :
    foldS (fun q : ℕ × Unit => q.1 + 1) m (List.replicate n ()) = m + n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    simp only [foldS, List.foldl_cons] at ih ⊢
    rw [ih]; ring

theorem foldS_pred (m n : ℕ) :
    foldS (fun q : ℕ × Unit => q.1 - 1) m (List.replicate n ()) = m - n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    simp only [foldS, List.foldl_cons] at ih ⊢
    rw [ih]; omega

theorem PT.addU : PT fun p : ℕ × ℕ => p.1 + p.2 := by
  have h := PT.foldl_unif (step := fun q : ℕ × Unit => q.1 + 1) (by fun_prop) 2 fun s _ => by
    simp only [enc_nat_length]; omega
  exact (PT.comp (PT.pair PT.fst (PT.comp PT.snd PT.units)) h).of_eq fun p => foldS_succ _ _

theorem PT.subU : PT fun p : ℕ × ℕ => p.1 - p.2 := by
  have h := PT.foldl_unif (step := fun q : ℕ × Unit => q.1 - 1) (by fun_prop) 0 fun s _ => by
    simp only [enc_nat_length]; omega
  exact (PT.comp (PT.pair PT.fst (PT.comp PT.snd PT.units)) h).of_eq fun p => foldS_pred _ _

@[fun_prop] theorem PT.fp_add {α : Type} [Rep α] {f g : α → ℕ} (hf : PT f) (hg : PT g) :
    PT fun x => f x + g x := PT.comp (PT.pair hf hg) PT.addU

@[fun_prop] theorem PT.fp_sub {α : Type} [Rep α] {f g : α → ℕ} (hf : PT f) (hg : PT g) :
    PT fun x => f x - g x := PT.comp (PT.pair hf hg) PT.subU

@[fun_prop] theorem PT.fp_le {α : Type} [Rep α] {f g : α → ℕ} (hf : PT f) (hg : PT g) :
    PT fun x => decide (f x ≤ g x) :=
  (PT.fp_not (PT.fp_pos (PT.fp_sub hf hg))).of_eq fun x => by
    by_cases h : f x ≤ g x
    · simp [h, Nat.sub_eq_zero_of_le h]
    · have : 0 < f x - g x := by omega
      simp [h, this]

@[fun_prop] theorem PT.fp_lt {α : Type} [Rep α] {f g : α → ℕ} (hf : PT f) (hg : PT g) :
    PT fun x => decide (f x < g x) :=
  (PT.fp_le (PT.fp_succ hf) hg).of_eq fun x => by simp

@[fun_prop] theorem PT.fp_eq {α : Type} [Rep α] {f g : α → ℕ} (hf : PT f) (hg : PT g) :
    PT fun x => decide (f x = g x) :=
  (PT.fp_and (PT.fp_le hf hg) (PT.fp_le hg hf)).of_eq fun x => by
    rw [← Bool.decide_and]; exact decide_eq_decide.mpr le_antisymm_iff.symm

@[fun_prop] theorem PT.fp_max {α : Type} [Rep α] {f g : α → ℕ} (hf : PT f) (hg : PT g) :
    PT fun x => max (f x) (g x) :=
  (PT.fp_ite' (p := fun x => f x ≤ g x) (PT.fp_le hf hg) hg hf).of_eq fun x => by
    by_cases h : f x ≤ g x <;> simp [h, max_def]

@[fun_prop] theorem PT.fp_min {α : Type} [Rep α] {f g : α → ℕ} (hf : PT f) (hg : PT g) :
    PT fun x => min (f x) (g x) :=
  (PT.fp_ite' (p := fun x => f x ≤ g x) (PT.fp_le hf hg) hf hg).of_eq fun x => by
    by_cases h : f x ≤ g x <;> simp [h, min_def]

/-! ### Lists -/

@[fun_prop] theorem PT.fp_toV {α β : Type} [Rep α] [Rep β] {f : α → β} (hf : PT f) :
    PT fun x => (Rep.toV (f x) : V) := PT.comp hf PT.toV

@[fun_prop] theorem PT.fp_isNode {α : Type} [Rep α] {f : α → V} (hf : PT f) :
    PT fun x => isNode (f x) := PT.comp hf PT.isNodeU

@[fun_prop] theorem PT.fp_vfst {α : Type} [Rep α] {f : α → V} (hf : PT f) :
    PT fun x => vfst (f x) := PT.comp hf PT.vfstU

@[fun_prop] theorem PT.fp_vsnd {α : Type} [Rep α] {f : α → V} (hf : PT f) :
    PT fun x => vsnd (f x) := PT.comp hf PT.vsndU

@[fun_prop] theorem PT.fp_cons {α β : Type} [Rep α] [Rep β] {f : α → β} {g : α → List β} (hf : PT f)
    (hg : PT g) : PT fun x => f x :: g x :=
  PT.congrOut (PT.pair hf hg) fun _ => rfl

theorem PT.isEmptyU {α : Type} [Rep α] : PT fun l : List α => l.isEmpty :=
  PT.ofV (F := fun v => !isNode v) (by fun_prop) fun l => by cases l <;> rfl

@[fun_prop] theorem PT.fp_isEmpty {α β : Type} [Rep α] [Rep β] {f : α → List β} (hf : PT f) :
    PT fun x => (f x).isEmpty := PT.comp hf PT.isEmptyU

theorem PT.tailU {α : Type} [Rep α] : PT fun l : List α => l.tail :=
  PT.ofV PT.vsndU fun l => by cases l <;> rfl

@[fun_prop] theorem PT.fp_tail {α β : Type} [Rep α] [Rep β] {f : α → List β} (hf : PT f) :
    PT fun x => (f x).tail := PT.comp hf PT.tailU

theorem PT.headDU {α : Type} [Rep α] : PT fun p : List α × α => p.1.headD p.2 := by
  have h : PT fun p : List α × α =>
      (if p.1.isEmpty then Rep.toV p.2 else vfst (Rep.toV p.1) : V) := by fun_prop
  exact PT.congrOut h fun ⟨l, d⟩ => by cases l <;> rfl

@[fun_prop] theorem PT.fp_headD {α β : Type} [Rep α] [Rep β] {f : α → List β} {g : α → β} (hf : PT f)
    (hg : PT g) : PT fun x => (f x).headD (g x) := PT.comp (PT.pair hf hg) PT.headDU

theorem foldS_length {α : Type} (m : ℕ) (l : List α) :
    foldS (fun q : ℕ × α => q.1 + 1) m l = m + l.length := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih => simp only [foldS, List.foldl_cons] at ih ⊢; rw [ih]; simp; ring

theorem PT.lengthU {α : Type} [Rep α] : PT fun l : List α => l.length := by
  have h := PT.foldl_unif (α := α) (step := fun q : ℕ × α => q.1 + 1) (by fun_prop) 2 fun s _ => by
    simp only [enc_nat_length]; omega
  exact (PT.comp (PT.pair (PT.const 0) PT.id) h).of_eq fun l => by
    simp [foldS_length]

@[fun_prop] theorem PT.fp_length {α β : Type} [Rep α] [Rep β] {f : α → List β} (hf : PT f) :
    PT fun x => (f x).length := PT.comp hf PT.lengthU

theorem foldS_rev {α : Type} (acc l : List α) :
    foldS (fun q : List α × α => q.2 :: q.1) acc l = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih => simp only [foldS, List.foldl_cons] at ih ⊢; rw [ih]; simp

theorem PT.revOnto {α : Type} [Rep α] : PT fun p : List α × List α => p.2.reverse ++ p.1 := by
  have h := PT.foldl_unif (α := α) (step := fun q : List α × α => q.2 :: q.1) (by fun_prop) 1
    fun s x => by dsimp only; rw [enc_cons_length]; omega
  exact h.of_eq fun p => foldS_rev _ _

@[fun_prop] theorem PT.fp_reverse {α β : Type} [Rep α] [Rep β] {f : α → List β} (hf : PT f) :
    PT fun x => (f x).reverse :=
  (PT.comp (PT.pair (PT.const []) hf) PT.revOnto).of_eq fun x => by simp

@[fun_prop] theorem PT.fp_append {α β : Type} [Rep α] [Rep β] {f g : α → List β} (hf : PT f)
    (hg : PT g) : PT fun x => f x ++ g x :=
  (PT.comp (PT.pair hg (PT.fp_reverse hf)) PT.revOnto).of_eq fun x => by simp

/-- Map with a context, as a fold. -/
theorem foldS_map {α β γ : Type} (h : γ × α → β) (c : γ) (acc : List β) (l : List α) :
    foldS (fun q : (γ × List β) × α => (q.1.1, h (q.1.1, q.2) :: q.1.2)) (c, acc) l =
      (c, (l.map fun a => h (c, a)).reverse ++ acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih => simp only [foldS, List.foldl_cons] at ih ⊢; rw [ih]; simp

theorem PT.mapU {α β γ : Type} [Rep α] [Rep β] [Rep γ] {h : γ × α → β} (hh : PT h) :
    PT fun p : γ × List α => p.2.map fun a => h (p.1, a) := by
  have hh₀ := hh
  obtain ⟨B₀, q, hq⟩ := hh₀
  have hstep : PT fun q : (γ × List β) × α => (q.1.1, h (q.1.1, q.2) :: q.1.2) := by fun_prop
  have hf := PT.foldl_add hstep (q + 1) fun s xs k x hx => by
    obtain ⟨c, acc⟩ := s
    rw [foldS_map]
    simp only [enc_pair_length, enc_cons_length]
    have h₁ := enc_get_lt xs k x hx
    have h₂ := (hq (c, x)).1
    have h₃ : q.eval (enc (c, x)).length ≤ q.eval (enc ((c, acc), xs)).length := by
      apply ShiQIP.TMComp.eval_mono
      simp only [enc_pair_length]; omega
    simp only [enc_pair_length] at h₂ h₃
    simp only [Polynomial.eval_add, Polynomial.eval_one]
    omega
  exact (PT.comp (PT.pair (PT.pair PT.fst (PT.const [])) PT.snd) (PT.fp_reverse (PT.comp hf PT.snd))).of_eq
    fun ⟨c, l⟩ => by simp [foldS_map]

@[fun_prop] theorem PT.fp_map {α β δ : Type} [Rep α] [Rep β] [Rep δ] {h : δ → α → β}
    {l : δ → List α} (hh : PT fun p : δ × α => h p.1 p.2) (hl : PT l) :
    PT fun x => (l x).map (h x) :=
  (PT.comp (PT.pair PT.id hl) (PT.mapU hh)).of_eq fun _ => rfl

theorem foldS_flatten {α : Type} (acc : List α) (ls : List (List α)) :
    foldS (fun q : List α × List α => q.1 ++ q.2) acc ls = acc ++ ls.flatten := by
  induction ls generalizing acc with
  | nil => simp [foldS]
  | cons a l ih => simp only [foldS, List.foldl_cons] at ih ⊢; rw [ih]; simp

theorem enc_append_length {α : Type} [Rep α] (l₁ l₂ : List α) :
    (enc (l₁ ++ l₂)).length + 1 = (enc l₁).length + (enc l₂).length := by
  induction l₁ with
  | nil => simp [enc_nil]; omega
  | cons a l ih => simp only [List.cons_append, enc_cons_length]; omega

theorem PT.flattenU {α : Type} [Rep α] : PT fun ls : List (List α) => ls.flatten := by
  have h := PT.foldl_unif (α := List α) (step := fun q : List α × List α => q.1 ++ q.2)
    (by fun_prop) 0 fun s x => by dsimp only; have := enc_append_length s x; omega
  exact (PT.comp (PT.pair (PT.const []) PT.id) h).of_eq fun ls => by simp [foldS_flatten]

@[fun_prop] theorem PT.fp_flatten {α β : Type} [Rep α] [Rep β] {f : α → List (List β)} (hf : PT f) :
    PT fun x => (f x).flatten := PT.comp hf PT.flattenU

@[fun_prop] theorem PT.fp_flatMap {α β δ : Type} [Rep α] [Rep β] [Rep δ] {h : δ → α → List β}
    {l : δ → List α} (hh : PT fun p : δ × α => h p.1 p.2) (hl : PT l) :
    PT fun x => (l x).flatMap (h x) :=
  (PT.fp_flatten (PT.fp_map hh hl)).of_eq fun x => by simp [List.flatMap_def]

/-! ### More list functions -/

theorem foldS_sum (s : ℕ) (l : List ℕ) : foldS (fun q : ℕ × ℕ => q.1 + q.2) s l = s + l.sum := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => simp only [foldS, List.foldl_cons] at ih ⊢; rw [ih]; simp; ring

theorem PT.sumU : PT fun l : List ℕ => l.sum := by
  have h := PT.foldl_unif (α := ℕ) (step := fun q : ℕ × ℕ => q.1 + q.2) (by fun_prop) 0
    fun s x => by dsimp only; simp only [enc_nat_length]; omega
  exact (PT.comp (PT.pair (PT.const 0) PT.id) h).of_eq fun l => by simp [foldS_sum]

@[fun_prop] theorem PT.fp_sum {α : Type} [Rep α] {f : α → List ℕ} (hf : PT f) :
    PT fun x => (f x).sum := PT.comp hf PT.sumU

theorem enc_tail_le {α : Type} [Rep α] (l : List α) : (enc l.tail).length ≤ (enc l).length := by
  cases l with
  | nil => simp
  | cons a l => rw [List.tail_cons, enc_cons_length]; omega

theorem foldS_drop {α : Type} (l : List α) (n : ℕ) :
    foldS (fun q : List α × Unit => q.1.tail) l (List.replicate n ()) = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    simp only [foldS, List.foldl_cons] at ih ⊢
    rw [ih]; cases l <;> simp

theorem PT.dropU {α : Type} [Rep α] : PT fun p : List α × ℕ => p.1.drop p.2 := by
  have h := PT.foldl_unif (α := Unit) (step := fun q : List α × Unit => q.1.tail) (by fun_prop) 0
    fun s x => by dsimp only; have := enc_tail_le s; omega
  exact (PT.comp (PT.pair PT.fst (PT.comp PT.snd PT.units)) h).of_eq fun p => foldS_drop _ _

@[fun_prop] theorem PT.fp_drop {α β : Type} [Rep α] [Rep β] {f : α → List β} {g : α → ℕ}
    (hf : PT f) (hg : PT g) : PT fun x => (f x).drop (g x) := PT.comp (PT.pair hf hg) PT.dropU

theorem getD_eq_headD_drop {α : Type} (l : List α) (i : ℕ) (d : α) :
    l.getD i d = (l.drop i).headD d := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih => cases i <;> simp

@[fun_prop] theorem PT.fp_getD {α β : Type} [Rep α] [Rep β] {f : α → List β} {g : α → ℕ}
    {h : α → β} (hf : PT f) (hg : PT g) (hh : PT h) : PT fun x => (f x).getD (g x) (h x) :=
  (PT.fp_headD (PT.fp_drop hf hg) hh).of_eq fun _ => (getD_eq_headD_drop _ _ _).symm

theorem foldS_take {α : Type} (k : ℕ) (acc l : List α) :
    foldS (fun q : (ℕ × List α) × α => if q.1.1 = 0 then q.1 else (q.1.1 - 1, q.1.2 ++ [q.2]))
      (k, acc) l = (k - l.length, acc ++ l.take k) := by
  induction l generalizing k acc with
  | nil => simp [foldS]
  | cons a l ih =>
    simp only [foldS, List.foldl_cons] at ih ⊢
    rcases k with _ | k
    · simp only [if_true]
      rw [show ((0 : ℕ), acc) = (0, acc) from rfl, ih]; simp
    · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      rw [ih]; simp

theorem PT.takeU {α : Type} [Rep α] : PT fun p : List α × ℕ => p.1.take p.2 := by
  have h := PT.foldl_unif (α := α) (step := fun q : (ℕ × List α) × α =>
    if q.1.1 = 0 then q.1 else (q.1.1 - 1, q.1.2 ++ [q.2])) (by fun_prop) 3 fun s x => by
    obtain ⟨k, acc⟩ := s
    dsimp only
    split_ifs
    · omega
    · have := enc_append_length acc [x]
      simp only [enc_pair_length, enc_nat_length, enc_cons_length, enc_nil, List.length_cons,
        List.length_nil] at this ⊢
      omega
  exact (PT.comp (PT.pair (PT.pair PT.snd (PT.const [])) PT.fst) (PT.comp h PT.snd)).of_eq
    fun p => by simp [foldS_take]

@[fun_prop] theorem PT.fp_take {α β : Type} [Rep α] [Rep β] {f : α → List β} {g : α → ℕ}
    (hf : PT f) (hg : PT g) : PT fun x => (f x).take (g x) := PT.comp (PT.pair hf hg) PT.takeU

theorem foldS_filter {α γ : Type} (p : γ × α → Bool) (c : γ) (acc l : List α) :
    foldS (fun q : (γ × List α) × α => (q.1.1, if p (q.1.1, q.2) then q.1.2 ++ [q.2] else q.1.2))
      (c, acc) l = (c, acc ++ l.filter fun a => p (c, a)) := by
  induction l generalizing acc with
  | nil => simp [foldS]
  | cons a l ih =>
    simp only [foldS, List.foldl_cons] at ih ⊢
    rw [ih, List.filter_cons]
    split_ifs <;> simp

theorem PT.filterU {α γ : Type} [Rep α] [Rep γ] {p : γ × α → Bool} (hp : PT p) :
    PT fun q : γ × List α => q.2.filter fun a => p (q.1, a) := by
  have h := PT.foldl_unif (α := α) (step := fun q : (γ × List α) × α =>
    (q.1.1, if p (q.1.1, q.2) then q.1.2 ++ [q.2] else q.1.2)) (by fun_prop) 3 fun s x => by
    obtain ⟨c, acc⟩ := s
    dsimp only
    split_ifs
    · have := enc_append_length acc [x]
      simp only [enc_pair_length, enc_cons_length, enc_nil, List.length_cons,
        List.length_nil] at this ⊢
      omega
    · omega
  exact (PT.comp (PT.pair (PT.pair PT.fst (PT.const [])) PT.snd) (PT.comp h PT.snd)).of_eq
    fun q => by simp [foldS_filter]

@[fun_prop] theorem PT.fp_filter {β δ : Type} [Rep β] [Rep δ] {p : δ → β → Bool}
    {l : δ → List β} (hp : PT fun q : δ × β => p q.1 q.2) (hl : PT l) :
    PT fun x => (l x).filter (p x) :=
  (PT.comp (PT.pair PT.id hl) (PT.filterU hp)).of_eq fun _ => rfl

theorem foldS_all {α γ : Type} (p : γ × α → Bool) (c : γ) (b : Bool) (l : List α) :
    foldS (fun q : (γ × Bool) × α => (q.1.1, q.1.2 && p (q.1.1, q.2))) (c, b) l =
      (c, b && l.all fun a => p (c, a)) := by
  induction l generalizing b with
  | nil => simp [foldS]
  | cons a l ih =>
    simp only [foldS, List.foldl_cons] at ih ⊢
    rw [ih]; simp [Bool.and_assoc]

theorem PT.allU {α γ : Type} [Rep α] [Rep γ] {p : γ × α → Bool} (hp : PT p) :
    PT fun q : γ × List α => q.2.all fun a => p (q.1, a) := by
  have h := PT.foldl_unif (α := α) (step := fun q : (γ × Bool) × α =>
    (q.1.1, q.1.2 && p (q.1.1, q.2))) (by fun_prop) 2 fun s x => by
    obtain ⟨c, b⟩ := s
    dsimp only
    have h₁ := enc_bool_length (b && p (c, x))
    have h₂ : 1 ≤ (enc b).length := length_enc_pos b
    simp only [enc_pair_length]
    omega
  exact (PT.comp (PT.pair (PT.pair PT.fst (PT.const true)) PT.snd) (PT.comp h PT.snd)).of_eq
    fun q => by simp [foldS_all]

@[fun_prop] theorem PT.fp_all {β δ : Type} [Rep β] [Rep δ] {p : δ → β → Bool}
    {l : δ → List β} (hp : PT fun q : δ × β => p q.1 q.2) (hl : PT l) :
    PT fun x => (l x).all (p x) :=
  (PT.comp (PT.pair PT.id hl) (PT.allU hp)).of_eq fun _ => rfl

/-! ### Folds with input-dependent initial data -/

/-- **Folds, general form.** The initial state and the list are computed from the input `a`, and
the intermediate states need only be bounded along these inputs. -/
theorem PT.foldl_gen {α β ι : Type} [Rep α] [Rep β] [Rep ι] {step : β × α → β} {s : ι → β}
    {xs : ι → List α} (hstep : PT step) (hs : PT s) (hxs : PT xs)
    (hB : ∃ B : Polynomial ℕ, ∀ a k,
      (enc (foldS step (s a) ((xs a).take k))).length ≤ B.eval (enc a).length) :
    PT fun a => foldS step (s a) (xs a) := by
  obtain ⟨B₁, p, hp⟩ := hstep
  obtain ⟨B, hB⟩ := hB
  obtain ⟨B₀, P, hP⟩ := PT.pair hs hxs
  refine ⟨compB B₀ (foldB B₁), P * (p.comp (1 + B + P) + 4 * B + 4 * P + 14) + 3 * B + 7 * P + 14,
    fun a => ?_⟩
  obtain ⟨hlP, t₀, ht₀, h₀⟩ := hP a
  set y := enc (s a, xs a) with hy
  have hxs' : (xs a).length ≤ P.eval (enc a).length := by
    have := length_lt_enc_list (xs a)
    have : (enc (xs a)).length ≤ y.length := by rw [hy, enc_pair_length]; omega
    omega
  have hs' : (enc (s a)).length ≤ P.eval (enc a).length := by
    have : (enc (s a)).length ≤ y.length := by rw [hy, enc_pair_length]; omega
    omega
  have hsf : (enc (foldS step (s a) (xs a))).length ≤ B.eval (enc a).length := by
    have := hB a (xs a).length
    rwa [List.take_length] at this
  set U := p.eval (1 + B.eval (enc a).length + P.eval (enc a).length) + 4 * B.eval (enc a).length + 4 * P.eval (enc a).length + 13 with hU
  have hok := foldOK_of step (fun s x => ∃ t, t + 2 * (enc (step (s, x))).length +
        2 * (enc s).length + 4 * (enc x).length + 13 ≤ U ∧
        B₁.Computes (enc (s, x)) (enc (step (s, x))) t) (xs a) (s a) (fun k x hx => by
    obtain ⟨_, t, ht, h⟩ := hp (foldS step (s a) ((xs a).take k), x)
    refine ⟨t, ?_, h⟩
    have h₁ := hB a k
    have h₂ := hB a (k + 1)
    rw [foldS_take_succ step (s a) (xs a) k x hx] at h₂
    have h₃ := enc_get_lt (xs a) k x hx
    have h₄ : (enc (xs a)).length ≤ P.eval (enc a).length := by
      have : (enc (xs a)).length ≤ y.length := by rw [hy, enc_pair_length]; omega
      omega
    have h₅ : p.eval (enc (foldS step (s a) ((xs a).take k), x)).length ≤
        p.eval (1 + B.eval (enc a).length + P.eval (enc a).length) := by
      apply ShiQIP.TMComp.eval_mono
      rw [enc_pair_length]
      omega
    omega)
  obtain ⟨t, ht, h⟩ := foldB_computes B₁ step U (s a) (xs a) hok
  refine ⟨?_, _, ?_, compB_computes h₀ h⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    omega
  · have hm : (xs a).length * (U + 1) ≤ P.eval (enc a).length * (U + 1) := Nat.mul_le_mul_right _ hxs'
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_comp, Polynomial.eval_one]
    have e : P.eval (enc a).length * (p.eval (1 + B.eval (enc a).length + P.eval (enc a).length) + 4 * B.eval (enc a).length + 4 * P.eval (enc a).length + 14) =
        P.eval (enc a).length * (U + 1) := by rw [hU]
    rw [e]
    have : y.length ≤ P.eval (enc a).length := hlP
    omega

/-! ### Ranges, replication, zips, parity -/

theorem enc_list_le {α : Type} [Rep α] (l : List α) (c : ℕ) (h : ∀ x ∈ l, (enc x).length ≤ c) :
    (enc l).length ≤ l.length * (c + 1) + 1 := by
  induction l with
  | nil => simp [enc_nil]
  | cons a l ih =>
    rw [enc_cons_length, List.length_cons]
    have h₁ := h a (by simp)
    have h₂ := ih fun x hx => h x (by simp [hx])
    nlinarith

theorem foldS_range (k : ℕ) (acc : List ℕ) (n : ℕ) :
    foldS (fun q : (ℕ × List ℕ) × Unit => (q.1.1 + 1, q.1.2 ++ [q.1.1])) (k, acc)
      (List.replicate n ()) = (k + n, acc ++ List.range' k n) := by
  induction n generalizing k acc with
  | zero => simp [foldS]
  | succ n ih =>
    rw [List.replicate_succ]
    simp only [foldS, List.foldl_cons] at ih ⊢
    rw [ih]; simp [List.range'_succ]; ring

theorem PT.rangeU : PT fun n : ℕ => List.range n := by
  have hstep : PT fun q : (ℕ × List ℕ) × Unit => (q.1.1 + 1, q.1.2 ++ [q.1.1]) := by fun_prop
  have h := PT.foldl_gen (s := fun _ : ℕ => ((0 : ℕ), ([] : List ℕ)))
    (xs := fun n => List.replicate n ()) hstep (by fun_prop) PT.units
    ⟨Polynomial.X * Polynomial.X + 4 * Polynomial.X + 4, fun n k => by
      rw [List.take_replicate, foldS_range]
      simp only [enc_pair_length, enc_nat_length, zero_add, List.nil_append]
      have h₁ := enc_list_le (List.range' 0 (min k n)) (2 * n + 1) fun x hx => by
        rw [enc_nat_length]; simp [List.mem_range'] at hx; omega
      simp only [List.length_range'] at h₁
      have h₂ : min k n * (2 * n + 1 + 1) ≤ n * (2 * n + 2) := Nat.mul_le_mul (min_le_right _ _) le_rfl
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      nlinarith [min_le_right k n]⟩
  exact (PT.comp h PT.snd).of_eq fun n => by simp [foldS_range, List.range_eq_range']

@[fun_prop] theorem PT.fp_range {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) :
    PT fun x => List.range (f x) := PT.comp hf PT.rangeU

theorem foldS_replicate {α : Type} (a : α) (acc : List α) (n : ℕ) :
    foldS (fun q : (α × List α) × Unit => (q.1.1, q.1.1 :: q.1.2)) (a, acc) (List.replicate n ()) =
      (a, List.replicate n a ++ acc) := by
  induction n generalizing acc with
  | zero => simp [foldS]
  | succ n ih =>
    rw [List.replicate_succ]
    simp only [foldS, List.foldl_cons] at ih ⊢
    rw [ih]; simp [List.replicate_succ']

theorem PT.replicateU {α : Type} [Rep α] : PT fun p : ℕ × α => List.replicate p.1 p.2 := by
  have hstep : PT fun q : (α × List α) × Unit => (q.1.1, q.1.1 :: q.1.2) := by fun_prop
  have h := PT.foldl_gen (s := fun p : ℕ × α => (p.2, ([] : List α)))
    (xs := fun p => List.replicate p.1 ()) hstep (by fun_prop) (PT.comp PT.fst PT.units)
    ⟨Polynomial.X * Polynomial.X + 2 * Polynomial.X + 2, fun ⟨n, a⟩ k => by
      rw [List.take_replicate, foldS_replicate]
      simp only [enc_pair_length, enc_nat_length, List.append_nil]
      have h₁ := enc_list_le (List.replicate (min k n) a) (enc a).length fun x hx => by
        rw [(List.eq_of_mem_replicate hx)]
      simp only [List.length_replicate] at h₁
      have h₂ : min k n * ((enc a).length + 1) ≤ (2 * n + 1 + (enc a).length + 1) *
          (2 * n + 1 + (enc a).length + 1) := by
        apply Nat.mul_le_mul <;> omega
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      nlinarith⟩
  exact (PT.comp h PT.snd).of_eq fun p => by simp [foldS_replicate]

@[fun_prop] theorem PT.fp_replicate {α β : Type} [Rep α] [Rep β] {f : α → ℕ} {g : α → β}
    (hf : PT f) (hg : PT g) : PT fun x => List.replicate (f x) (g x) :=
  PT.comp (PT.pair hf hg) PT.replicateU

theorem foldS_parity (b : Bool) (n : ℕ) :
    foldS (fun q : Bool × Unit => !q.1) b (List.replicate n ()) = (b ^^ decide (n % 2 = 1)) := by
  induction n generalizing b with
  | zero => simp [foldS]
  | succ n ih =>
    rw [List.replicate_succ]
    simp only [foldS, List.foldl_cons] at ih ⊢
    rw [ih]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h, Nat.succ_mod_two_eq_one_iff]

theorem PT.oddU : PT fun n : ℕ => decide (n % 2 = 1) := by
  have h := PT.foldl_unif (α := Unit) (step := fun q : Bool × Unit => !q.1) (by fun_prop) 2
    fun s _ => by
      dsimp only
      have h₁ := enc_bool_length (!s)
      have h₂ : 1 ≤ (enc s).length := length_enc_pos s
      omega
  exact (PT.comp (PT.pair (PT.const false) PT.units) h).of_eq fun n => by
    simp [foldS_parity]

@[fun_prop] theorem PT.fp_mod2 {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) :
    PT fun x => f x % 2 :=
  (PT.fp_ite (PT.comp hf PT.oddU) (PT.const 1) (PT.const 0)).of_eq fun x => by
    rcases Nat.mod_two_eq_zero_or_one (f x) with h | h <;> simp [h]

theorem foldS_zip {α β : Type} [Inhabited β] (r : List β) (acc : List (α × β)) (l : List α) :
    foldS (fun q : (List β × List (α × β)) × α =>
      (q.1.1.tail, if q.1.1.isEmpty then q.1.2 else q.1.2 ++ [(q.2, q.1.1.headD default)]))
      (r, acc) l = (r.drop l.length, acc ++ l.zip r) := by
  induction l generalizing r acc with
  | nil => simp [foldS]
  | cons x l ih =>
    simp only [foldS, List.foldl_cons] at ih ⊢
    rcases r with _ | ⟨y, r⟩
    · simp only [List.tail_nil, List.isEmpty_nil, if_true]
      rw [ih]; simp
    · simp only [List.tail_cons, List.isEmpty_cons, Bool.false_eq_true, if_false, List.headD_cons]
      rw [ih]; simp

theorem enc_zip_le {α β : Type} [Rep α] [Rep β] :
    ∀ (l : List α) (r : List β), (enc (l.zip r)).length ≤ (enc l).length + (enc r).length
  | [], _ => by simp [enc_nil]
  | _ :: _, [] => by simp [enc_nil]
  | x :: l, y :: r => by
    have := enc_zip_le l r
    simp only [List.zip_cons_cons, enc_cons_length, enc_pair_length]
    omega

theorem enc_drop_le {α : Type} [Rep α] (l : List α) (n : ℕ) :
    (enc (l.drop n)).length ≤ (enc l).length := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    cases l with
    | nil => simp
    | cons a l => rw [List.drop_succ_cons]; have := ih l; rw [enc_cons_length]; omega

theorem enc_take_le {α : Type} [Rep α] (l : List α) (n : ℕ) :
    (enc (l.take n)).length ≤ (enc l).length := by
  induction n generalizing l with
  | zero => cases l <;> simp [enc_nil, enc_cons_length]
  | succ n ih =>
    cases l with
    | nil => simp
    | cons a l => rw [List.take_succ_cons, enc_cons_length, enc_cons_length]; have := ih l; omega

theorem zipWith_eq_map_zip' {α β γ : Type} (h : α → β → γ) :
    ∀ (l : List α) (r : List β), List.zipWith h l r = (l.zip r).map fun p => h p.1 p.2
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: l, b :: r => by simp [zipWith_eq_map_zip' h l r]

theorem PT.zipU {α β : Type} [Rep α] [Rep β] [Inhabited β] :
    PT fun p : List α × List β => p.1.zip p.2 := by
  have hstep : PT fun q : (List β × List (α × β)) × α =>
      (q.1.1.tail, if q.1.1.isEmpty then q.1.2 else q.1.2 ++ [(q.2, q.1.1.headD default)]) := by
    fun_prop
  have h := PT.foldl_gen (s := fun p : List α × List β => (p.2, ([] : List (α × β))))
    (xs := fun p => p.1) hstep (by fun_prop) (by fun_prop)
    ⟨3 * Polynomial.X + 2, fun ⟨l, r⟩ k => by
      rw [foldS_zip]
      simp only [enc_pair_length, List.nil_append]
      have h₁ := enc_drop_le r (List.take k l).length
      have h₂ := enc_zip_le (List.take k l) r
      have h₃ := enc_take_le l k
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega⟩
  exact (PT.comp h PT.snd).of_eq fun p => by
    show (foldS _ (p.2, []) p.1).2 = _
    rw [foldS_zip]; simp

@[fun_prop] theorem PT.fp_zip {α β γ : Type} [Rep α] [Rep β] [Rep γ] [Inhabited β]
    {f : γ → List α} {g : γ → List β} (hf : PT f) (hg : PT g) : PT fun x => (f x).zip (g x) :=
  PT.comp (PT.pair hf hg) PT.zipU

@[fun_prop] theorem PT.fp_zipWith {α β γ δ : Type} [Rep α] [Rep β] [Rep γ] [Rep δ] [Inhabited β]
    {h : δ → α → β → γ} {f : δ → List α} {g : δ → List β}
    (hh : PT fun q : δ × (α × β) => h q.1 q.2.1 q.2.2) (hf : PT f) (hg : PT g) :
    PT fun x => List.zipWith (h x) (f x) (g x) :=
  (PT.fp_map (h := fun x (p : α × β) => h x p.1 p.2) hh (PT.fp_zip hf hg)).of_eq fun x => by
    rw [zipWith_eq_map_zip']


/-! ### Multiplication -/

theorem foldS_mul (s m n : ℕ) :
    foldS (fun q : (ℕ × ℕ) × Unit => (q.1.1 + q.1.2, q.1.2)) (s, m) (List.replicate n ()) =
      (s + m * n, m) := by
  induction n generalizing s with
  | zero => simp [foldS]
  | succ n ih =>
    rw [List.replicate_succ]
    simp only [foldS, List.foldl_cons] at ih ⊢
    rw [ih]; congr 1; ring

theorem PT.mulU : PT fun p : ℕ × ℕ => p.1 * p.2 := by
  have h := PT.foldl_gen (s := fun p : ℕ × ℕ => ((0 : ℕ), p.1))
    (xs := fun p => List.replicate p.2 ()) (step := fun q : (ℕ × ℕ) × Unit => (q.1.1 + q.1.2, q.1.2))
    (by fun_prop) (by fun_prop) (PT.comp PT.snd PT.units)
    ⟨Polynomial.X * Polynomial.X + Polynomial.X + 3, fun ⟨m, n⟩ k => by
      rw [List.take_replicate, foldS_mul]
      simp only [enc_pair_length, enc_nat_length, zero_add]
      have h₁ : m * min k n ≤ m * n := Nat.mul_le_mul_left _ (min_le_right _ _)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      nlinarith⟩
  exact (PT.comp h PT.fst).of_eq fun p => by simp [foldS_mul]

@[fun_prop] theorem PT.fp_mul {α : Type} [Rep α] {f g : α → ℕ} (hf : PT f) (hg : PT g) :
    PT fun x => f x * g x := PT.comp (PT.pair hf hg) PT.mulU

end ShiQIP.Uniform
