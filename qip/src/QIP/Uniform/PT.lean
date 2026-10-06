import QIP.Uniform.Glue


/-!
# Q34 — polynomial-time functions on tree-encoded data

* `Rep α`: a representation `toV : α → V` of the values of `α` as binary trees; `enc a` is the
  preorder code of `toV a`, a Boolean string.
* `BM`: a bundled machine (finite stacks, all with alphabet `Bool`, a finite state type, an
  input stack and an output stack). `B.Computes x y t`: started on `x` (all other stacks empty,
  initial state), `B` halts after exactly `t` steps with `y` on its output stack, every other
  stack empty, and the initial state.
* `PT f`: some `BM` computes `enc a ↦ enc (f a)`, and one polynomial bounds both the running
  time and the output length in the input length.

Closure: `PT.ofEnc` (re-encodings with the same code, e.g. `id`), `PT.comp`.
-/

namespace ShiQIP.Uniform

open Turing

/-! ### Tree representations -/

/-- A representation of the values of `α` as binary trees. -/
class Rep (α : Type) where
  toV : α → V

/-- The Boolean code of a value. -/
def enc {α : Type} [Rep α] (a : α) : List Bool := (Rep.toV a).code

instance : Rep V := ⟨id⟩

instance {α β : Type} [Rep α] [Rep β] : Rep (α × β) :=
  ⟨fun p => .node (Rep.toV p.1) (Rep.toV p.2)⟩

/-- Naturals as right spines. -/
def natV : ℕ → V
  | 0 => .leaf
  | n + 1 => .node .leaf (natV n)

instance : Rep ℕ := ⟨natV⟩

instance : Rep Bool := ⟨fun b => if b then .node .leaf .leaf else .leaf⟩

instance : Rep Unit := ⟨fun _ => .leaf⟩

/-- Lists as right spines of their items. -/
def listV {α : Type} [Rep α] : List α → V
  | [] => .leaf
  | a :: l => .node (Rep.toV a) (listV l)

instance {α : Type} [Rep α] : Rep (List α) := ⟨listV⟩

theorem enc_pair {α β : Type} [Rep α] [Rep β] (a : α) (b : β) :
    enc (a, b) = true :: (enc a ++ enc b) := rfl

theorem enc_nil {α : Type} [Rep α] : enc ([] : List α) = [false] := rfl

theorem enc_cons {α : Type} [Rep α] (a : α) (l : List α) :
    enc (a :: l) = true :: (enc a ++ enc l) := rfl

theorem enc_zero : enc (0 : ℕ) = [false] := rfl

theorem enc_succ (n : ℕ) : enc (n + 1) = true :: false :: enc n := rfl

theorem enc_false : enc false = [false] := rfl

theorem enc_true : enc true = [true, false, false] := rfl

theorem length_enc_pos {α : Type} [Rep α] (a : α) : 0 < (enc a).length := by
  unfold enc; cases Rep.toV a <;> simp [V.code]

/-! ### Bundled machines -/

/-- A bundled machine over Boolean stacks. -/
structure BM where
  K : Type
  [dK : DecidableEq K]
  [fK : Fintype K]
  σ : Type
  [fσ : Fintype σ]
  init : σ
  M : Mach K σ
  i : K
  o : K

attribute [instance] BM.dK BM.fK BM.fσ

/-- Stacks with `x` on stack `k` and every other stack empty. -/
def one {K : Type} [DecidableEq K] (k : K) (x : List Bool) : K → List Bool :=
  Function.update (fun _ => []) k x

/-- `B` turns `x` into `y` in exactly `t` steps. -/
def BM.Computes (B : BM) (x y : List Bool) (t : ℕ) : Prop :=
  Runs B.M B.init (one B.i x) B.init (one B.o y) t

/-- **Polynomial-time computable** functions between tree-represented types. -/
def PT {α β : Type} [Rep α] [Rep β] (f : α → β) : Prop :=
  ∃ (B : BM) (p : Polynomial ℕ), ∀ a, (enc (f a)).length ≤ p.eval (enc a).length ∧
    ∃ t ≤ p.eval (enc a).length, B.Computes (enc a) (enc (f a)) t

theorem one_inl {K₀ K₁ : Type} [DecidableEq K₀] [DecidableEq K₁] (k : K₀) (x : List Bool) :
    one (Sum.inl k : K₀ ⊕ K₁) x = Sum.elim (one k x) (fun _ => []) := by
  funext k'
  rcases k' with k' | k' <;> simp [one, Function.update_apply]

theorem one_inr {K₀ K₁ : Type} [DecidableEq K₀] [DecidableEq K₁] (k : K₁) (x : List Bool) :
    one (Sum.inr k : K₀ ⊕ K₁) x = Sum.elim (fun _ => []) (one k x) := by
  funext k'
  rcases k' with k' | k' <;> simp [one, Function.update_apply]

/-! ### Re-encodings -/

/-- The machine that copies its input to its output. -/
def castM : BM where
  K := Fin 3
  σ := Option Bool × Unit
  init := (none, ())
  M := seq (moveAll 0 1) (moveAll 1 2)
  i := 0
  o := 2

theorem castM_computes (x : List Bool) : castM.Computes x x (4 * x.length + 4) := by
  have h₁ := runs_moveAll (τ := Unit) (0 : Fin 3) 1 (by decide) none () (one 0 x)
  have h₂ := runs_moveAll (τ := Unit) (1 : Fin 3) 2 (by decide) none () (Function.update
    (Function.update (one 0 x) 0 []) 1 ((one 0 x 0).reverse ++ one 0 x 1))
  refine (runs_seq h₁ h₂).of_eq rfl ?_ ?_
  · funext k
    fin_cases k <;> simp [one, castM, Function.update]
  · simp [one]; ring

/-- A function whose output code equals its input code is polynomial time. -/
theorem PT.ofEnc {α β : Type} [Rep α] [Rep β] {f : α → β} (h : ∀ a, enc (f a) = enc a) :
    PT f := by
  refine ⟨castM, 4 * Polynomial.X + 4, fun a => ⟨?_, 4 * (enc a).length + 4, ?_, ?_⟩⟩
  · simp [h]; omega
  · simp
  · rw [h]; exact castM_computes _

theorem PT.id {α : Type} [Rep α] : PT (id : α → α) := PT.ofEnc fun _ => rfl

/-! ### Two sub-machines -/

section Two

variable {Own K₁ K₂ σ₁ σ₂ : Type} [DecidableEq Own] [DecidableEq K₁] [DecidableEq K₂]

/-- The first sub-machine, inside `Own ⊕ (K₁ ⊕ K₂)` with states `Option Bool × (σ₁ × σ₂)`. -/
def lift1 (M : Mach K₁ σ₁) : Mach (Own ⊕ (K₁ ⊕ K₂)) (Option Bool × (σ₁ × σ₂)) :=
  Mach.vR (Mach.vL (Mach.sR (Mach.sL M)))

/-- The second sub-machine. -/
def lift2 (M : Mach K₂ σ₂) : Mach (Own ⊕ (K₁ ⊕ K₂)) (Option Bool × (σ₁ × σ₂)) :=
  Mach.vR (Mach.vR (Mach.sR (Mach.sR M)))

theorem runs_lift1 {M : Mach K₁ σ₁} {v v' : σ₁} {S S' : K₁ → List Bool} {t : ℕ}
    (h : Runs M v S v' S' t) (U : Own → List Bool) (T : K₂ → List Bool) (o : Option Bool)
    (w : σ₂) :
    Runs (lift1 (Own := Own) (K₂ := K₂) M) (o, (v, w)) (Sum.elim U (Sum.elim S T)) (o, (v', w))
      (Sum.elim U (Sum.elim S' T)) t :=
  runs_vR (runs_vL (runs_sR (runs_sL h T) U) w) o

theorem runs_lift2 {M : Mach K₂ σ₂} {v v' : σ₂} {S S' : K₂ → List Bool} {t : ℕ}
    (h : Runs M v S v' S' t) (U : Own → List Bool) (T : K₁ → List Bool) (o : Option Bool)
    (w : σ₁) :
    Runs (lift2 (Own := Own) (K₁ := K₁) M) (o, (w, v)) (Sum.elim U (Sum.elim T S)) (o, (w, v'))
      (Sum.elim U (Sum.elim T S')) t :=
  runs_vR (runs_vR (runs_sR (runs_sR h T) U) w) o

end Two

/-! ### Composition -/

/-- Run `B₁`, move its output to the input of `B₂` (twice, to keep the order), run `B₂`. -/
def compB (B₁ B₂ : BM) : BM where
  K := Unit ⊕ (B₁.K ⊕ B₂.K)
  σ := Option Bool × (B₁.σ × B₂.σ)
  init := (none, (B₁.init, B₂.init))
  M := seq (lift1 B₁.M) (seq (moveAll (.inr (.inl B₁.o)) (.inl ()))
    (seq (moveAll (.inl ()) (.inr (.inr B₂.i))) (lift2 B₂.M)))
  i := .inr (.inl B₁.i)
  o := .inr (.inr B₂.o)

theorem compB_stk₁ {A B : Type} [DecidableEq A] [DecidableEq B] (a : A) (y : List Bool) :
    (Function.update (Function.update (Sum.elim (fun _ => []) (Sum.elim (one a y) fun _ => []) :
      Unit ⊕ (A ⊕ B) → List Bool) (.inr (.inl a)) []) (.inl ()) (y.reverse ++ [])) =
    Sum.elim (fun _ => y.reverse) (fun _ => []) := by
  funext k
  rcases k with k | k | k
  · simp only [Function.update_apply, Sum.elim_inl, reduceCtorEq, if_false, if_true, List.append_nil]
  · simp only [one, Function.update_apply, Sum.elim_inr, reduceCtorEq, if_false, Sum.inr.injEq,
      Sum.inl.injEq]
    split_ifs <;> simp_all
  · simp only [Function.update_apply, Sum.elim_inr, reduceCtorEq, if_false, ite_self]

theorem compB_stk₂ {A B : Type} [DecidableEq A] [DecidableEq B] (b : B) (y : List Bool) :
    (Function.update (Function.update (Sum.elim (fun _ => y.reverse) (fun _ => []) :
      Unit ⊕ (A ⊕ B) → List Bool) (.inl ()) []) (.inr (.inr b)) (y.reverse.reverse ++ [])) =
    Sum.elim (fun _ => []) (Sum.elim (fun _ => []) (one b y)) := by
  funext k
  rcases k with k | k | k <;>
    simp only [one, Function.update_apply, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false,
      if_true, List.append_nil, List.reverse_reverse, Sum.inr.injEq]

theorem compB_computes {B₁ B₂ : BM} {x y z : List Bool} {t₁ t₂ : ℕ} (h₁ : B₁.Computes x y t₁)
    (h₂ : B₂.Computes y z t₂) :
    (compB B₁ B₂).Computes x z (t₂ + (2 * y.length + 2) + (2 * y.length + 2) + t₁) := by
  have r₁ := runs_lift1 (Own := Unit) (K₂ := B₂.K) h₁ (fun _ => []) (fun _ => []) none B₂.init
  have r₂ := runs_moveAll (τ := B₁.σ × B₂.σ) (.inr (.inl B₁.o) : Unit ⊕ (B₁.K ⊕ B₂.K)) (.inl ())
    (by simp) none (B₁.init, B₂.init) (Sum.elim (fun _ => []) (Sum.elim (one B₁.o y) fun _ => []))
  have r₃ := runs_moveAll (τ := B₁.σ × B₂.σ) (.inl () : Unit ⊕ (B₁.K ⊕ B₂.K)) (.inr (.inr B₂.i))
    (by simp) none (B₁.init, B₂.init) (Sum.elim (fun _ => y.reverse) (fun _ => []))
  have r₄ := runs_lift2 (Own := Unit) (K₁ := B₁.K) h₂ (fun _ => []) (fun _ => []) none B₁.init
  have e₁ : (Sum.elim (fun _ => []) (Sum.elim (one B₁.o y) fun _ => []) :
      Unit ⊕ (B₁.K ⊕ B₂.K) → List Bool) (.inr (.inl B₁.o)) = y := by
    simp only [Sum.elim_inr, Sum.elim_inl, one, Function.update_self]
  rw [e₁, Sum.elim_inl] at r₂
  rw [Sum.elim_inl, Sum.elim_inr, List.length_reverse] at r₃
  rw [compB_stk₁] at r₂
  rw [compB_stk₂] at r₃
  have r := runs_seq r₁ (runs_seq r₂ (runs_seq r₃ r₄))
  refine (r.of_eq rfl ?_ (by ring)).of_eq₀ ?_
  · exact ((one_inr _ _).trans (congrArg _ (one_inr _ _))).symm
  · exact ((one_inr _ _).trans (congrArg _ (one_inl _ _))).symm

theorem PT.comp {α β γ : Type} [Rep α] [Rep β] [Rep γ] {f : α → β} {g : β → γ} (hf : PT f)
    (hg : PT g) : PT (g ∘ f) := by
  obtain ⟨B₁, p, hp⟩ := hf
  obtain ⟨B₂, q, hq⟩ := hg
  refine ⟨compB B₁ B₂, q.comp p + 5 * p + 4, fun a => ?_⟩
  obtain ⟨hl₁, t₁, ht₁, h₁⟩ := hp a
  obtain ⟨hl₂, t₂, ht₂, h₂⟩ := hq (f a)
  have m₁ := ShiQIP.TMComp.eval_mono q hl₁
  refine ⟨?_, _, ?_, compB_computes h₁ h₂⟩
  · simp only [Function.comp_apply, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
      Polynomial.eval_ofNat]
    omega
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_ofNat]
    omega

/-- Composition, written with a lambda. -/
theorem PT.comp' {α β γ : Type} [Rep α] [Rep β] [Rep γ] {f : α → β} {g : β → γ} (hg : PT g)
    (hf : PT f) : PT fun a => g (f a) := PT.comp hf hg

/-! ### Pairing -/

/-- Three own stacks. -/
inductive Slot where
  | a
  | b
  | c
  deriving DecidableEq

instance : Fintype Slot := ⟨{.a, .b, .c}, by intro x; cases x <;> simp⟩

/-- Contents of the three own stacks. -/
def slot3 (A B C : List Bool) : Slot → List Bool
  | .a => A
  | .b => B
  | .c => C

/-- Stack equalities in the layout `Slot ⊕ (K₁ ⊕ K₂)`. -/
macro "stk_tac" : tactic => `(tactic| (
  funext k
  rcases k with (_ | _ | _) | k | k <;>
    simp only [Function.update_apply, Sum.elim_inl, Sum.elim_inr, slot3, one, reduceCtorEq,
      if_false, if_true, ite_self, Sum.inl.injEq, Sum.inr.injEq, List.append_nil, List.nil_append,
      List.reverse_reverse, List.reverse_nil, List.reverse_append, List.append_assoc] <;>
    (try split_ifs) <;> (try simp_all)))

/-- Copy the input to both sub-machines, run both, output `true :: y ++ z`. -/
def pairB (B₁ B₂ : BM) : BM where
  K := Slot ⊕ (B₁.K ⊕ B₂.K)
  σ := Option Bool × (B₁.σ × B₂.σ)
  init := (none, (B₁.init, B₂.init))
  M := seq (moveAll (.inl .a) (.inl .b)) <| seq (moveAll2 (.inl .b) (.inr (.inl B₁.i)) (.inr (.inr B₂.i))) <|
    seq (lift1 B₁.M) <| seq (lift2 B₂.M) <| seq (moveAll (.inr (.inr B₂.o)) (.inl .b)) <|
    seq (moveAll (.inl .b) (.inl .c)) <| seq (moveAll (.inr (.inl B₁.o)) (.inl .b)) <|
    seq (moveAll (.inl .b) (.inl .c)) (basic (.push (.inl .c) (fun _ => true) .halt))
  i := .inl .a
  o := .inl .c

theorem pairB_computes {B₁ B₂ : BM} {x y z : List Bool} {t₁ t₂ : ℕ} (h₁ : B₁.Computes x y t₁)
    (h₂ : B₂.Computes x z t₂) :
    (pairB B₁ B₂).Computes x (true :: (y ++ z))
      (1 + (2 * y.length + 2) + (2 * y.length + 2) + (2 * z.length + 2) + (2 * z.length + 2) +
        t₂ + t₁ + (2 * x.length + 2) + (2 * x.length + 2)) := by
  have r₁ := (runs_moveAll (τ := B₁.σ × B₂.σ) (.inl .a : Slot ⊕ (B₁.K ⊕ B₂.K)) (.inl .b) (by simp)
    none (B₁.init, B₂.init) (Sum.elim (slot3 x [] []) (Sum.elim (fun _ : B₁.K => ([] : List Bool)) (fun _ : B₂.K => ([] : List Bool))))).of_eq rfl
      (show _ = Sum.elim (slot3 [] x.reverse []) (Sum.elim (fun _ : B₁.K => ([] : List Bool)) (fun _ : B₂.K => ([] : List Bool))) by stk_tac) rfl
  have r₂ := (runs_moveAll2 (τ := B₁.σ × B₂.σ) (.inl .b : Slot ⊕ (B₁.K ⊕ B₂.K)) (.inr (.inl B₁.i))
    (.inr (.inr B₂.i)) (by simp) (by simp) (by simp) none (B₁.init, B₂.init)
    (Sum.elim (slot3 [] x.reverse []) (Sum.elim (fun _ : B₁.K => ([] : List Bool)) (fun _ : B₂.K => ([] : List Bool))))).of_eq rfl
      (show _ = Sum.elim (slot3 [] [] []) (Sum.elim (one B₁.i x) (one B₂.i x)) by stk_tac) rfl
  have r₃ := runs_lift1 (Own := Slot) (K₂ := B₂.K) h₁ (slot3 [] [] []) (one B₂.i x) none B₂.init
  have r₄ := runs_lift2 (Own := Slot) (K₁ := B₁.K) h₂ (slot3 [] [] []) (one B₁.o y) none B₁.init
  have r₅ := (runs_moveAll (τ := B₁.σ × B₂.σ) (.inr (.inr B₂.o) : Slot ⊕ (B₁.K ⊕ B₂.K)) (.inl .b)
    (by simp) none (B₁.init, B₂.init) (Sum.elim (slot3 [] [] []) (Sum.elim (one B₁.o y)
      (one B₂.o z)))).of_eq rfl
      (show _ = Sum.elim (slot3 [] z.reverse []) (Sum.elim (one B₁.o y) (fun _ : B₂.K => ([] : List Bool))) by stk_tac) rfl
  have r₆ := (runs_moveAll (τ := B₁.σ × B₂.σ) (.inl .b : Slot ⊕ (B₁.K ⊕ B₂.K)) (.inl .c)
    (by simp) none (B₁.init, B₂.init) (Sum.elim (slot3 [] z.reverse []) (Sum.elim (one B₁.o y)
      (fun _ : B₂.K => ([] : List Bool))))).of_eq rfl
      (show _ = Sum.elim (slot3 [] [] z) (Sum.elim (one B₁.o y) (fun _ : B₂.K => ([] : List Bool))) by stk_tac) rfl
  have r₇ := (runs_moveAll (τ := B₁.σ × B₂.σ) (.inr (.inl B₁.o) : Slot ⊕ (B₁.K ⊕ B₂.K)) (.inl .b)
    (by simp) none (B₁.init, B₂.init) (Sum.elim (slot3 [] [] z) (Sum.elim (one B₁.o y)
      (fun _ : B₂.K => ([] : List Bool))))).of_eq rfl
      (show _ = Sum.elim (slot3 [] y.reverse z) (Sum.elim (fun _ : B₁.K => ([] : List Bool)) (fun _ : B₂.K => ([] : List Bool))) by stk_tac) rfl
  have r₈ := (runs_moveAll (τ := B₁.σ × B₂.σ) (.inl .b : Slot ⊕ (B₁.K ⊕ B₂.K)) (.inl .c)
    (by simp) none (B₁.init, B₂.init) (Sum.elim (slot3 [] y.reverse z) (Sum.elim (fun _ : B₁.K => ([] : List Bool)) (fun _ : B₂.K => ([] : List Bool))))).of_eq rfl
      (show _ = Sum.elim (slot3 [] [] (y ++ z)) (Sum.elim (fun _ : B₁.K => ([] : List Bool)) (fun _ : B₂.K => ([] : List Bool))) by stk_tac) rfl
  have r₉ := runs_basic (K := Slot ⊕ (B₁.K ⊕ B₂.K)) (σ := Option Bool × (B₁.σ × B₂.σ)) (.push (.inl .c) (fun _ => true) .halt)
    (none, (B₁.init, B₂.init)) (Sum.elim (slot3 [] [] (y ++ z)) (Sum.elim (fun _ : B₁.K => ([] : List Bool)) (fun _ : B₂.K => ([] : List Bool)))) rfl
  have r := runs_seq r₁ (runs_seq r₂ (runs_seq r₃ (runs_seq r₄ (runs_seq r₅ (runs_seq r₆
    (runs_seq r₇ (runs_seq r₈ r₉)))))))
  refine (r.of_eq rfl ?_ ?_).of_eq₀ ?_
  · clear r r₁ r₂ r₃ r₄ r₅ r₆ r₇ r₈ r₉ h₁ h₂
    show _ = one (K := Slot ⊕ (B₁.K ⊕ B₂.K)) (Sum.inl Slot.c) _
    simp only [TM2.stepAux]
    stk_tac
  · simp only [Sum.elim_inl, Sum.elim_inr, slot3, one, Function.update_self, List.length_reverse]
  · clear r r₁ r₂ r₃ r₄ r₅ r₆ r₇ r₈ r₉ h₁ h₂
    show _ = one (K := Slot ⊕ (B₁.K ⊕ B₂.K)) (Sum.inl Slot.a) _
    stk_tac

theorem PT.pair {α β γ : Type} [Rep α] [Rep β] [Rep γ] {f : α → β} {g : α → γ} (hf : PT f)
    (hg : PT g) : PT fun a => (f a, g a) := by
  obtain ⟨B₁, p, hp⟩ := hf
  obtain ⟨B₂, q, hq⟩ := hg
  refine ⟨pairB B₁ B₂, 5 * p + 5 * q + 4 * Polynomial.X + 13, fun a => ?_⟩
  obtain ⟨hl₁, t₁, ht₁, h₁⟩ := hp a
  obtain ⟨hl₂, t₂, ht₂, h₂⟩ := hq a
  refine ⟨?_, _, ?_, pairB_computes h₁ h₂⟩
  · simp only [enc_pair, List.length_cons, List.length_append, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    simp only [enc] at hl₁ hl₂ ht₁ ht₂ ⊢
    omega

/-! ### Machines without sub-machines -/

/-- Four registers. -/
inductive Reg where
  | a
  | b
  | c
  | d
  deriving DecidableEq

instance : Fintype Reg := ⟨{.a, .b, .c, .d}, by intro x; cases x <;> simp⟩

/-- Contents of the four registers. -/
def reg4 (A B C D : List Bool) : Reg → List Bool
  | .a => A
  | .b => B
  | .c => C
  | .d => D

/-- Stack equalities over `Reg`. -/
macro "reg_tac" : tactic => `(tactic| (
  funext k
  cases k <;>
    simp only [Function.update_apply, reg4, one, reduceCtorEq, if_false, if_true, ite_self,
      List.append_nil, List.nil_append, List.reverse_reverse, List.reverse_nil, List.reverse_append,
      List.append_assoc, List.cons_append, V.code]))

/-- Sub-free machine on the registers. -/
def regB (M : Mach Reg (Option Bool × Unit)) : BM where
  K := Reg
  σ := Option Bool × Unit
  init := (none, ())
  M := M
  i := .a
  o := .c

theorem regB_computes {M : Mach Reg (Option Bool × Unit)} {x y : List Bool} {t : ℕ}
    (h : Runs M (none, ()) (reg4 x [] [] []) (none, ()) (reg4 [] [] y []) t) :
    (regB M).Computes x y t := by
  refine (h.of_eq rfl ?_ rfl).of_eq₀ ?_
  · show _ = one (K := Reg) .c y
    reg_tac
  · show _ = one (K := Reg) .a x
    reg_tac

/-- Pop twice into the scratch register. -/
def pop2 (r : Reg) : BS Reg Unit (Option Bool × Unit) :=
  .pop r (fun v x => (x, v.2)) (.pop r (fun v x => (x, v.2)) .halt)

/-- The first projection: drop the root, parse the left subtree, drop the rest. -/
def fstM : Mach Reg (Option Bool × Unit) :=
  seq (basic (popTo .a)) <| seq (parseV .a .b .d) <| seq (discard .a) (moveAll .b .c)

theorem fstM_runs (o : Option Bool) (x y : V) :
    Runs fstM (o, ()) (reg4 (V.node x y).code [] [] []) (none, ()) (reg4 [] [] x.code [])
      (2 * x.code.length + 2 + (2 * y.code.length + 2) + (2 * x.code.length + 2) + 1) := by
  have r₁ := runs_basic (popTo (τ := Unit) Reg.a) (o, ()) (reg4 (V.node x y).code [] [] []) rfl
  simp only [popTo, TM2.stepAux, reg4, V.code, List.head?_cons, List.tail_cons] at r₁
  have r₂ := runs_parseV (τ := Unit) Reg.a .b .d (by decide) (by decide) (by decide) (some true) ()
    x y.code (Function.update (reg4 (true :: (x.code ++ y.code)) [] [] []) .a (x.code ++ y.code))
    (by simp) (by simp [reg4])
  have r₃ := runs_discard (τ := Unit) Reg.a none () (reg4 y.code x.code.reverse [] [])
  have r₄ := runs_moveAll (τ := Unit) Reg.b .c (by decide) none () (reg4 [] x.code.reverse [] [])
  have r := runs_seq r₁ (runs_seq (r₂.of_eq rfl (show _ = reg4 y.code x.code.reverse [] [] by reg_tac) rfl)
    (runs_seq (r₃.of_eq rfl (show _ = reg4 [] x.code.reverse [] [] by reg_tac) rfl)
      (r₄.of_eq rfl (show _ = reg4 [] [] x.code [] by reg_tac) rfl)))
  refine (r.of_eq rfl rfl ?_).of_eq₀ (by reg_tac)
  simp only [reg4, List.length_reverse]

/-- The second projection. -/
def sndM : Mach Reg (Option Bool × Unit) :=
  seq (basic (popTo .a)) <| seq (parseV .a .b .d) <| seq (discard .b) <|
    seq (moveAll .a .b) (moveAll .b .c)

theorem sndM_runs (o : Option Bool) (x y : V) :
    Runs sndM (o, ()) (reg4 (V.node x y).code [] [] []) (none, ()) (reg4 [] [] y.code [])
      (2 * y.code.length + 2 + (2 * y.code.length + 2) + (2 * x.code.length + 2) +
        (2 * x.code.length + 2) + 1) := by
  have r₁ := runs_basic (popTo (τ := Unit) Reg.a) (o, ()) (reg4 (V.node x y).code [] [] []) rfl
  simp only [popTo, TM2.stepAux, reg4, V.code, List.head?_cons, List.tail_cons] at r₁
  have r₂ := runs_parseV (τ := Unit) Reg.a .b .d (by decide) (by decide) (by decide) (some true) ()
    x y.code (Function.update (reg4 (true :: (x.code ++ y.code)) [] [] []) .a (x.code ++ y.code))
    (by simp) (by simp [reg4])
  have r₃ := runs_discard (τ := Unit) Reg.b none () (reg4 y.code x.code.reverse [] [])
  have r₄ := runs_moveAll (τ := Unit) Reg.a .b (by decide) none () (reg4 y.code [] [] [])
  have r₅ := runs_moveAll (τ := Unit) Reg.b .c (by decide) none () (reg4 [] y.code.reverse [] [])
  have r := runs_seq r₁ (runs_seq (r₂.of_eq rfl (show _ = reg4 y.code x.code.reverse [] [] by reg_tac) rfl)
    (runs_seq (r₃.of_eq rfl (show _ = reg4 y.code [] [] [] by reg_tac) rfl)
      (runs_seq (r₄.of_eq rfl (show _ = reg4 [] y.code.reverse [] [] by reg_tac) rfl)
        (r₅.of_eq rfl (show _ = reg4 [] [] y.code [] by reg_tac) rfl))))
  refine (r.of_eq rfl rfl ?_).of_eq₀ (by reg_tac)
  simp only [reg4, List.length_reverse]

/-- Push a fixed list (its last element first). -/
def pushL {K σ Λ : Type} (k : K) : List Bool → BS K Λ σ → BS K Λ σ
  | [], q => q
  | b :: l, q => .push k (fun _ => b) (pushL k l q)

theorem stepAux_pushL {K σ Λ : Type} [DecidableEq K] (k : K) (l : List Bool) (q : BS K Λ σ) (v : σ)
    (S : K → List Bool) :
    TM2.stepAux (pushL k l q) v S = TM2.stepAux q v (Function.update S k (l.reverse ++ S k)) := by
  induction l generalizing S with
  | nil => simp [pushL]
  | cons b l ih =>
    simp only [pushL, TM2.stepAux, ih, Function.update_idem, Function.update_self,
      List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Discard the input and write a constant. -/
def constM (w : V) : Mach Reg (Option Bool × Unit) :=
  seq (discard .a) (basic (pushL .c w.code.reverse .halt))

theorem constM_runs (w : V) (x : List Bool) :
    Runs (constM w) (none, ()) (reg4 x [] [] []) (none, ()) (reg4 [] [] w.code [])
      (1 + (2 * x.length + 2)) := by
  have r₁ := runs_discard (τ := Unit) Reg.a none () (reg4 x [] [] [])
  have r₂ := runs_basic (σ := Option Bool × Unit) (pushL Reg.c w.code.reverse .halt) (none, ())
    (reg4 [] [] [] []) (by rw [stepAux_pushL]; rfl)
  simp only [stepAux_pushL, TM2.stepAux] at r₂
  exact runs_seq (r₁.of_eq rfl (show _ = reg4 [] [] [] [] by reg_tac) rfl)
    (r₂.of_eq rfl (show _ = reg4 [] [] w.code [] by reg_tac) rfl)

/-- Select by a Boolean: input `(b, (x, y))`, output `x` if `b` else `y`. -/
def selM : Mach Reg (Option Bool × Unit) :=
  seq (basic (pop2 .a)) (ite (fun v => v.1.getD false) (seq (basic (pop2 .a)) fstM) sndM)

theorem selM_runs_true (x y : V) :
    Runs selM (none, ()) (reg4 (V.node (.node .leaf .leaf) (.node x y)).code [] [] []) (none, ())
      (reg4 [] [] x.code [])
      ((2 * x.code.length + 2 + (2 * y.code.length + 2) + (2 * x.code.length + 2) + 1 + 1) + 1 + 1) := by
  have r₁ := runs_basic (pop2 Reg.a) (none, ())
    (reg4 (V.node (.node .leaf .leaf) (.node x y)).code [] [] []) rfl
  simp only [pop2, TM2.stepAux, reg4, V.code, List.head?_cons, List.tail_cons, List.cons_append,
    List.nil_append, Function.update_self] at r₁
  have r₂ := runs_basic (pop2 Reg.a) (some true, ())
    (Function.update (reg4 [] [] [] []) Reg.a (false :: false :: true :: (x.code ++ y.code))) rfl
  simp only [pop2, TM2.stepAux, Function.update_self, List.head?_cons, List.tail_cons,
    Function.update_idem] at r₂
  have r₃ := fstM_runs (some false) x y
  have r := runs_seq r₁ (runs_ite_true (c := fun v : Option Bool × Unit => v.1.getD false) (M₂ := sndM) rfl (runs_seq (r₂.of_eq₀ (by reg_tac))
    (r₃.of_eq₀ (by reg_tac))))
  exact r.of_eq₀ (by reg_tac)

theorem selM_runs_false (x y : V) :
    Runs selM (none, ()) (reg4 (V.node .leaf (.node x y)).code [] [] []) (none, ())
      (reg4 [] [] y.code [])
      ((2 * y.code.length + 2 + (2 * y.code.length + 2) + (2 * x.code.length + 2) +
        (2 * x.code.length + 2) + 1) + 1 + 1) := by
  have r₁ := runs_basic (pop2 Reg.a) (none, ()) (reg4 (V.node .leaf (.node x y)).code [] [] []) rfl
  simp only [pop2, TM2.stepAux, reg4, V.code, List.head?_cons, List.tail_cons, List.cons_append,
    List.nil_append, Function.update_self] at r₁
  have r₃ := sndM_runs (some false) x y
  have r := runs_seq r₁ (runs_ite_false (c := fun v : Option Bool × Unit => v.1.getD false)
    (M₁ := seq (basic (pop2 .a)) fstM) rfl (r₃.of_eq₀ (by reg_tac)))
  exact r.of_eq₀ (by reg_tac)

/-! ### Projections, constants, selection -/

theorem PT.fst {α β : Type} [Rep α] [Rep β] : PT (Prod.fst : α × β → α) := by
  refine ⟨regB fstM, 6 * Polynomial.X + 7, fun ⟨u, w⟩ => ⟨?_, _, ?_, regB_computes (fstM_runs none _ _)⟩⟩
  · simp only [enc_pair, List.length_cons, List.length_append, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  · simp only [enc_pair, List.length_cons, List.length_append, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    simp only [enc]
    omega

theorem PT.snd {α β : Type} [Rep α] [Rep β] : PT (Prod.snd : α × β → β) := by
  refine ⟨regB sndM, 8 * Polynomial.X + 9, fun ⟨u, w⟩ => ⟨?_, _, ?_, regB_computes (sndM_runs none _ _)⟩⟩
  · simp only [enc_pair, List.length_cons, List.length_append, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  · simp only [enc_pair, List.length_cons, List.length_append, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    simp only [enc]
    omega

theorem PT.const {α β : Type} [Rep α] [Rep β] (c : β) : PT fun _ : α => c := by
  refine ⟨regB (constM (Rep.toV c)), 2 * Polynomial.X + Polynomial.C ((enc c).length + 3),
    fun a => ⟨?_, _, ?_, regB_computes (constM_runs _ _)⟩⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
      Polynomial.eval_C]
    omega
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
      Polynomial.eval_C]
    omega

/-- Selection by a Boolean. -/
def sel {β : Type} (p : Bool × (β × β)) : β := if p.1 then p.2.1 else p.2.2

theorem PT.sel {β : Type} [Rep β] : PT (sel : Bool × (β × β) → β) := by
  refine ⟨regB selM, 8 * Polynomial.X + 9, fun ⟨b, u, w⟩ => ?_⟩
  cases b
  · refine ⟨?_, _, ?_, regB_computes (selM_runs_false _ _)⟩
    · simp only [ShiQIP.Uniform.sel, enc_pair, enc_false, List.length_cons, List.length_append,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      simp
      omega
    · simp only [enc_pair, enc_false, List.length_cons, List.length_append, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      simp only [enc]
      simp
      omega
  · refine ⟨?_, _, ?_, regB_computes (selM_runs_true _ _)⟩
    · simp only [ShiQIP.Uniform.sel, enc_pair, enc_true, List.length_cons, List.length_append,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      simp
      omega
    · simp only [enc_pair, enc_true, List.length_cons, List.length_append, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      simp only [enc]
      simp
      omega

/-- **If-then-else.** -/
theorem PT.ite {α β : Type} [Rep α] [Rep β] {c : α → Bool} {f g : α → β} (hc : PT c)
    (hf : PT f) (hg : PT g) : PT fun a => if c a then f a else g a :=
  PT.comp (PT.pair hc (PT.pair hf hg)) PT.sel

/-! ### Folding over a list -/

section Fold

variable (B₁ : BM)

/-- Peek register `a` into the scratch register. -/
def peekA {K₁ : Type} : BS (Reg ⊕ K₁) Unit (Option Bool × B₁.σ) :=
  .peek (.inl .a) (fun v x => (x, v.2)) .halt

/-- The step machine, inside `Reg ⊕ B₁.K`. -/
def subM : Mach (Reg ⊕ B₁.K) (Option Bool × B₁.σ) := Mach.vR (Mach.sR B₁.M)

/-- One iteration: take the head `x` of the list on `a`, feed `(s, x)` to the step machine (the
state `s` is kept reversed on `b`), store the new state reversed on `b`, peek `a`. -/
def foldBody : Mach (Reg ⊕ B₁.K) (Option Bool × B₁.σ) :=
  seq (basic (popTo (.inl .a))) <| seq (parseV (.inl .a) (.inl .c) (.inl .d)) <|
    seq (moveAll (.inl .c) (.inr B₁.i)) <| seq (moveAll (.inl .b) (.inr B₁.i)) <|
    seq (basic (.push (.inr B₁.i) (fun _ => true) .halt)) <| seq (subM B₁) <|
    seq (moveAll (.inr B₁.o) (.inl .b)) (basic (peekA B₁))

/-- The loop. -/
def foldLoop : Mach (Reg ⊕ B₁.K) (Option Bool × B₁.σ) :=
  loop (fun v => v.1.getD false) (foldBody B₁)

/-- The fold machine: input `(s, xs)`, output `xs.foldl step s`. -/
def foldB : BM where
  K := Reg ⊕ B₁.K
  σ := Option Bool × B₁.σ
  init := (none, B₁.init)
  M := seq (basic (popTo (.inl .a))) <| seq (parseV (.inl .a) (.inl .b) (.inl .d)) <|
    seq (basic (peekA B₁)) <| seq (foldLoop B₁) <| seq (basic (popTo (.inl .a)))
      (moveAll (.inl .b) (.inl .c))
  i := .inl .a
  o := .inl .c

/-- Stack equalities in the layout `Reg ⊕ K₁`. -/
macro "fold_tac" : tactic => `(tactic| (
  clear * -
  funext k
  rcases k with (_ | _ | _ | _) | k <;>
    simp only [Function.update_apply, Sum.elim_inl, Sum.elim_inr, reg4, one, reduceCtorEq,
      if_false, if_true, ite_self, Sum.inl.injEq, Sum.inr.injEq, List.append_nil, List.nil_append,
      List.reverse_reverse, List.reverse_nil, List.reverse_append, List.append_assoc,
      List.cons_append, V.code, enc_pair] <;>
    (try split_ifs) <;> (try simp_all) <;> (try rfl)))

theorem runs_subM {x y : List Bool} {t : ℕ} (h : B₁.Computes x y t) (U : Reg → List Bool)
    (o : Option Bool) :
    Runs (subM B₁) (o, B₁.init) (Sum.elim U (one B₁.i x)) (o, B₁.init) (Sum.elim U (one B₁.o y)) t :=
  runs_vR (runs_sR h U) o

theorem foldBody_runs (X : V) (L S S' : List Bool) (t : ℕ)
    (h : B₁.Computes (true :: (S ++ X.code)) S' t) :
    Runs (foldBody B₁) (some true, B₁.init)
      (Sum.elim (reg4 (true :: (X.code ++ L)) S.reverse [] []) (fun _ => []))
      (L.head?, B₁.init) (Sum.elim (reg4 L S'.reverse [] []) (fun _ => []))
      (1 + (2 * S'.length + 2) + t + 1 + (2 * S.length + 2) + (2 * X.code.length + 2) +
        (2 * X.code.length + 2) + 1) := by
  have r₁ := runs_basic (popTo (τ := B₁.σ) (.inl .a : Reg ⊕ B₁.K)) (some true, B₁.init)
    (Sum.elim (reg4 (true :: (X.code ++ L)) S.reverse [] []) (fun _ => [])) rfl
  simp only [popTo, TM2.stepAux, Sum.elim_inl, reg4, List.head?_cons, List.tail_cons] at r₁
  have r₂ := runs_parseV (τ := B₁.σ) (.inl .a : Reg ⊕ B₁.K) (.inl .c) (.inl .d) (by simp) (by simp)
    (by simp) (some true) B₁.init X L (Function.update (Sum.elim (reg4 (true :: (X.code ++ L))
      S.reverse [] []) (fun _ => [])) (.inl .a) (X.code ++ L)) (by simp) (by simp [reg4])
  have r₃ := runs_moveAll (τ := B₁.σ) (.inl .c : Reg ⊕ B₁.K) (.inr B₁.i) (by simp) none B₁.init
    (Sum.elim (reg4 L S.reverse X.code.reverse []) (fun _ => []))
  have r₄ := runs_moveAll (τ := B₁.σ) (.inl .b : Reg ⊕ B₁.K) (.inr B₁.i) (by simp) none B₁.init
    (Sum.elim (reg4 L S.reverse [] []) (one B₁.i X.code))
  have r₅ := runs_basic (K := Reg ⊕ B₁.K) (σ := Option Bool × B₁.σ)
    (.push (.inr B₁.i) (fun _ => true) .halt) (none, B₁.init)
    (Sum.elim (reg4 L [] [] []) (one B₁.i (S ++ X.code))) rfl
  have r₆ := runs_subM B₁ h (reg4 L [] [] []) none
  have r₇ := runs_moveAll (τ := B₁.σ) (.inr B₁.o : Reg ⊕ B₁.K) (.inl .b) (by simp) none B₁.init
    (Sum.elim (reg4 L [] [] []) (one B₁.o S'))
  have r₈ := runs_basic (peekA B₁ (K₁ := B₁.K)) (none, B₁.init)
    (Sum.elim (reg4 L S'.reverse [] []) (fun _ => [])) rfl
  simp only [peekA, TM2.stepAux, Sum.elim_inl, reg4] at r₈
  have r := runs_seq r₁ (runs_seq (r₂.of_eq rfl
      (show _ = Sum.elim (reg4 L S.reverse X.code.reverse []) (fun _ => []) by fold_tac) rfl)
    (runs_seq (r₃.of_eq rfl (show _ = Sum.elim (reg4 L S.reverse [] []) (one B₁.i X.code) by fold_tac) rfl)
    (runs_seq (r₄.of_eq rfl (show _ = Sum.elim (reg4 L [] [] []) (one B₁.i (S ++ X.code)) by fold_tac) rfl)
    (runs_seq (r₅.of_eq rfl (show _ = Sum.elim (reg4 L [] [] []) (one B₁.i (true :: (S ++ X.code)))
        by simp only [TM2.stepAux]; fold_tac) rfl)
    (runs_seq r₆ (runs_seq (r₇.of_eq rfl
        (show _ = Sum.elim (reg4 L S'.reverse [] []) (fun _ => []) by fold_tac) rfl) r₈))))))
  refine r.of_eq rfl ?_ ?_
  · fold_tac
  · simp only [Sum.elim_inl, Sum.elim_inr, reg4, one, Function.update_self, List.length_reverse]

end Fold

section FoldRuns

variable (B₁ : BM) {α β : Type} [Rep α] [Rep β] (step : β × α → β)

/-- Every step of the fold from `s` along `xs` satisfies `P`. -/
def FoldOK (P : β → α → Prop) : β → List α → Prop
  | _, [] => True
  | s, x :: l => P s x ∧ FoldOK P (step (s, x)) l

/-- The fold of `step`. -/
def foldS (s : β) (xs : List α) : β := xs.foldl (fun s x => step (s, x)) s

theorem foldLoop_runs (U : ℕ) :
    ∀ (xs : List α) (s : β), FoldOK step (fun s x => ∃ t, t + 2 * (enc (step (s, x))).length +
        2 * (enc s).length + 4 * (enc x).length + 13 ≤ U ∧
        B₁.Computes (enc (s, x)) (enc (step (s, x))) t) s xs →
      ∃ t ≤ xs.length * (U + 1) + 1, Runs (foldLoop B₁) ((enc xs).head?, B₁.init)
        (Sum.elim (reg4 (enc xs) (enc s).reverse [] []) (fun _ => [])) (some false, B₁.init)
        (Sum.elim (reg4 [false] (enc (foldS step s xs)).reverse [] []) (fun _ => [])) t := by
  intro xs
  induction xs with
  | nil =>
    intro s _
    exact ⟨1, by simp, runs_loop_false _ rfl⟩
  | cons x l ih =>
    intro s ⟨⟨t, ht, h⟩, hl⟩
    obtain ⟨t', ht', h'⟩ := ih (step (s, x)) hl
    have r := foldBody_runs B₁ (Rep.toV x) (enc l) (enc s) (enc (step (s, x))) t h
    refine ⟨_, ?_, runs_loop_true rfl r h'⟩
    simp only [List.length_cons, enc] at ht ⊢
    nlinarith

omit [Rep α] [Rep β] in
theorem foldOK_of (P : β → α → Prop) :
    ∀ (xs : List α) (s : β), (∀ k x, xs[k]? = some x → P (foldS step s (xs.take k)) x) →
      FoldOK step P s xs := by
  intro xs
  induction xs with
  | nil => intro s _; trivial
  | cons x l ih =>
    intro s h
    refine ⟨h 0 x rfl, ih _ fun k y hy => ?_⟩
    have := h (k + 1) y (by simpa using hy)
    simpa [foldS] using this

theorem length_lt_enc_list : ∀ xs : List α, xs.length < (enc xs).length
  | [] => by simp [enc_nil]
  | x :: l => by
    have := length_lt_enc_list l
    simp only [enc_cons, List.length_cons, List.length_append]
    omega

theorem enc_get_lt : ∀ (xs : List α) (k : ℕ) (x : α), xs[k]? = some x →
    (enc x).length < (enc xs).length
  | [], _, _, h => by simp at h
  | y :: l, 0, x, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [enc_cons, List.length_cons, List.length_append]
    omega
  | y :: l, k + 1, x, h => by
    have := enc_get_lt l k x (by simpa using h)
    simp only [enc_cons, List.length_cons, List.length_append]
    omega

theorem foldB_computes (U : ℕ) (s : β) (xs : List α)
    (hok : FoldOK step (fun s x => ∃ t, t + 2 * (enc (step (s, x))).length +
        2 * (enc s).length + 4 * (enc x).length + 13 ≤ U ∧
        B₁.Computes (enc (s, x)) (enc (step (s, x))) t) s xs) :
    ∃ t ≤ (2 * (enc (foldS step s xs)).length + 2) + 1 + (xs.length * (U + 1) + 1) + 1 +
        (2 * (enc s).length + 2) + 1,
      (foldB B₁).Computes (enc (s, xs)) (enc (foldS step s xs)) t := by
  obtain ⟨t₄, ht₄, r₄⟩ := foldLoop_runs B₁ step U xs s hok
  have r₁ := runs_basic (popTo (τ := B₁.σ) (.inl .a : Reg ⊕ B₁.K)) (none, B₁.init)
    (Sum.elim (reg4 (true :: (enc s ++ enc xs)) [] [] []) (fun _ => [])) rfl
  simp only [popTo, TM2.stepAux, Sum.elim_inl, reg4, List.head?_cons, List.tail_cons] at r₁
  have r₂ := runs_parseV (τ := B₁.σ) (.inl .a : Reg ⊕ B₁.K) (.inl .b) (.inl .d) (by simp) (by simp)
    (by simp) (some true) B₁.init (Rep.toV s) (enc xs) (Function.update (Sum.elim
      (reg4 (true :: (enc s ++ enc xs)) [] [] []) (fun _ => [])) (.inl .a) (enc s ++ enc xs))
    (by simp [enc]) (by simp [reg4])
  have r₃ := runs_basic (peekA B₁ (K₁ := B₁.K)) (none, B₁.init)
    (Sum.elim (reg4 (enc xs) (enc s).reverse [] []) (fun _ => [])) rfl
  simp only [peekA, TM2.stepAux, Sum.elim_inl, reg4] at r₃
  have r₅ := runs_basic (popTo (τ := B₁.σ) (.inl .a : Reg ⊕ B₁.K)) (some false, B₁.init)
    (Sum.elim (reg4 [false] (enc (foldS step s xs)).reverse [] []) (fun _ => [])) rfl
  simp only [popTo, TM2.stepAux, Sum.elim_inl, reg4, List.head?_cons, List.tail_cons] at r₅
  have r₆ := runs_moveAll (τ := B₁.σ) (.inl .b : Reg ⊕ B₁.K) (.inl .c) (by simp) (some false)
    B₁.init (Sum.elim (reg4 [] (enc (foldS step s xs)).reverse [] []) (fun _ => []))
  have r := runs_seq r₁ (runs_seq (r₂.of_eq rfl
      (show _ = Sum.elim (reg4 (enc xs) (enc s).reverse [] []) (fun _ => []) by fold_tac) rfl)
    (runs_seq (r₃.of_eq rfl (show _ = Sum.elim (reg4 (enc xs) (enc s).reverse [] []) (fun _ => [])
        by fold_tac) rfl)
    (runs_seq r₄ (runs_seq (r₅.of_eq rfl
        (show _ = Sum.elim (reg4 [] (enc (foldS step s xs)).reverse [] []) (fun _ => []) by fold_tac) rfl)
      (r₆.of_eq rfl (show _ = Sum.elim (reg4 [] [] (enc (foldS step s xs)) []) (fun _ => [])
        by fold_tac) rfl)))))
  refine ⟨_, ?_, (r.of_eq rfl ?_ rfl).of_eq₀ ?_⟩
  · simp only [Sum.elim_inl, reg4, List.length_reverse, enc] at ht₄ ⊢
    omega
  · show _ = one (K := Reg ⊕ B₁.K) (.inl .c) _
    fold_tac
  · show _ = one (K := Reg ⊕ B₁.K) (.inl .a) _
    fold_tac

omit [Rep α] [Rep β] in
theorem foldS_take_succ (s : β) (xs : List α) (k : ℕ) (x : α) (h : xs[k]? = some x) :
    foldS step s (xs.take (k + 1)) = step (foldS step s (xs.take k), x) := by
  rw [List.take_add_one, h]
  simp [foldS, List.foldl_append]

end FoldRuns

/-- **Folds.** If the step is polynomial time and the intermediate states are polynomially
bounded in the input, the fold is polynomial time. -/
theorem PT.foldl {α β : Type} [Rep α] [Rep β] {step : β × α → β} (hstep : PT step)
    (hB : ∃ B : Polynomial ℕ, ∀ (s : β) (xs : List α) (k : ℕ),
      (enc (foldS step s (xs.take k))).length ≤ B.eval (enc (s, xs)).length) :
    PT fun p : β × List α => foldS step p.1 p.2 := by
  obtain ⟨B₁, p, hp⟩ := hstep
  obtain ⟨B, hB⟩ := hB
  refine ⟨foldB B₁, Polynomial.X * (p.comp (1 + B + Polynomial.X) + 4 * B + 4 * Polynomial.X + 14) +
    3 * B + 2 * Polynomial.X + 10, fun ⟨s, xs⟩ => ?_⟩
  set n := (enc (s, xs)).length with hn
  have hxs : xs.length ≤ n := by
    have := length_lt_enc_list xs
    simp only [hn, enc_pair, List.length_cons, List.length_append]; omega
  have hs : (enc s).length ≤ n := by simp only [hn, enc_pair, List.length_cons, List.length_append]; omega
  have hsf : (enc (foldS step s xs)).length ≤ B.eval n := by
    have := hB s xs xs.length
    rwa [List.take_length] at this
  set U := p.eval (1 + B.eval n + n) + 4 * B.eval n + 4 * n + 13 with hU
  have hok := foldOK_of step (fun s x => ∃ t, t + 2 * (enc (step (s, x))).length +
        2 * (enc s).length + 4 * (enc x).length + 13 ≤ U ∧
        B₁.Computes (enc (s, x)) (enc (step (s, x))) t) xs s (fun k x hx => by
    obtain ⟨_, t, ht, h⟩ := hp (foldS step s (xs.take k), x)
    refine ⟨t, ?_, h⟩
    have h₁ := hB s xs k
    have h₂ := hB s xs (k + 1)
    rw [foldS_take_succ step s xs k x hx] at h₂
    rw [← hn] at h₁ h₂
    have h₃ := enc_get_lt xs k x hx
    have h₄ : (enc xs).length < n := by
      simp only [hn, enc_pair, List.length_cons, List.length_append]; omega
    have h₅ : p.eval (enc (foldS step s (xs.take k), x)).length ≤ p.eval (1 + B.eval n + n) := by
      apply ShiQIP.TMComp.eval_mono
      simp only [enc_pair, List.length_cons, List.length_append]
      omega
    omega)
  obtain ⟨t, ht, h⟩ := foldB_computes B₁ step U s xs hok
  refine ⟨?_, t, ?_, h⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  · have hm : xs.length * (U + 1) ≤ n * (U + 1) := Nat.mul_le_mul_right _ hxs
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
      Polynomial.eval_comp, Polynomial.eval_one]
    have e : n * (p.eval (1 + B.eval n + n) + 4 * B.eval n + 4 * n + 14) = n * (U + 1) := by
      rw [hU]
    rw [e]
    omega



end ShiQIP.Uniform
