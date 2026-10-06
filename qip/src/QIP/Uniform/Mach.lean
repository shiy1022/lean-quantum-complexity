import QIP.Uniform.Compose


/-!
# Q34 — structured machines over Boolean stacks

`Mach K σ` is a TM2 program over stacks indexed by `K`, all with alphabet `Bool`, and internal
states `σ`, with its own finite label type. `Runs M v S v' S' t` says that `M`, started at its
main label in state `v` with stacks `S`, halts after exactly `t` steps in state `v'` with stacks
`S'`.

Combinators: `basic` (one statement), `seq`, `loop` (a `while` loop), `ite`, and the lifts
`stkL`/`stkR` (into a sum of stack types) and `stL`/`stR` (into a product of state types). Each
has an exact run lemma.
-/

namespace ShiQIP.Uniform

open Turing ShiQIP.TMComp

/-- Statements over Boolean stacks. -/
abbrev BS (K Λ σ : Type) := TM2.Stmt (fun _ : K => Bool) Λ σ

/-- An open machine: a finite label type, a main label and a program. -/
structure Mach (K σ : Type) where
  Λ : Type
  [fin : Fintype Λ]
  main : Λ
  m : Λ → BS K Λ σ

attribute [instance] Mach.fin

section

variable {K σ : Type} [DecidableEq K]

/-- `M` runs from `(v, S)` to a halt in `(v', S')` in exactly `t` steps. -/
def Runs (M : Mach K σ) (v : σ) (S : K → List Bool) (v' : σ) (S' : K → List Bool) (t : ℕ) :
    Prop :=
  (flip bind (TM2.step M.m))^[t] (some ⟨some M.main, v, S⟩) = some ⟨none, v', S'⟩

theorem Runs.of_eq {M : Mach K σ} {v v₁ v₂ : σ} {S S₁ S₂ : K → List Bool} {t₁ t₂ : ℕ}
    (h : Runs M v S v₁ S₁ t₁) (hv : v₁ = v₂) (hS : S₁ = S₂) (ht : t₁ = t₂) : Runs M v S v₂ S₂ t₂ := by
  subst hv hS ht; exact h

theorem Runs.of_eq₀ {M : Mach K σ} {v v' : σ} {S₀ S₁ S' : K → List Bool} {t : ℕ}
    (h : Runs M v S₁ v' S' t) (hS : S₁ = S₀) : Runs M v S₀ v' S' t := by
  subst hS; exact h

/-! ### Relabelling -/

/-- Relabel a statement; `e` replaces `halt` (`none` keeps it). -/
def rl {Λ Λ' : Type} (f : Λ → Λ') (e : Option Λ') : BS K Λ σ → BS K Λ' σ
  | .push k g q => .push k g (rl f e q)
  | .peek k g q => .peek k g (rl f e q)
  | .pop k g q => .pop k g (rl f e q)
  | .load a q => .load a (rl f e q)
  | .branch c q₁ q₂ => .branch c (rl f e q₁) (rl f e q₂)
  | .goto g => .goto fun v => f (g v)
  | .halt => match e with
    | none => .halt
    | some l => .goto fun _ => l

/-- The label after a relabelled statement. -/
def rlLab {Λ Λ' : Type} (f : Λ → Λ') (e : Option Λ') : Option Λ → Option Λ'
  | some l => some (f l)
  | none => e

theorem stepAux_rl {Λ Λ' : Type} (f : Λ → Λ') (e : Option Λ') (q : BS K Λ σ) (v : σ)
    (S : K → List Bool) :
    TM2.stepAux (rl f e q) v S =
      ⟨rlLab f e (TM2.stepAux q v S).l, (TM2.stepAux q v S).var, (TM2.stepAux q v S).stk⟩ := by
  induction q generalizing v S with
  | push k g q ih => exact ih _ _
  | peek k g q ih => exact ih _ _
  | pop k g q ih => exact ih _ _
  | load a q ih => exact ih _ _
  | branch c q₁ q₂ ih₁ ih₂ => simp only [rl, TM2.stepAux]; cases c v <;> simp [ih₁, ih₂]
  | goto g => rfl
  | halt => cases e <;> rfl

/-- A program embedded along a label map runs the same way. -/
theorem iterate_embed {Λ Λ' : Type} (m : Λ → BS K Λ σ) (m' : Λ' → BS K Λ' σ) (f : Λ → Λ')
    (e : Option Λ') (hm : ∀ l, m' (f l) = rl f e (m l)) (t : ℕ) (l₀ : Λ) (v : σ)
    (S : K → List Bool) (v' : σ) (S' : K → List Bool)
    (h : (flip bind (TM2.step m))^[t] (some ⟨some l₀, v, S⟩) = some ⟨none, v', S'⟩) :
    (flip bind (TM2.step m'))^[t] (some ⟨some (f l₀), v, S⟩) = some ⟨e, v', S'⟩ := by
  have := iterate_sim (TM2.step m) (TM2.step m')
    (fun c => (⟨rlLab f e c.l, c.var, c.stk⟩ : TM2.Cfg (fun _ : K => Bool) Λ' σ)) ?_ t _ _ h
  · exact this
  · rintro ⟨_ | l, v, S⟩ c' hc
    · simp [TM2.step] at hc
    · simp only [TM2.step, Option.some.injEq] at hc
      subst hc
      simp only [TM2.step, rlLab, hm, stepAux_rl]

/-! ### Combinators -/

/-- One statement (which should end in `halt`). -/
def basic (q : BS K Unit σ) : Mach K σ := ⟨Unit, (), fun _ => q⟩

/-- Sequential composition. -/
def seq (M₁ M₂ : Mach K σ) : Mach K σ where
  Λ := M₁.Λ ⊕ M₂.Λ
  main := .inl M₁.main
  m
    | .inl l => rl Sum.inl (some (.inr M₂.main)) (M₁.m l)
    | .inr l => rl Sum.inr none (M₂.m l)

/-- `while c do M`. -/
def loop (c : σ → Bool) (M : Mach K σ) : Mach K σ where
  Λ := Unit ⊕ M.Λ
  main := .inl ()
  m
    | .inl _ => .branch c (.goto fun _ => .inr M.main) .halt
    | .inr l => rl Sum.inr (some (.inl ())) (M.m l)

/-- `if c then M₁ else M₂`. -/
def ite (c : σ → Bool) (M₁ M₂ : Mach K σ) : Mach K σ where
  Λ := Unit ⊕ M₁.Λ ⊕ M₂.Λ
  main := .inl ()
  m
    | .inl _ => .branch c (.goto fun _ => .inr (.inl M₁.main)) (.goto fun _ => .inr (.inr M₂.main))
    | .inr (.inl l) => rl (fun l => .inr (.inl l)) none (M₁.m l)
    | .inr (.inr l) => rl (fun l => .inr (.inr l)) none (M₂.m l)

theorem runs_basic (q : BS K Unit σ) (v : σ) (S : K → List Bool)
    (h : (TM2.stepAux q v S).l = none) :
    Runs (basic q) v S (TM2.stepAux q v S).var (TM2.stepAux q v S).stk 1 := by
  show some (TM2.stepAux q v S) = some (⟨none, (TM2.stepAux q v S).var,
    (TM2.stepAux q v S).stk⟩ : TM2.Cfg (fun _ : K => Bool) Unit σ)
  rw [← h]

theorem runs_seq {M₁ M₂ : Mach K σ} {v v₁ v₂ : σ} {S S₁ S₂ : K → List Bool} {t₁ t₂ : ℕ}
    (h₁ : Runs M₁ v S v₁ S₁ t₁) (h₂ : Runs M₂ v₁ S₁ v₂ S₂ t₂) :
    Runs (seq M₁ M₂) v S v₂ S₂ (t₂ + t₁) := by
  unfold Runs
  rw [Function.iterate_add_apply, show (seq M₁ M₂).main = Sum.inl M₁.main from rfl]
  rw [iterate_embed M₁.m (seq M₁ M₂).m Sum.inl (some (.inr M₂.main)) (fun _ => rfl) t₁ _ _ _ _ _ h₁]
  exact iterate_embed M₂.m (seq M₁ M₂).m Sum.inr none (fun _ => rfl) t₂ _ _ _ _ _ h₂

theorem runs_loop_false {c : σ → Bool} {M : Mach K σ} {v : σ} (S : K → List Bool)
    (hc : c v = false) : Runs (loop c M) v S v S 1 := by
  show some (TM2.stepAux (.branch c _ .halt) v S) = _
  simp [TM2.stepAux, hc]

theorem runs_loop_true {c : σ → Bool} {M : Mach K σ} {v v₁ v₂ : σ} {S S₁ S₂ : K → List Bool}
    {t t' : ℕ} (hc : c v = true) (h : Runs M v S v₁ S₁ t) (h' : Runs (loop c M) v₁ S₁ v₂ S₂ t') :
    Runs (loop c M) v S v₂ S₂ (t' + t + 1) := by
  unfold Runs at h' ⊢
  rw [Function.iterate_add_apply, Function.iterate_add_apply]
  have h₀ : (flip bind (TM2.step (loop c M).m))^[1] (some ⟨some (loop c M).main, v, S⟩) =
      some ⟨some (.inr M.main), v, S⟩ := by
    show some (TM2.stepAux (.branch c _ .halt) v S) = _
    simp [TM2.stepAux, hc]
  rw [h₀, iterate_embed M.m (loop c M).m Sum.inr (some (.inl ())) (fun _ => rfl) t _ _ _ _ _ h]
  exact h'

theorem runs_ite_true {c : σ → Bool} {M₁ M₂ : Mach K σ} {v v' : σ} {S S' : K → List Bool} {t : ℕ}
    (hc : c v = true) (h : Runs M₁ v S v' S' t) : Runs (ite c M₁ M₂) v S v' S' (t + 1) := by
  unfold Runs
  rw [Function.iterate_add_apply]
  have h₀ : (flip bind (TM2.step (ite c M₁ M₂).m))^[1] (some ⟨some (ite c M₁ M₂).main, v, S⟩) =
      some ⟨some (.inr (.inl M₁.main)), v, S⟩ := by
    show some (TM2.stepAux (.branch c _ _) v S) = _
    simp [TM2.stepAux, hc]
  rw [h₀]
  exact iterate_embed M₁.m (ite c M₁ M₂).m (fun l => .inr (.inl l)) none (fun _ => rfl) t _ _ _ _ _ h

theorem runs_ite_false {c : σ → Bool} {M₁ M₂ : Mach K σ} {v v' : σ} {S S' : K → List Bool} {t : ℕ}
    (hc : c v = false) (h : Runs M₂ v S v' S' t) : Runs (ite c M₁ M₂) v S v' S' (t + 1) := by
  unfold Runs
  rw [Function.iterate_add_apply]
  have h₀ : (flip bind (TM2.step (ite c M₁ M₂).m))^[1] (some ⟨some (ite c M₁ M₂).main, v, S⟩) =
      some ⟨some (.inr (.inr M₂.main)), v, S⟩ := by
    show some (TM2.stepAux (.branch c _ _) v S) = _
    simp [TM2.stepAux, hc]
  rw [h₀]
  exact iterate_embed M₂.m (ite c M₁ M₂).m (fun l => .inr (.inr l)) none (fun _ => rfl) t _ _ _ _ _ h

end

/-! ### Lifts -/

section Lift

variable {K₀ K₁ σ₀ σ₁ Λ : Type} [DecidableEq K₀] [DecidableEq K₁]

/-- Move a statement to the right summand of the stack type. -/
def sR : BS K₁ Λ σ₀ → BS (K₀ ⊕ K₁) Λ σ₀
  | .push k g q => .push (.inr k) g (sR q)
  | .peek k g q => .peek (.inr k) g (sR q)
  | .pop k g q => .pop (.inr k) g (sR q)
  | .load a q => .load a (sR q)
  | .branch c q₁ q₂ => .branch c (sR q₁) (sR q₂)
  | .goto g => .goto g
  | .halt => .halt

/-- Move a statement to the left summand of the stack type. -/
def sL : BS K₀ Λ σ₀ → BS (K₀ ⊕ K₁) Λ σ₀
  | .push k g q => .push (.inl k) g (sL q)
  | .peek k g q => .peek (.inl k) g (sL q)
  | .pop k g q => .pop (.inl k) g (sL q)
  | .load a q => .load a (sL q)
  | .branch c q₁ q₂ => .branch c (sL q₁) (sL q₂)
  | .goto g => .goto g
  | .halt => .halt

/-- Move a statement to the right factor of the state type. -/
def vR : BS K₀ Λ σ₁ → BS K₀ Λ (σ₀ × σ₁)
  | .push k g q => .push k (fun v => g v.2) (vR q)
  | .peek k g q => .peek k (fun v a => (v.1, g v.2 a)) (vR q)
  | .pop k g q => .pop k (fun v a => (v.1, g v.2 a)) (vR q)
  | .load a q => .load (fun v => (v.1, a v.2)) (vR q)
  | .branch c q₁ q₂ => .branch (fun v => c v.2) (vR q₁) (vR q₂)
  | .goto g => .goto fun v => g v.2
  | .halt => .halt

/-- Move a statement to the left factor of the state type. -/
def vL : BS K₀ Λ σ₀ → BS K₀ Λ (σ₀ × σ₁)
  | .push k g q => .push k (fun v => g v.1) (vL q)
  | .peek k g q => .peek k (fun v a => (g v.1 a, v.2)) (vL q)
  | .pop k g q => .pop k (fun v a => (g v.1 a, v.2)) (vL q)
  | .load a q => .load (fun v => (a v.1, v.2)) (vL q)
  | .branch c q₁ q₂ => .branch (fun v => c v.1) (vL q₁) (vL q₂)
  | .goto g => .goto fun v => g v.1
  | .halt => .halt

theorem stepAux_sR (q : BS K₁ Λ σ₀) (v : σ₀) (U : K₀ → List Bool) (S : K₁ → List Bool) :
    TM2.stepAux (sR q) v (Sum.elim U S) =
      ⟨(TM2.stepAux q v S).l, (TM2.stepAux q v S).var, Sum.elim U (TM2.stepAux q v S).stk⟩ := by
  induction q generalizing v S with
  | push k g q ih => simp only [sR, TM2.stepAux, Sum.elim_inr, ← Sum.elim_update_right]; exact ih _ _
  | peek k g q ih => simp only [sR, TM2.stepAux, Sum.elim_inr]; exact ih _ _
  | pop k g q ih => simp only [sR, TM2.stepAux, Sum.elim_inr, ← Sum.elim_update_right]; exact ih _ _
  | load a q ih => exact ih _ _
  | branch c q₁ q₂ ih₁ ih₂ => simp only [sR, TM2.stepAux]; cases c v <;> simp [ih₁, ih₂]
  | goto g => rfl
  | halt => rfl

theorem stepAux_sL (q : BS K₀ Λ σ₀) (v : σ₀) (S : K₀ → List Bool) (U : K₁ → List Bool) :
    TM2.stepAux (sL q) v (Sum.elim S U) =
      ⟨(TM2.stepAux q v S).l, (TM2.stepAux q v S).var, Sum.elim (TM2.stepAux q v S).stk U⟩ := by
  induction q generalizing v S with
  | push k g q ih => simp only [sL, TM2.stepAux, Sum.elim_inl, ← Sum.elim_update_left]; exact ih _ _
  | peek k g q ih => simp only [sL, TM2.stepAux, Sum.elim_inl]; exact ih _ _
  | pop k g q ih => simp only [sL, TM2.stepAux, Sum.elim_inl, ← Sum.elim_update_left]; exact ih _ _
  | load a q ih => exact ih _ _
  | branch c q₁ q₂ ih₁ ih₂ => simp only [sL, TM2.stepAux]; cases c v <;> simp [ih₁, ih₂]
  | goto g => rfl
  | halt => rfl

theorem stepAux_vR (q : BS K₀ Λ σ₁) (u : σ₀) (v : σ₁) (S : K₀ → List Bool) :
    TM2.stepAux (vR q) (u, v) S =
      ⟨(TM2.stepAux q v S).l, (u, (TM2.stepAux q v S).var), (TM2.stepAux q v S).stk⟩ := by
  induction q generalizing v S with
  | push k g q ih => exact ih _ _
  | peek k g q ih => exact ih _ _
  | pop k g q ih => exact ih _ _
  | load a q ih => exact ih _ _
  | branch c q₁ q₂ ih₁ ih₂ => simp only [vR, TM2.stepAux]; cases c v <;> simp [ih₁, ih₂]
  | goto g => rfl
  | halt => rfl

theorem stepAux_vL (q : BS K₀ Λ σ₀) (v : σ₀) (u : σ₁) (S : K₀ → List Bool) :
    TM2.stepAux (vL q) (v, u) S =
      ⟨(TM2.stepAux q v S).l, ((TM2.stepAux q v S).var, u), (TM2.stepAux q v S).stk⟩ := by
  induction q generalizing v S with
  | push k g q ih => exact ih _ _
  | peek k g q ih => exact ih _ _
  | pop k g q ih => exact ih _ _
  | load a q ih => exact ih _ _
  | branch c q₁ q₂ ih₁ ih₂ => simp only [vL, TM2.stepAux]; cases c v <;> simp [ih₁, ih₂]
  | goto g => rfl
  | halt => rfl

end Lift

section LiftMach

variable {K₀ K₁ σ₀ σ₁ : Type} [DecidableEq K₀] [DecidableEq K₁]

def Mach.sR (M : Mach K₁ σ₀) : Mach (K₀ ⊕ K₁) σ₀ := ⟨M.Λ, M.main, fun l => ShiQIP.Uniform.sR (M.m l)⟩
def Mach.sL (M : Mach K₀ σ₀) : Mach (K₀ ⊕ K₁) σ₀ := ⟨M.Λ, M.main, fun l => ShiQIP.Uniform.sL (M.m l)⟩
def Mach.vR (M : Mach K₀ σ₁) : Mach K₀ (σ₀ × σ₁) := ⟨M.Λ, M.main, fun l => ShiQIP.Uniform.vR (M.m l)⟩
def Mach.vL (M : Mach K₀ σ₀) : Mach K₀ (σ₀ × σ₁) := ⟨M.Λ, M.main, fun l => ShiQIP.Uniform.vL (M.m l)⟩

theorem runs_sR {M : Mach K₁ σ₀} {v v' : σ₀} {S S' : K₁ → List Bool} {t : ℕ}
    (h : Runs M v S v' S' t) (U : K₀ → List Bool) :
    Runs (M.sR (K₀ := K₀)) v (Sum.elim U S) v' (Sum.elim U S') t := by
  have := iterate_sim (TM2.step M.m) (TM2.step (M.sR (K₀ := K₀)).m)
    (fun c => (⟨c.l, c.var, Sum.elim U c.stk⟩ : TM2.Cfg (fun _ : K₀ ⊕ K₁ => Bool) M.Λ σ₀)) ?_ t _ _ h
  · exact this
  · rintro ⟨_ | l, v, S⟩ c' hc
    · simp [TM2.step] at hc
    · simp only [TM2.step, Option.some.injEq] at hc
      subst hc
      exact congrArg some (stepAux_sR _ _ _ _)

theorem runs_sL {M : Mach K₀ σ₀} {v v' : σ₀} {S S' : K₀ → List Bool} {t : ℕ}
    (h : Runs M v S v' S' t) (U : K₁ → List Bool) :
    Runs (M.sL (K₁ := K₁)) v (Sum.elim S U) v' (Sum.elim S' U) t := by
  have := iterate_sim (TM2.step M.m) (TM2.step (M.sL (K₁ := K₁)).m)
    (fun c => (⟨c.l, c.var, Sum.elim c.stk U⟩ : TM2.Cfg (fun _ : K₀ ⊕ K₁ => Bool) M.Λ σ₀)) ?_ t _ _ h
  · exact this
  · rintro ⟨_ | l, v, S⟩ c' hc
    · simp [TM2.step] at hc
    · simp only [TM2.step, Option.some.injEq] at hc
      subst hc
      exact congrArg some (stepAux_sL _ _ _ _)

theorem runs_vR {M : Mach K₀ σ₁} {v v' : σ₁} {S S' : K₀ → List Bool} {t : ℕ}
    (h : Runs M v S v' S' t) (u : σ₀) : Runs (M.vR (σ₀ := σ₀)) (u, v) S (u, v') S' t := by
  have := iterate_sim (TM2.step M.m) (TM2.step (M.vR (σ₀ := σ₀)).m)
    (fun c => (⟨c.l, (u, c.var), c.stk⟩ : TM2.Cfg (fun _ : K₀ => Bool) M.Λ (σ₀ × σ₁))) ?_ t _ _ h
  · exact this
  · rintro ⟨_ | l, v, S⟩ c' hc
    · simp [TM2.step] at hc
    · simp only [TM2.step, Option.some.injEq] at hc
      subst hc
      exact congrArg some (stepAux_vR _ _ _ _)

theorem runs_vL {M : Mach K₀ σ₀} {v v' : σ₀} {S S' : K₀ → List Bool} {t : ℕ}
    (h : Runs M v S v' S' t) (u : σ₁) : Runs (M.vL (σ₁ := σ₁)) (v, u) S (v', u) S' t := by
  have := iterate_sim (TM2.step M.m) (TM2.step (M.vL (σ₁ := σ₁)).m)
    (fun c => (⟨c.l, (c.var, u), c.stk⟩ : TM2.Cfg (fun _ : K₀ => Bool) M.Λ (σ₀ × σ₁))) ?_ t _ _ h
  · exact this
  · rintro ⟨_ | l, v, S⟩ c' hc
    · simp [TM2.step] at hc
    · simp only [TM2.step, Option.some.injEq] at hc
      subst hc
      exact congrArg some (stepAux_vL _ _ _ _)

end LiftMach

end ShiQIP.Uniform
