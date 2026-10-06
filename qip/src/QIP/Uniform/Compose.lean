import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_PvsNP


/-!
# Q34 — sequential composition of polynomial-time TM2 machines

`compTM tm₁ tm₂` runs `tm₁`, moves its output onto the input stack of `tm₂` (through an
auxiliary stack, so the order is kept), then runs `tm₂`. Polynomial-time computable functions
are closed under composition (`polyTime_comp`).
-/

namespace ShiQIP.TMComp

open Turing

variable (tm₁ tm₂ : FinTM2)

/-- Stacks of the composite machine: those of both machines and one auxiliary stack. -/
abbrev CK : Type := tm₁.K ⊕ tm₂.K ⊕ Unit

/-- Stack alphabets of the composite machine. -/
abbrev CΓ : CK tm₁ tm₂ → Type
  | .inl k => tm₁.Γ k
  | .inr (.inl k) => tm₂.Γ k
  | .inr (.inr _) => Bool

/-- Labels: those of both machines and two transfer labels. -/
abbrev CΛ : Type := tm₁.Λ ⊕ tm₂.Λ ⊕ Bool

/-- States: those of both machines and one scratch symbol. -/
abbrev Cσ : Type := tm₁.σ × tm₂.σ × Option Bool

/-- Combine the stacks of both machines and the auxiliary stack. -/
def joinStk (S : ∀ k, List (tm₁.Γ k)) (T : ∀ k, List (tm₂.Γ k)) (U : List Bool) :
    ∀ k : CK tm₁ tm₂, List (CΓ tm₁ tm₂ k)
  | .inl k => S k
  | .inr (.inl k) => T k
  | .inr (.inr _) => U

variable {tm₁ tm₂}

theorem joinStk_inl (S : ∀ k, List (tm₁.Γ k)) (T : ∀ k, List (tm₂.Γ k)) (U : List Bool)
    (k : tm₁.K) : joinStk tm₁ tm₂ S T U (.inl k) = S k := rfl

theorem joinStk_inr (S : ∀ k, List (tm₁.Γ k)) (T : ∀ k, List (tm₂.Γ k)) (U : List Bool)
    (k : tm₂.K) : joinStk tm₁ tm₂ S T U (.inr (.inl k)) = T k := rfl

theorem joinStk_aux (S : ∀ k, List (tm₁.Γ k)) (T : ∀ k, List (tm₂.Γ k)) (U : List Bool)
    (u : Unit) : joinStk tm₁ tm₂ S T U (.inr (.inr u)) = U := rfl

theorem update_joinStk_inl (S : ∀ k, List (tm₁.Γ k)) (T : ∀ k, List (tm₂.Γ k)) (U : List Bool)
    (k : tm₁.K) (x : List (tm₁.Γ k)) :
    Function.update (joinStk tm₁ tm₂ S T U) (.inl k) x = joinStk tm₁ tm₂ (Function.update S k x) T U := by
  funext k'
  rcases k' with k' | k' | k'
  · by_cases h : k' = k
    · subst h; (simp [Function.update, joinStk])
    · (simp [Function.update, joinStk, h])
  · (simp [Function.update, joinStk])
  · (simp [Function.update, joinStk])

theorem update_joinStk_inr (S : ∀ k, List (tm₁.Γ k)) (T : ∀ k, List (tm₂.Γ k)) (U : List Bool)
    (k : tm₂.K) (x : List (tm₂.Γ k)) :
    Function.update (joinStk tm₁ tm₂ S T U) (.inr (.inl k)) x = joinStk tm₁ tm₂ S (Function.update T k x) U := by
  funext k'
  rcases k' with k' | k' | k'
  · (simp [Function.update, joinStk])
  · by_cases h : k' = k
    · subst h; (simp [Function.update, joinStk])
    · (simp [Function.update, joinStk, h])
  · (simp [Function.update, joinStk])

theorem update_joinStk_aux (S : ∀ k, List (tm₁.Γ k)) (T : ∀ k, List (tm₂.Γ k)) (U : List Bool)
    (x : List Bool) :
    Function.update (joinStk tm₁ tm₂ S T U) (.inr (.inr ())) x = joinStk tm₁ tm₂ S T x := by
  funext k'
  rcases k' with k' | k' | ⟨⟩
  · (simp [Function.update, joinStk])
  · (simp [Function.update, joinStk])
  · (simp [Function.update, joinStk])


variable (tm₁ tm₂)

/-- A statement of `tm₁`, run inside the composite; halting goes to the first transfer label. -/
def lift₁ : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ → TM2.Stmt (CΓ tm₁ tm₂) (CΛ tm₁ tm₂) (Cσ tm₁ tm₂)
  | .push k f q => .push (.inl k) (fun s => f s.1) (lift₁ q)
  | .peek k f q => .peek (.inl k) (fun s a => (f s.1 a, s.2)) (lift₁ q)
  | .pop k f q => .pop (.inl k) (fun s a => (f s.1 a, s.2)) (lift₁ q)
  | .load a q => .load (fun s => (a s.1, s.2)) (lift₁ q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (lift₁ q₁) (lift₁ q₂)
  | .goto f => .goto (fun s => .inl (f s.1))
  | .halt => .goto (fun _ => .inr (.inr false))

/-- A statement of `tm₂`, run inside the composite. -/
def lift₂ : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ → TM2.Stmt (CΓ tm₁ tm₂) (CΛ tm₁ tm₂) (Cσ tm₁ tm₂)
  | .push k f q => .push (.inr (.inl k)) (fun s => f s.2.1) (lift₂ q)
  | .peek k f q => .peek (.inr (.inl k)) (fun s a => (s.1, f s.2.1 a, s.2.2)) (lift₂ q)
  | .pop k f q => .pop (.inr (.inl k)) (fun s a => (s.1, f s.2.1 a, s.2.2)) (lift₂ q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (lift₂ q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (lift₂ q₁) (lift₂ q₂)
  | .goto f => .goto (fun s => .inr (.inl (f s.2.1)))
  | .halt => .halt

variable (e₁ : tm₁.Γ tm₁.k₁ → Bool) (e₂ : Bool → tm₂.Γ tm₂.k₀)

/-- Transfer, first phase: move the output of `tm₁` onto the auxiliary stack. -/
def move₁ : TM2.Stmt (CΓ tm₁ tm₂) (CΛ tm₁ tm₂) (Cσ tm₁ tm₂) :=
  .pop (.inl tm₁.k₁) (fun s a => (s.1, s.2.1, a.map e₁))
    (.branch (fun s => s.2.2.isSome)
      (.push (.inr (.inr ())) (fun s => s.2.2.getD false) (.goto fun _ => .inr (.inr false)))
      (.goto fun _ => .inr (.inr true)))

/-- Transfer, second phase: move the auxiliary stack onto the input stack of `tm₂`. -/
def move₂ : TM2.Stmt (CΓ tm₁ tm₂) (CΛ tm₁ tm₂) (Cσ tm₁ tm₂) :=
  .pop (.inr (.inr ())) (fun s a => (s.1, s.2.1, a))
    (.branch (fun s => s.2.2.isSome)
      (.push (.inr (.inl tm₂.k₀)) (fun s => e₂ (s.2.2.getD false)) (.goto fun _ => .inr (.inr true)))
      (.goto fun _ => .inr (.inl tm₂.main)))

/-- The program of the composite machine. -/
def compM : CΛ tm₁ tm₂ → TM2.Stmt (CΓ tm₁ tm₂) (CΛ tm₁ tm₂) (Cσ tm₁ tm₂)
  | .inl l => lift₁ tm₁ tm₂ (tm₁.m l)
  | .inr (.inl l) => lift₂ tm₁ tm₂ (tm₂.m l)
  | .inr (.inr false) => move₁ tm₁ tm₂ e₁
  | .inr (.inr true) => move₂ tm₁ tm₂ e₂

instance : DecidableEq (CK tm₁ tm₂) := by
  haveI := tm₁.kDecidableEq; haveI := tm₂.kDecidableEq; infer_instance

instance : Fintype (CK tm₁ tm₂) := by
  haveI := tm₁.kFin; haveI := tm₂.kFin; infer_instance

/-- **The composite machine.** -/
def compTM : FinTM2 :=
  @FinTM2.mk (CK tm₁ tm₂) inferInstance inferInstance (.inl tm₁.k₀) (.inr (.inl tm₂.k₁)) (CΓ tm₁ tm₂)
    (CΛ tm₁ tm₂) (.inl tm₁.main) (by haveI := tm₁.ΛFin; haveI := tm₂.ΛFin; infer_instance)
    (Cσ tm₁ tm₂) (tm₁.initialState, tm₂.initialState, none)
    (by haveI := tm₁.σFin; haveI := tm₂.σFin; infer_instance)
    (by haveI := tm₁.Γk₀Fin; exact tm₁.Γk₀Fin) (compM tm₁ tm₂ e₁ e₂)


variable {tm₁ tm₂}

/-- The label of the composite after a `tm₁` statement ends at label `l`. -/
def lab₁ : Option tm₁.Λ → Option (CΛ tm₁ tm₂)
  | some l => some (.inl l)
  | none => some (.inr (.inr false))

theorem stepAux_lift₁ (q : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ) (v : tm₁.σ) (w : tm₂.σ × Option Bool)
    (S : ∀ k, List (tm₁.Γ k)) (T : ∀ k, List (tm₂.Γ k)) (U : List Bool) :
    TM2.stepAux (lift₁ tm₁ tm₂ q) (v, w) (joinStk tm₁ tm₂ S T U) =
      ⟨lab₁ (TM2.stepAux q v S).l, ((TM2.stepAux q v S).var, w),
        joinStk tm₁ tm₂ (TM2.stepAux q v S).stk T U⟩ := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [lift₁, TM2.stepAux, joinStk_inl]
    exact (congrArg (TM2.stepAux (lift₁ tm₁ tm₂ q) (v, w))
      (update_joinStk_inl S T U k _)).trans (ih _ _)
  | peek k f q ih => simp only [lift₁, TM2.stepAux, joinStk_inl]; exact ih _ _
  | pop k f q ih =>
    simp only [lift₁, TM2.stepAux, joinStk_inl]
    exact (congrArg (TM2.stepAux (lift₁ tm₁ tm₂ q) _)
      (update_joinStk_inl S T U k _)).trans (ih _ _)
  | load a q ih => simp only [lift₁, TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [lift₁, TM2.stepAux]; cases f v <;> simp [ih₁, ih₂]
  | goto f => simp [lift₁, TM2.stepAux, lab₁]
  | halt => simp [lift₁, TM2.stepAux, lab₁]

theorem stepAux_lift₂ (q : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ) (u : tm₁.σ) (v : tm₂.σ) (o : Option Bool)
    (S : ∀ k, List (tm₁.Γ k)) (T : ∀ k, List (tm₂.Γ k)) (U : List Bool) :
    TM2.stepAux (lift₂ tm₁ tm₂ q) (u, v, o) (joinStk tm₁ tm₂ S T U) =
      ⟨(TM2.stepAux q v T).l.map (fun l => .inr (.inl l)), (u, (TM2.stepAux q v T).var, o),
        joinStk tm₁ tm₂ S (TM2.stepAux q v T).stk U⟩ := by
  induction q generalizing v T with
  | push k f q ih =>
    simp only [lift₂, TM2.stepAux, joinStk_inr]
    exact (congrArg (TM2.stepAux (lift₂ tm₁ tm₂ q) (u, v, o))
      (update_joinStk_inr S T U k _)).trans (ih _ _)
  | peek k f q ih => simp only [lift₂, TM2.stepAux, joinStk_inr]; exact ih _ _
  | pop k f q ih =>
    simp only [lift₂, TM2.stepAux, joinStk_inr]
    exact (congrArg (TM2.stepAux (lift₂ tm₁ tm₂ q) _)
      (update_joinStk_inr S T U k _)).trans (ih _ _)
  | load a q ih => simp only [lift₂, TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [lift₂, TM2.stepAux]; cases f v <;> simp [ih₁, ih₂]
  | goto f => simp [lift₂, TM2.stepAux]
  | halt => simp [lift₂, TM2.stepAux]


/-! ### Configurations -/

theorem initList_stk_self (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    (initList tm s).stk tm.k₀ = s := dif_pos rfl

theorem initList_stk_ne (tm : FinTM2) (s : List (tm.Γ tm.k₀)) (k : tm.K) (hk : k ≠ tm.k₀) :
    (initList tm s).stk k = [] := dif_neg hk

theorem haltList_stk_self (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    (haltList tm s).stk tm.k₁ = s := dif_pos rfl

theorem haltList_stk_ne (tm : FinTM2) (s : List (tm.Γ tm.k₁)) (k : tm.K) (hk : k ≠ tm.k₁) :
    (haltList tm s).stk k = [] := dif_neg hk

variable (e₁ : tm₁.Γ tm₁.k₁ → Bool) (e₂ : Bool → tm₂.Γ tm₂.k₀)

/-- A configuration of `tm₁` inside the composite. -/
def emb₁ (c : tm₁.Cfg) : (compTM tm₁ tm₂ e₁ e₂).Cfg :=
  ⟨lab₁ c.l, (c.var, tm₂.initialState, none), joinStk tm₁ tm₂ c.stk (fun _ => []) []⟩

/-- A configuration of `tm₂` inside the composite. -/
def emb₂ (c : tm₂.Cfg) : (compTM tm₁ tm₂ e₁ e₂).Cfg :=
  ⟨c.l.map (fun l => .inr (.inl l)), (tm₁.initialState, c.var, none),
    joinStk tm₁ tm₂ (fun _ => []) c.stk []⟩

theorem step_emb₁ (c c' : tm₁.Cfg) (h : tm₁.step c = some c') :
    (compTM tm₁ tm₂ e₁ e₂).step (emb₁ e₁ e₂ c) = some (emb₁ e₁ e₂ c') := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [FinTM2.step, TM2.step] at h
  · simp only [FinTM2.step, TM2.step] at h
    cases h
    exact congrArg some (stepAux_lift₁ _ _ _ _ _ _)

theorem step_emb₂ (c c' : tm₂.Cfg) (h : tm₂.step c = some c') :
    (compTM tm₁ tm₂ e₁ e₂).step (emb₂ e₁ e₂ c) = some (emb₂ e₁ e₂ c') := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [FinTM2.step, TM2.step] at h
  · simp only [FinTM2.step, TM2.step] at h
    cases h
    exact congrArg some (stepAux_lift₂ _ _ _ _ _ _ _)

theorem iterate_none {σ : Type*} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- Simulation along an iteration. -/
theorem iterate_sim {σ τ : Type*} (f : σ → Option σ) (g : τ → Option τ) (e : σ → τ)
    (he : ∀ c c', f c = some c' → g (e c) = some (e c')) (n : ℕ) (c c' : σ)
    (h : (flip bind f)^[n] (some c) = some c') : (flip bind g)^[n] (some (e c)) = some (e c') := by
  induction n generalizing c with
  | zero => simp only [Function.iterate_zero, id, Option.some.injEq] at h ⊢; rw [h]
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    rcases hc : f c with _ | c₁
    · rw [show flip bind f (some c) = f c from rfl, hc, iterate_none] at h
      cases h
    · rw [show flip bind f (some c) = f c from rfl, hc] at h
      rw [show flip bind g (some (e c)) = g (e c) from rfl, he c c₁ hc]
      exact ih c₁ h


/-! ### The transfer phase -/

theorem move₁_cons (a : tm₁.σ) (b : tm₂.σ) (o : Option Bool) (S : ∀ k, List (tm₁.Γ k))
    (T : ∀ k, List (tm₂.Γ k)) (U : List Bool) (z : tm₁.Γ tm₁.k₁) (rest : List (tm₁.Γ tm₁.k₁))
    (hS : S tm₁.k₁ = z :: rest) :
    (compTM tm₁ tm₂ e₁ e₂).step ⟨some (.inr (.inr false)), (a, b, o), joinStk tm₁ tm₂ S T U⟩ =
      some ⟨some (.inr (.inr false)), (a, b, some (e₁ z)),
        joinStk tm₁ tm₂ (Function.update S tm₁.k₁ rest) T (e₁ z :: U)⟩ := by
  show some (TM2.stepAux (move₁ tm₁ tm₂ e₁) _ _) = _
  simp only [move₁, TM2.stepAux, joinStk_inl, hS, List.head?_cons, List.tail_cons, Option.map_some,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 2
  rw [update_joinStk_inl]
  exact update_joinStk_aux _ _ _ _

theorem move₁_nil (a : tm₁.σ) (b : tm₂.σ) (o : Option Bool) (S : ∀ k, List (tm₁.Γ k))
    (T : ∀ k, List (tm₂.Γ k)) (U : List Bool) (hS : S tm₁.k₁ = []) :
    (compTM tm₁ tm₂ e₁ e₂).step ⟨some (.inr (.inr false)), (a, b, o), joinStk tm₁ tm₂ S T U⟩ =
      some ⟨some (.inr (.inr true)), (a, b, none), joinStk tm₁ tm₂ S T U⟩ := by
  show some (TM2.stepAux (move₁ tm₁ tm₂ e₁) _ _) = _
  simp only [move₁, TM2.stepAux, joinStk_inl, hS, List.head?_nil, List.tail_nil, Option.map_none,
    Option.isSome_none, cond_false]
  congr 2
  rw [← hS]
  exact (update_joinStk_inl S T U tm₁.k₁ _).trans (by rw [Function.update_eq_self])

theorem move₂_cons (a : tm₁.σ) (b : tm₂.σ) (o : Option Bool) (S : ∀ k, List (tm₁.Γ k))
    (T : ∀ k, List (tm₂.Γ k)) (u : Bool) (U : List Bool) :
    (compTM tm₁ tm₂ e₁ e₂).step ⟨some (.inr (.inr true)), (a, b, o), joinStk tm₁ tm₂ S T (u :: U)⟩ =
      some ⟨some (.inr (.inr true)), (a, b, some u),
        joinStk tm₁ tm₂ S (Function.update T tm₂.k₀ (e₂ u :: T tm₂.k₀)) U⟩ := by
  show some (TM2.stepAux (move₂ tm₁ tm₂ e₂) _ _) = _
  simp only [move₂, TM2.stepAux, joinStk_aux, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 2
  rw [update_joinStk_aux]
  exact update_joinStk_inr _ _ _ _ _

theorem move₂_nil (a : tm₁.σ) (b : tm₂.σ) (o : Option Bool) (S : ∀ k, List (tm₁.Γ k))
    (T : ∀ k, List (tm₂.Γ k)) :
    (compTM tm₁ tm₂ e₁ e₂).step ⟨some (.inr (.inr true)), (a, b, o), joinStk tm₁ tm₂ S T []⟩ =
      some ⟨some (.inr (.inl tm₂.main)), (a, b, none), joinStk tm₁ tm₂ S T []⟩ := by
  show some (TM2.stepAux (move₂ tm₁ tm₂ e₂) _ _) = _
  simp only [move₂, TM2.stepAux, joinStk_aux, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false]
  congr 2
  exact update_joinStk_aux _ _ _ _


theorem iterate_succ_some {σ : Type*} (f : σ → Option σ) (n : ℕ) (c c₁ : σ) (h : f c = some c₁) :
    (flip bind f)^[n + 1] (some c) = (flip bind f)^[n] (some c₁) := by
  rw [Function.iterate_succ_apply]; exact congrArg _ h

/-- The first transfer loop moves the output of `tm₁`, reversed, onto the auxiliary stack. -/
theorem move₁_loop (a : tm₁.σ) (b : tm₂.σ) (T : ∀ k, List (tm₂.Γ k)) (y : List (tm₁.Γ tm₁.k₁)) :
    ∀ (o : Option Bool) (S : ∀ k, List (tm₁.Γ k)) (U : List Bool), S tm₁.k₁ = y →
    (flip bind (compTM tm₁ tm₂ e₁ e₂).step)^[y.length + 1]
        (some ⟨some (.inr (.inr false)), (a, b, o), joinStk tm₁ tm₂ S T U⟩) =
      some ⟨some (.inr (.inr true)), (a, b, none),
        joinStk tm₁ tm₂ (Function.update S tm₁.k₁ []) T ((y.map e₁).reverse ++ U)⟩ := by
  induction y with
  | nil =>
    intro o S U hS
    refine (iterate_succ_some _ _ _ _ (move₁_nil e₁ e₂ a b o S T U hS)).trans ?_
    have h : Function.update S tm₁.k₁ [] = S := by rw [← hS]; exact Function.update_eq_self _ _
    rw [h]; rfl
  | cons z rest ih =>
    intro o S U hS
    refine (iterate_succ_some _ _ _ _ (move₁_cons e₁ e₂ a b o S T U z rest hS)).trans
      ((ih _ _ _ (Function.update_self ..)).trans ?_)
    rw [Function.update_idem]
    simp

/-- The second transfer loop moves the auxiliary stack onto the input stack of `tm₂`. -/
theorem move₂_loop (a : tm₁.σ) (b : tm₂.σ) (S : ∀ k, List (tm₁.Γ k)) (U : List Bool) :
    ∀ (o : Option Bool) (T : ∀ k, List (tm₂.Γ k)),
    (flip bind (compTM tm₁ tm₂ e₁ e₂).step)^[U.length + 1]
        (some ⟨some (.inr (.inr true)), (a, b, o), joinStk tm₁ tm₂ S T U⟩) =
      some ⟨some (.inr (.inl tm₂.main)), (a, b, none),
        joinStk tm₁ tm₂ S (Function.update T tm₂.k₀ (U.reverse.map e₂ ++ T tm₂.k₀)) []⟩ := by
  induction U with
  | nil =>
    intro o T
    refine (iterate_succ_some _ _ _ _ (move₂_nil e₁ e₂ a b o S T)).trans ?_
    simp only [List.reverse_nil, List.map_nil, List.nil_append, Function.update_eq_self]
    rfl
  | cons u U ih =>
    intro o T
    refine (iterate_succ_some _ _ _ _ (move₂_cons e₁ e₂ a b o S T u U)).trans ((ih _ _).trans ?_)
    rw [Function.update_idem, Function.update_self]
    simp


/-! ### The whole run -/

theorem initList_comp (x : List (tm₁.Γ tm₁.k₀)) :
    initList (compTM tm₁ tm₂ e₁ e₂) x = emb₁ e₁ e₂ (initList tm₁ x) := by
  have hs : (initList (compTM tm₁ tm₂ e₁ e₂) x).stk =
      joinStk tm₁ tm₂ (initList tm₁ x).stk (fun _ => []) [] := by
    funext k
    rcases k with k | k | k
    · by_cases hk : k = tm₁.k₀
      · subst hk
        exact (initList_stk_self (compTM tm₁ tm₂ e₁ e₂) x).trans (initList_stk_self tm₁ x).symm
      · exact (initList_stk_ne (compTM tm₁ tm₂ e₁ e₂) x _ (by simpa [compTM] using hk)).trans
          (initList_stk_ne tm₁ x k hk).symm
    · exact initList_stk_ne (compTM tm₁ tm₂ e₁ e₂) x _ (by simp [compTM])
    · exact initList_stk_ne (compTM tm₁ tm₂ e₁ e₂) x _ (by simp [compTM])
  rw [show initList (compTM tm₁ tm₂ e₁ e₂) x = ⟨(initList (compTM tm₁ tm₂ e₁ e₂) x).l,
    (initList (compTM tm₁ tm₂ e₁ e₂) x).var, (initList (compTM tm₁ tm₂ e₁ e₂) x).stk⟩ from rfl, hs]
  rfl

theorem haltList_comp (z : List (tm₂.Γ tm₂.k₁)) :
    haltList (compTM tm₁ tm₂ e₁ e₂) z = emb₂ e₁ e₂ (haltList tm₂ z) := by
  have hs : (haltList (compTM tm₁ tm₂ e₁ e₂) z).stk =
      joinStk tm₁ tm₂ (fun _ => []) (haltList tm₂ z).stk [] := by
    funext k
    rcases k with k | k | k
    · exact haltList_stk_ne (compTM tm₁ tm₂ e₁ e₂) z _ (by simp [compTM])
    · by_cases hk : k = tm₂.k₁
      · subst hk
        exact (haltList_stk_self (compTM tm₁ tm₂ e₁ e₂) z).trans (haltList_stk_self tm₂ z).symm
      · exact (haltList_stk_ne (compTM tm₁ tm₂ e₁ e₂) z _ (by simpa [compTM] using hk)).trans
          (haltList_stk_ne tm₂ z k hk).symm
    · exact haltList_stk_ne (compTM tm₁ tm₂ e₁ e₂) z _ (by simp [compTM])
  rw [show haltList (compTM tm₁ tm₂ e₁ e₂) z = ⟨(haltList (compTM tm₁ tm₂ e₁ e₂) z).l,
    (haltList (compTM tm₁ tm₂ e₁ e₂) z).var, (haltList (compTM tm₁ tm₂ e₁ e₂) z).stk⟩ from rfl, hs]
  rfl

/-- The transfer phase takes `2 (|y| + 1)` steps. -/
theorem transfer (y : List (tm₁.Γ tm₁.k₁)) :
    (flip bind (compTM tm₁ tm₂ e₁ e₂).step)^[(y.length + 1) + (y.length + 1)]
        (some (emb₁ e₁ e₂ (haltList tm₁ y))) =
      some (emb₂ e₁ e₂ (initList tm₂ (y.map (e₂ ∘ e₁)))) := by
  rw [Function.iterate_add_apply]
  have h₁ := move₁_loop e₁ e₂ tm₁.initialState tm₂.initialState (fun _ => []) y none
    (haltList tm₁ y).stk [] (haltList_stk_self tm₁ y)
  rw [List.append_nil] at h₁
  have h₂ := move₂_loop e₁ e₂ tm₁.initialState tm₂.initialState
    (Function.update (haltList tm₁ y).stk tm₁.k₁ []) (y.map e₁).reverse none (fun _ => [])
  rw [List.length_reverse, List.length_map, List.reverse_reverse, List.append_nil,
    List.map_map] at h₂
  refine (congrArg _ h₁).trans (h₂.trans ?_)
  have hS : Function.update (haltList tm₁ y).stk tm₁.k₁ [] = fun _ => [] := by
    funext k
    by_cases hk : k = tm₁.k₁
    · subst hk; exact Function.update_self ..
    · rw [Function.update_of_ne hk]; exact haltList_stk_ne tm₁ y k hk
  have hT : Function.update (fun _ => ([] : List _)) tm₂.k₀ (y.map (e₂ ∘ e₁)) =
      (initList tm₂ (y.map (e₂ ∘ e₁))).stk := by
    funext k
    by_cases hk : k = tm₂.k₀
    · subst hk; exact (Function.update_self ..).trans (initList_stk_self tm₂ _).symm
    · rw [Function.update_of_ne hk]; exact (initList_stk_ne tm₂ _ k hk).symm
  rw [hS, hT]
  rfl

/-- **The run of the composite.** -/
theorem comp_run (x : List (tm₁.Γ tm₁.k₀)) (y : List (tm₁.Γ tm₁.k₁)) (z : List (tm₂.Γ tm₂.k₁))
    (n₁ n₂ : ℕ) (h₁ : (flip bind tm₁.step)^[n₁] (some (initList tm₁ x)) = some (haltList tm₁ y))
    (h₂ : (flip bind tm₂.step)^[n₂] (some (initList tm₂ (y.map (e₂ ∘ e₁)))) =
      some (haltList tm₂ z)) :
    (flip bind (compTM tm₁ tm₂ e₁ e₂).step)^[n₂ + ((y.length + 1) + (y.length + 1) + n₁)]
        (some (initList (compTM tm₁ tm₂ e₁ e₂) x)) =
      some (haltList (compTM tm₁ tm₂ e₁ e₂) z) := by
  rw [Function.iterate_add_apply, Function.iterate_add_apply, initList_comp, haltList_comp,
    iterate_sim _ _ (emb₁ e₁ e₂) (step_emb₁ e₁ e₂) n₁ _ _ h₁, transfer]
  exact iterate_sim _ _ (emb₂ e₁ e₂) (step_emb₂ e₁ e₂) n₂ _ _ h₂


/-! ### Output size -/

section Size

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type}

/-- The number of pushes along any path through a statement (an upper bound). -/
def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => pushes q₁ + pushes q₂
  | .goto _ => 0
  | .halt => 0

/-- The total length of all stacks. -/
def stkSize (S : ∀ k, List (Γ k)) : ℕ := ∑ k, (S k).length

theorem stkSize_update (S : ∀ k, List (Γ k)) (k : K) (x : List (Γ k)) :
    stkSize (Function.update S k x) + (S k).length = stkSize S + x.length := by
  have hfun : (fun k' => (Function.update S k x k').length) =
      Function.update (fun k' => (S k').length) k x.length := by
    funext k'
    by_cases h : k' = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  unfold stkSize
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ _),
    Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase _ (fun k' => (S k').length) (Finset.mem_univ k)]
  ring

theorem stkSize_stepAux (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    stkSize (TM2.stepAux q v S).stk ≤ stkSize S + pushes q := by
  induction q generalizing v S with
  | push k f q ih =>
    have h := stkSize_update S k (f v :: S k)
    simp only [List.length_cons] at h
    simp only [TM2.stepAux, pushes]
    have := ih v (Function.update S k (f v :: S k))
    omega
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have h := stkSize_update S k (S k).tail
    simp only [List.length_tail] at h
    simp only [TM2.stepAux, pushes]
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    omega
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, pushes]
    cases f v
    · have := ih₂ v S; simp only [cond_false]; omega
    · have := ih₁ v S; simp only [cond_true]; omega
  | goto f => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]

end Size

instance kFinInst (tm : FinTM2) : Fintype tm.K := tm.kFin

instance ΛFinInst (tm : FinTM2) : Fintype tm.Λ := tm.ΛFin

/-- The most a single step of `tm` can add to the total stack length. -/
def stepGrowth (tm : FinTM2) : ℕ :=
  ∑ l, pushes (tm.m l)

theorem stkSize_step (tm : FinTM2) (c c' : tm.Cfg) (h : tm.step c = some c') :
    stkSize c'.stk ≤ stkSize c.stk + stepGrowth tm := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [FinTM2.step, TM2.step] at h
  · simp only [FinTM2.step, TM2.step] at h
    cases h
    have h₁ := stkSize_stepAux (tm.m l) v S
    have h₂ : pushes (tm.m l) ≤ stepGrowth tm := by
      exact Finset.single_le_sum (f := fun l => pushes (tm.m l)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ l)
    exact h₁.trans (Nat.add_le_add_left h₂ _)

theorem stkSize_iterate (tm : FinTM2) (n : ℕ) (c c' : tm.Cfg)
    (h : (flip bind tm.step)^[n] (some c) = some c') :
    stkSize c'.stk ≤ stkSize c.stk + n * stepGrowth tm := by
  induction n generalizing c with
  | zero =>
    simp only [Function.iterate_zero, id, Option.some.injEq] at h
    subst h; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    rcases hc : tm.step c with _ | c₁
    · rw [show flip bind tm.step (some c) = tm.step c from rfl, hc, iterate_none] at h
      cases h
    · rw [show flip bind tm.step (some c) = tm.step c from rfl, hc] at h
      have := ih c₁ h
      have := stkSize_step tm c c₁ hc
      rw [Nat.succ_mul]; omega

theorem stkSize_initList (tm : FinTM2) (x : List (tm.Γ tm.k₀)) :
    stkSize (initList tm x).stk = x.length := by
  unfold stkSize
  rw [Finset.sum_eq_single tm.k₀ (fun k _ hk => by rw [initList_stk_ne tm x k hk]; rfl)
    (fun h => absurd (Finset.mem_univ _) h), initList_stk_self]

theorem length_le_stkSize_haltList (tm : FinTM2) (y : List (tm.Γ tm.k₁)) :
    y.length ≤ stkSize (haltList tm y).stk := by
  have := Finset.single_le_sum (f := fun k => ((haltList tm y).stk k).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ tm.k₁)
  simp only [haltList_stk_self] at this
  exact this

/-- **Output bound.** A machine that halts in `n` steps outputs at most
`|x| + n · stepGrowth` symbols. -/
theorem output_length_le (tm : FinTM2) (x : List (tm.Γ tm.k₀)) (y : List (tm.Γ tm.k₁)) (n : ℕ)
    (h : (flip bind tm.step)^[n] (some (initList tm x)) = some (haltList tm y)) :
    y.length ≤ x.length + n * stepGrowth tm := by
  have h₁ := stkSize_iterate tm n _ _ h
  have h₂ := length_le_stkSize_haltList tm y
  have h₃ := stkSize_initList tm x
  omega


/-! ### Polynomial-time computable functions compose -/

/-- Polynomials with natural coefficients are monotone on `ℕ`. -/
theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-- **Composition**, for arbitrary encodings with a Boolean middle alphabet. -/
theorem comp_inPolyTime {α β γ αΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List Bool}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ} (hf : Nonempty (TM2ComputableInPolyTime ea eb f))
    (hg : Nonempty (TM2ComputableInPolyTime eb ec g)) :
    Nonempty (TM2ComputableInPolyTime ea ec (g ∘ f)) := by
  obtain ⟨M₁⟩ := hf
  obtain ⟨M₂⟩ := hg
  let e₁ : M₁.tm.Γ M₁.tm.k₁ → Bool := M₁.outputAlphabet
  let e₂ : Bool → M₂.tm.Γ M₂.tm.k₀ := M₂.inputAlphabet.invFun
  let G := stepGrowth M₁.tm
  let q : Polynomial ℕ := Polynomial.X + Polynomial.C G * M₁.time
  refine ⟨⟨⟨compTM M₁.tm M₂.tm e₁ e₂, M₁.inputAlphabet, M₂.outputAlphabet⟩,
    M₂.time.comp q + 2 * (q + 1) + M₁.time, fun a => ?_⟩⟩
  obtain ⟨⟨s₁, h₁⟩, hs₁⟩ := M₁.outputsFun a
  obtain ⟨⟨s₂, h₂⟩, hs₂⟩ := M₂.outputsFun (f a)
  simp only [Option.map_some] at h₁ h₂ hs₁ hs₂
  set y := List.map M₁.outputAlphabet.invFun (eb (f a))
  have hy : y.map (e₂ ∘ e₁) = List.map M₂.inputAlphabet.invFun (eb (f a)) := by
    simp [y, e₁, e₂, Function.comp_def]
  rw [← hy] at h₂
  have hrun := comp_run e₁ e₂ _ _ _ s₁ s₂ h₁ h₂
  have hlen : y.length ≤ (ea a).length + s₁ * G := by
    have := output_length_le M₁.tm _ _ s₁ h₁
    simpa using this
  have hfa : (eb (f a)).length = y.length := by simp [y]
  refine ⟨⟨_, hrun⟩, ?_⟩
  have hq : (eb (f a)).length ≤ q.eval (ea a).length := by
    simp only [q, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
    have := Nat.mul_le_mul_left G hs₁
    rw [hfa]; nlinarith
  have h₂' : s₂ ≤ (M₂.time.comp q).eval (ea a).length := by
    rw [Polynomial.eval_comp]; exact hs₂.trans (eval_mono _ hq)
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  rw [← hfa] at hlen
  omega

open PvsNP in
/-- **Composition.** If `f` and `g` are polynomial-time computable, so is `g ∘ f`. -/
theorem polyTime_comp {f g : Str → Str} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : PolyTimeComputable (g ∘ f) :=
  comp_inPolyTime hf hg

end ShiQIP.TMComp
