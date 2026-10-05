import «AMPUNI-centering-packing»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
noncomputable section
open Turing Turing.TM2
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

namespace ShiTMJoint

private theorem cfg_ext {K L V : Type} {G : K → Type} {c d : Cfg G L V}
    (hl : c.l = d.l) (hv : c.var = d.var) (hs : c.stk = d.stk) : c = d := by
  cases c; cases d; cases hl; cases hv; cases hs; rfl

inductive Port where
  | source | scratch | output
  deriving DecidableEq
instance : Fintype Port := Fintype.ofList [Port.source, Port.scratch, Port.output]
  (by intro p; cases p <;> simp)
inductive Phase where
  | reverse | duplicate | takeB | putB | takeA | putA | finish
  deriving DecidableEq
instance : Fintype Phase := Fintype.ofList
  [Phase.reverse, Phase.duplicate, Phase.takeB, Phase.putB, Phase.takeA, Phase.putA, Phase.finish]
  (by intro p; cases p <;> simp)

variable (a b : FinTM2)
abbrev K := a.K ⊕ b.K ⊕ Port
abbrev Gam : K a b → Type := Sum.elim a.Γ (Sum.elim b.Γ (fun _ => Bool))
abbrev Label := Option a.Λ ⊕ Option b.Λ ⊕ Phase
abbrev State := a.σ × b.σ × Option Bool
abbrev ka (j : a.K) : K a b := .inl j
abbrev kb (j : b.K) : K a b := .inr (.inl j)
abbrev port (p : Port) : K a b := .inr (.inr p)
abbrev phase (p : Phase) : Label a b := .inr (.inr p)

/-- Disjoint machine stacks and three Boolean boundary stacks. -/
def store (S : ∀ j, List (a.Γ j)) (T : ∀ j, List (b.Γ j))
    (xs tmp out : List Bool) : ∀ j, List (Gam a b j)
  | .inl j => S j
  | .inr (.inl j) => T j
  | .inr (.inr .source) => xs
  | .inr (.inr .scratch) => tmp
  | .inr (.inr .output) => out

@[simp] theorem update_a (S : ∀ j, List (a.Γ j)) (T : ∀ j, List (b.Γ j))
    (xs tmp out : List Bool) (j : a.K) (ys : List (a.Γ j)) :
    Function.update (store a b S T xs tmp out) (ka a b j) ys =
      store a b (Function.update S j ys) T xs tmp out := by
  funext k
  cases k with
  | inl k => by_cases h : k = j <;> subst_vars <;> simp [store, ka, *]
  | inr k =>
    cases k with
    | inl k => simp [store, ka]
    | inr p => cases p <;> simp [store, ka]

@[simp] theorem update_b (S : ∀ j, List (a.Γ j)) (T : ∀ j, List (b.Γ j))
    (xs tmp out : List Bool) (j : b.K) (ys : List (b.Γ j)) :
    Function.update (store a b S T xs tmp out) (kb a b j) ys =
      store a b S (Function.update T j ys) xs tmp out := by
  funext k
  cases k with
  | inl k => simp [store, kb]
  | inr k =>
    cases k with
    | inl k => by_cases h : k = j <;> subst_vars <;> simp [store, kb, *]
    | inr k => cases k <;> simp [store, kb]

@[simp] theorem update_source (S : ∀ j, List (a.Γ j)) (T : ∀ j, List (b.Γ j))
    (xs tmp out ys : List Bool) :
    Function.update (store a b S T xs tmp out) (port a b .source) ys = store a b S T ys tmp out := by
  funext k
  rcases k with k | k | p
  · simp [store, port]
  · simp [store, port]
  · cases p <;> simp [store, port]

@[simp] theorem update_scratch (S : ∀ j, List (a.Γ j)) (T : ∀ j, List (b.Γ j))
    (xs tmp out ys : List Bool) :
    Function.update (store a b S T xs tmp out) (port a b .scratch) ys = store a b S T xs ys out := by
  funext k
  rcases k with k | k | p
  · simp [store, port]
  · simp [store, port]
  · cases p <;> simp [store, port]

@[simp] theorem update_output (S : ∀ j, List (a.Γ j)) (T : ∀ j, List (b.Γ j))
    (xs tmp out ys : List Bool) :
    Function.update (store a b S T xs tmp out) (port a b .output) ys = store a b S T xs tmp ys := by
  funext k
  rcases k with k | k | p
  · simp [store, port]
  · simp [store, port]
  · cases p <;> simp [store, port]

def liftA : Stmt a.Γ a.Λ a.σ → Stmt (Gam a b) (Label a b) (State a b)
  | .push k f q => .push (ka a b k) (fun v => f v.1) (liftA q)
  | .peek k f q => .peek (ka a b k) (fun v x => (f v.1 x, v.2)) (liftA q)
  | .pop k f q => .pop (ka a b k) (fun v x => (f v.1 x, v.2)) (liftA q)
  | .load f q => .load (fun v => (f v.1, v.2)) (liftA q)
  | .branch f q r => .branch (fun v => f v.1) (liftA q) (liftA r)
  | .goto f => .goto (fun v => .inl (some (f v.1)))
  | .halt => .goto (fun _ => .inl none)

def liftB : Stmt b.Γ b.Λ b.σ → Stmt (Gam a b) (Label a b) (State a b)
  | .push k f q => .push (kb a b k) (fun v => f v.2.1) (liftB q)
  | .peek k f q => .peek (kb a b k) (fun v x => (v.1, f v.2.1 x, v.2.2)) (liftB q)
  | .pop k f q => .pop (kb a b k) (fun v x => (v.1, f v.2.1 x, v.2.2)) (liftB q)
  | .load f q => .load (fun v => (v.1, f v.2.1, v.2.2)) (liftB q)
  | .branch f q r => .branch (fun v => f v.2.1) (liftB q) (liftB r)
  | .goto f => .goto (fun v => .inr (.inl (some (f v.2.1))))
  | .halt => .goto (fun _ => .inr (.inl none))

def cfgA (c : a.Cfg) (bv : b.σ) (reg : Option Bool) (T : ∀ j, List (b.Γ j))
    (xs tmp out : List Bool) : Cfg (Gam a b) (Label a b) (State a b) :=
  ⟨some (.inl c.l), (c.var, bv, reg), store a b c.stk T xs tmp out⟩
def cfgB (c : b.Cfg) (av : a.σ) (reg : Option Bool) (S : ∀ j, List (a.Γ j))
    (xs tmp out : List Bool) : Cfg (Gam a b) (Label a b) (State a b) :=
  ⟨some (.inr (.inl c.l)), (av, c.var, reg), store a b S c.stk xs tmp out⟩

theorem stepAux_A (q : Stmt a.Γ a.Λ a.σ) (av : a.σ) (bv : b.σ) (reg : Option Bool)
    (S : ∀ j, List (a.Γ j)) (T : ∀ j, List (b.Γ j)) (xs tmp out : List Bool) :
    stepAux (liftA a b q) (av,bv,reg) (store a b S T xs tmp out) =
      cfgA a b (stepAux q av S) bv reg T xs tmp out := by
  induction q generalizing av S with
  | push k f q ih => simpa only [liftA, stepAux, store, update_a] using ih av (Function.update S k (f av :: S k))
  | peek k f q ih => exact ih _ _
  | pop k f q ih => simpa only [liftA, stepAux, store, update_a] using ih (f av (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => exact ih _ _
  | branch f q r iq ir => cases h : f av <;> simp [liftA, stepAux, h, iq, ir]
  | goto f => rfl
  | halt => rfl

theorem stepAux_B (q : Stmt b.Γ b.Λ b.σ) (av : a.σ) (bv : b.σ) (reg : Option Bool)
    (S : ∀ j, List (a.Γ j)) (T : ∀ j, List (b.Γ j)) (xs tmp out : List Bool) :
    stepAux (liftB a b q) (av,bv,reg) (store a b S T xs tmp out) =
      cfgB a b (stepAux q bv T) av reg S xs tmp out := by
  induction q generalizing bv T with
  | push k f q ih => simpa only [liftB, stepAux, store, update_b] using ih bv (Function.update T k (f bv :: T k))
  | peek k f q ih => exact ih _ _
  | pop k f q ih => simpa only [liftB, stepAux, store, update_b] using ih (f bv (T k).head?) (Function.update T k (T k).tail)
  | load f q ih => exact ih _ _
  | branch f q r iq ir => cases h : f bv <;> simp [liftB, stepAux, h, iq, ir]
  | goto f => rfl
  | halt => rfl

/-- A finite source run is simulated through its final halt, redirected to
an active continuation label. The surrounding stacks may carry arbitrary data. -/
theorem simulate {K₀ L₀ V₀ K₁ L₁ V₁ : Type} [DecidableEq K₀] [DecidableEq K₁]
    {G₀ : K₀ → Type} {G₁ : K₁ → Type}
    (small : L₀ → Stmt G₀ L₀ V₀) (big : L₁ → Stmt G₁ L₁ V₁)
    (embed : Cfg G₀ L₀ V₀ → Cfg G₁ L₁ V₁)
    (hstep : ∀ l v S, ShiTMSubroutine.run big (some (embed ⟨some l,v,S⟩)) =
      some (embed (stepAux (small l) v S)))
    (n : Nat) (c d : Cfg G₀ L₀ V₀)
    (hr : (ShiTMSubroutine.run small)^[n] (some c) = some d) :
    (ShiTMSubroutine.run big)^[n] (some (embed c)) = some (embed d) := by
  have hn (j : Nat) : (ShiTMSubroutine.run small)^[j] none = none := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply]; exact ih
  induction n generalizing c with
  | zero => simpa using congrArg (Option.map embed) hr
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hr ⊢
    rcases c with ⟨l,v,S⟩
    cases l with
    | none =>
      change (ShiTMSubroutine.run small)^[n] none = some d at hr
      rw [hn] at hr
      cases hr
    | some l =>
      rw [hstep]
      exact ih _ hr

variable (ai : a.Γ a.k₀ ≃ Bool) (ao : a.Γ a.k₁ ≃ Bool)
  (bi : b.Γ b.k₀ ≃ Bool) (bo : b.Γ b.k₁ ≃ Bool)

def setReg (v : State a b) (r : Option Bool) : State a b := (v.1,v.2.1,r)
def getReg (v : State a b) : Bool := v.2.2.getD false

def machine : Label a b → Stmt (Gam a b) (Label a b) (State a b)
  | .inl (some l) => liftA a b (a.m l)
  | .inl none => .goto (fun _ => .inr (.inl (some b.main)))
  | .inr (.inl (some l)) => liftB a b (b.m l)
  | .inr (.inl none) => .goto (fun _ => phase a b .takeB)
  | .inr (.inr .reverse) => .pop (port a b .source) (setReg a b)
      (.branch (fun v => v.2.2.isSome)
        (.push (port a b .scratch) (getReg a b) (.goto (fun _ => phase a b .reverse)))
        (.goto (fun _ => phase a b .duplicate)))
  | .inr (.inr .duplicate) => .pop (port a b .scratch) (setReg a b)
      (.branch (fun v => v.2.2.isSome)
        (.push (ka a b a.k₀) (fun v => ai.symm (getReg a b v))
          (.push (kb a b b.k₀) (fun v => bi.symm (getReg a b v))
            (.goto (fun _ => phase a b .duplicate))))
        (.goto (fun _ => .inl (some a.main))))
  | .inr (.inr .takeB) => .pop (kb a b b.k₁) (fun v r => setReg a b v (r.map bo))
      (.branch (fun v => v.2.2.isSome)
        (.push (port a b .scratch) (getReg a b) (.goto (fun _ => phase a b .takeB)))
        (.goto (fun _ => phase a b .putB)))
  | .inr (.inr .putB) => .pop (port a b .scratch) (setReg a b)
      (.branch (fun v => v.2.2.isSome)
        (.push (port a b .output) (getReg a b) (.goto (fun _ => phase a b .putB)))
        (.goto (fun _ => phase a b .takeA)))
  | .inr (.inr .takeA) => .pop (ka a b a.k₁) (fun v r => setReg a b v (r.map ao))
      (.branch (fun v => v.2.2.isSome)
        (.push (port a b .scratch) (getReg a b) (.goto (fun _ => phase a b .takeA)))
        (.goto (fun _ => phase a b .putA)))
  | .inr (.inr .putA) => .pop (port a b .scratch) (setReg a b)
      (.branch (fun v => v.2.2.isSome)
        (.push (port a b .output) (getReg a b) (.goto (fun _ => phase a b .putA)))
        (.goto (fun _ => phase a b .finish)))
  | .inr (.inr .finish) => .halt

abbrev run := ShiTMSubroutine.run (machine a b ai ao bi bo)
def cfg (p : Phase) (av : a.σ) (bv : b.σ) (reg : Option Bool)
    (S : ∀ j, List (a.Γ j)) (T : ∀ j, List (b.Γ j)) (xs tmp out : List Bool) :=
  (⟨some (phase a b p),(av,bv,reg),store a b S T xs tmp out⟩ : Cfg (Gam a b) (Label a b) (State a b))

end ShiTMJoint
namespace ShiTMJoint
variable (a b : FinTM2)
variable (ai : a.Γ a.k₀ ≃ Bool) (ao : a.Γ a.k₁ ≃ Bool)
  (bi : b.Γ b.k₀ ≃ Bool) (bo : b.Γ b.k₁ ≃ Bool)

theorem reverse_run (xs tmp out : List Bool) (av : a.σ) (bv : b.σ) (reg : Option Bool)
    (S : ∀ j, List (a.Γ j)) (T : ∀ j, List (b.Γ j)) :
    (run a b ai ao bi bo)^[xs.length+1] (some (cfg a b .reverse av bv reg S T xs tmp out)) =
      some (cfg a b .duplicate av bv none S T [] (xs.reverse++tmp) out) := by
  induction xs generalizing reg tmp with
  | nil => simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, store, setReg]
  | cons x xs ih =>
    have first : run a b ai ao bi bo (some (cfg a b .reverse av bv reg S T (x::xs) tmp out)) =
        some (cfg a b .reverse av bv (some x) S T xs (x::tmp) out) := by
      simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, store, setReg, getReg]
    rw [List.length_cons, Function.iterate_succ_apply, first, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem duplicate_run (xs src out : List Bool) (av : a.σ) (bv : b.σ) (reg : Option Bool)
    (S : ∀ j, List (a.Γ j)) (T : ∀ j, List (b.Γ j)) :
    (run a b ai ao bi bo)^[xs.length+1] (some (cfg a b .duplicate av bv reg S T src xs out)) =
      some ⟨some (.inl (some a.main)), (av,bv,none),
        store a b (Function.update S a.k₀ (xs.reverse.map ai.symm ++ S a.k₀))
          (Function.update T b.k₀ (xs.reverse.map bi.symm ++ T b.k₀)) src [] out⟩ := by
  induction xs generalizing reg S T with
  | nil => simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, store, setReg]
  | cons x xs ih =>
    let S' := Function.update S a.k₀ (ai.symm x :: S a.k₀)
    let T' := Function.update T b.k₀ (bi.symm x :: T b.k₀)
    have first : run a b ai ao bi bo (some (cfg a b .duplicate av bv reg S T src (x::xs) out)) =
        some (cfg a b .duplicate av bv (some x) S' T' src xs out) := by
      simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, store, setReg, getReg, S', T']
    rw [List.length_cons, Function.iterate_succ_apply, first, ih]
    simp [S', T', List.reverse_cons, List.map_append, List.append_assoc]

theorem takeA_run (xs : List (a.Γ a.k₁)) (src tmp out : List Bool)
    (av : a.σ) (bv : b.σ) (reg : Option Bool)
    (S : ∀ j, List (a.Γ j)) (T : ∀ j, List (b.Γ j)) (hs : S a.k₁ = xs) :
    (run a b ai ao bi bo)^[xs.length+1] (some (cfg a b .takeA av bv reg S T src tmp out)) =
      some (cfg a b .putA av bv none (Function.update S a.k₁ []) T src
        ((xs.map ao).reverse++tmp) out) := by
  induction xs generalizing reg S tmp with
  | nil => simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, store, setReg, hs]
  | cons x xs ih =>
    let S' := Function.update S a.k₁ xs
    have first : run a b ai ao bi bo (some (cfg a b .takeA av bv reg S T src tmp out)) =
        some (cfg a b .takeA av bv (some (ao x)) S' T src (ao x::tmp) out) := by
      simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, store, setReg, getReg, hs, S']
    rw [List.length_cons, Function.iterate_succ_apply, first, ih (ao x::tmp) (some (ao x)) S' (by simp [S'])]
    simp [S', List.reverse_cons, List.append_assoc]

theorem takeB_run (xs : List (b.Γ b.k₁)) (src tmp out : List Bool)
    (av : a.σ) (bv : b.σ) (reg : Option Bool)
    (S : ∀ j, List (a.Γ j)) (T : ∀ j, List (b.Γ j)) (hs : T b.k₁ = xs) :
    (run a b ai ao bi bo)^[xs.length+1] (some (cfg a b .takeB av bv reg S T src tmp out)) =
      some (cfg a b .putB av bv none S (Function.update T b.k₁ []) src
        ((xs.map bo).reverse++tmp) out) := by
  induction xs generalizing reg T tmp with
  | nil => simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, store, setReg, hs]
  | cons x xs ih =>
    let T' := Function.update T b.k₁ xs
    have first : run a b ai ao bi bo (some (cfg a b .takeB av bv reg S T src tmp out)) =
        some (cfg a b .takeB av bv (some (bo x)) S T' src (bo x::tmp) out) := by
      simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, store, setReg, getReg, hs, T']
    rw [List.length_cons, Function.iterate_succ_apply, first, ih (bo x::tmp) (some (bo x)) T' (by simp [T'])]
    simp [T', List.reverse_cons, List.append_assoc]

theorem put_run (last : Bool) (xs src out : List Bool) (av : a.σ) (bv : b.σ) (reg : Option Bool)
    (S : ∀ j, List (a.Γ j)) (T : ∀ j, List (b.Γ j)) :
    (run a b ai ao bi bo)^[xs.length+1]
      (some (cfg a b (if last then .putA else .putB) av bv reg S T src xs out)) =
      some (cfg a b (if last then .finish else .takeA) av bv none S T src [] (xs.reverse++out)) := by
  induction xs generalizing reg out with
  | nil => cases last <;> simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, store, setReg]
  | cons x xs ih =>
    have first : run a b ai ao bi bo
        (some (cfg a b (if last then .putA else .putB) av bv reg S T src (x::xs) out)) =
        some (cfg a b (if last then .putA else .putB) av bv (some x) S T src xs (x::out)) := by
      cases last <;> simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, store, setReg, getReg]
    rw [List.length_cons, Function.iterate_succ_apply, first, ih]
    simp [List.reverse_cons, List.append_assoc]

/-- Run either component without changing the other component or boundary stacks. -/
theorem simulateA (n : Nat) (c d : a.Cfg) (bv : b.σ) (reg : Option Bool)
    (T : ∀ j, List (b.Γ j)) (xs tmp out : List Bool)
    (hr : (ShiTMSubroutine.run a.m)^[n] (some c) = some d) :
    (run a b ai ao bi bo)^[n] (some (cfgA a b c bv reg T xs tmp out)) =
      some (cfgA a b d bv reg T xs tmp out) := by
  apply simulate a.m (machine a b ai ao bi bo) (fun c => cfgA a b c bv reg T xs tmp out) _ n c d hr
  intro l v S
  simpa only [ShiTMSubroutine.run, cfgA, Option.bind_some, step, machine] using
    congrArg some (stepAux_A a b (a.m l) v bv reg S T xs tmp out)

theorem simulateB (n : Nat) (c d : b.Cfg) (av : a.σ) (reg : Option Bool)
    (S : ∀ j, List (a.Γ j)) (xs tmp out : List Bool)
    (hr : (ShiTMSubroutine.run b.m)^[n] (some c) = some d) :
    (run a b ai ao bi bo)^[n] (some (cfgB a b c av reg S xs tmp out)) =
      some (cfgB a b d av reg S xs tmp out) := by
  apply simulate b.m (machine a b ai ao bi bo) (fun c => cfgB a b c av reg S xs tmp out) _ n c d hr
  intro l v T
  simpa only [ShiTMSubroutine.run, cfgB, Option.bind_some, step, machine] using
    congrArg some (stepAux_B a b (b.m l) av v reg S T xs tmp out)

end ShiTMJoint

namespace ShiTMJoint

def oneStack (tm : FinTM2) (k : tm.K) (xs : List (tm.Γ k)) : ∀ j, List (tm.Γ j) :=
  Function.update (fun _ => []) k xs

@[simp] theorem init_stk (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) :
    (Turing.initList tm xs).stk = oneStack tm tm.k₀ xs := by
  funext k
  by_cases hk : k = tm.k₀
  · subst k
    simp only [Turing.initList]
    rw [dif_pos trivial]
    simp only [oneStack, Function.update_self, eq_mpr_eq_cast, cast_eq]
  · simp [Turing.initList, oneStack, hk]

@[simp] theorem halt_stk (tm : FinTM2) (xs : List (tm.Γ tm.k₁)) :
    (Turing.haltList tm xs).stk = oneStack tm tm.k₁ xs := by
  funext k
  by_cases hk : k = tm.k₁
  · subst k
    simp only [Turing.haltList]
    rw [dif_pos trivial]
    simp only [oneStack, Function.update_self, eq_mpr_eq_cast, cast_eq]
  · simp [Turing.haltList, oneStack, hk]

@[simp] theorem oneStack_self (tm : FinTM2) (k : tm.K) (xs : List (tm.Γ k)) :
    oneStack tm k xs k = xs := Function.update_self _ _ _

@[simp] theorem oneStack_clear (tm : FinTM2) (k : tm.K) (xs : List (tm.Γ k)) :
    Function.update (oneStack tm k xs) k [] = (fun _ => []) := by
  simp [oneStack]

variable (a b : FinTM2)
variable (ai : a.Γ a.k₀ ≃ Bool) (ao : a.Γ a.k₁ ≃ Bool)
  (bi : b.Γ b.k₀ ≃ Bool) (bo : b.Γ b.k₁ ≃ Bool)

abbrev finiteMachine : FinTM2 where
  K := K a b
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := port a b .source
  k₁ := port a b .output
  Γ := Gam a b
  Λ := Label a b
  main := phase a b .reverse
  ΛFin := inferInstance
  σ := State a b
  initialState := (a.initialState,b.initialState,none)
  σFin := inferInstance
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := machine a b ai ao bi bo

/-- Duplicate the external input in forward order onto both input stacks. -/
theorem prepare_run (xs : List Bool) :
    (run a b ai ao bi bo)^[2*xs.length+2]
      (some (cfg a b .reverse a.initialState b.initialState none (fun _ => []) (fun _ => []) xs [] [])) =
      some (cfgA a b (Turing.initList a (xs.map ai.symm)) b.initialState none
        (Turing.initList b (xs.map bi.symm)).stk [] [] []) := by
  have h1 := reverse_run a b ai ao bi bo xs [] [] a.initialState b.initialState none
    (fun _ => []) (fun _ => [])
  simp only [List.append_nil] at h1
  have h2 := duplicate_run a b ai ao bi bo xs.reverse [] [] a.initialState b.initialState none
    (fun _ => []) (fun _ => [])
  have h := ShiTMFanout.iterTwo (run a b ai ao bi bo) _ _ _ _ _ h1 h2
  have ht : xs.length+1+(xs.reverse.length+1) = 2*xs.length+2 := by simp; omega
  simp only [cfgA, init_stk]
  change (run a b ai ao bi bo)^[2*xs.length+2] _ = some ⟨some (.inl (some a.main)),
    (a.initialState,b.initialState,none),
    store a b (oneStack a a.k₀ (xs.map ai.symm)) (oneStack b b.k₀ (xs.map bi.symm)) [] [] []⟩
  simpa only [ht, oneStack, List.reverse_reverse, List.append_nil] using h

/-- Both arbitrary generator runs execute with the other stack family protected. -/
theorem generators_run (xs : List Bool) (ys : List (a.Γ a.k₁)) (zs : List (b.Γ b.k₁))
    (sa sb : Nat)
    (ha : (ShiTMSubroutine.run a.m)^[sa] (some (Turing.initList a (xs.map ai.symm))) =
      some (Turing.haltList a ys))
    (hb : (ShiTMSubroutine.run b.m)^[sb] (some (Turing.initList b (xs.map bi.symm))) =
      some (Turing.haltList b zs)) :
    (run a b ai ao bi bo)^[sa+sb+2]
      (some (cfgA a b (Turing.initList a (xs.map ai.symm)) b.initialState none
        (Turing.initList b (xs.map bi.symm)).stk [] [] [])) =
      some (cfg a b .takeB a.initialState b.initialState none
        (oneStack a a.k₁ ys) (oneStack b b.k₁ zs) [] [] []) := by
  have h1 := simulateA a b ai ao bi bo sa _ _ b.initialState none
    (Turing.initList b (xs.map bi.symm)).stk [] [] [] ha
  have bridgeA : (run a b ai ao bi bo)^[1]
      (some (cfgA a b (Turing.haltList a ys) b.initialState none
        (Turing.initList b (xs.map bi.symm)).stk [] [] [])) =
      some (cfgB a b (Turing.initList b (xs.map bi.symm)) a.initialState none
        (Turing.haltList a ys).stk [] [] []) := rfl
  have h2 := simulateB a b ai ao bi bo sb _ _ a.initialState none
    (Turing.haltList a ys).stk [] [] [] hb
  have bridgeB : (run a b ai ao bi bo)^[1]
      (some (cfgB a b (Turing.haltList b zs) a.initialState none
        (Turing.haltList a ys).stk [] [] [])) =
      some (cfg a b .takeB a.initialState b.initialState none
        (oneStack a a.k₁ ys) (oneStack b b.k₁ zs) [] [] []) := by
    simp only [run, Function.iterate_one, ShiTMSubroutine.run, cfgB, cfg, Option.bind_some,
      step, machine, halt_stk]
    rfl
  have h3 := ShiTMFanout.iterTwo (run a b ai ao bi bo) _ _ _ _ _ h1 bridgeA
  have h4 := ShiTMFanout.iterTwo (run a b ai ao bi bo) _ _ _ _ _ h3 h2
  have h5 := ShiTMFanout.iterTwo (run a b ai ao bi bo) _ _ _ _ _ h4 bridgeB
  simpa only [show sa+1+sb+1 = sa+sb+2 by omega] using h5

/-- Concatenate the decoded outputs while emptying both component output stacks. -/
theorem collect_run (ys : List (a.Γ a.k₁)) (zs : List (b.Γ b.k₁)) :
    (run a b ai ao bi bo)^[2*ys.length+2*zs.length+4]
      (some (cfg a b .takeB a.initialState b.initialState none
        (oneStack a a.k₁ ys) (oneStack b b.k₁ zs) [] [] [])) =
      some (cfg a b .finish a.initialState b.initialState none (fun _ => []) (fun _ => [])
        [] [] (ys.map ao ++ zs.map bo)) := by
  have h1 := takeB_run a b ai ao bi bo zs [] [] [] a.initialState b.initialState none
    (oneStack a a.k₁ ys) (oneStack b b.k₁ zs) (oneStack_self b _ _)
  simp only [oneStack_clear, List.append_nil] at h1
  have h2 := put_run a b ai ao bi bo false (zs.map bo).reverse [] []
    a.initialState b.initialState none (oneStack a a.k₁ ys) (fun _ => [])
  simp only [Bool.false_eq_true, ↓reduceIte, List.reverse_reverse, List.append_nil] at h2
  have h3 := takeA_run a b ai ao bi bo ys [] [] (zs.map bo) a.initialState b.initialState none
    (oneStack a a.k₁ ys) (fun _ => []) (oneStack_self a _ _)
  simp only [oneStack_clear, List.append_nil] at h3
  have h4 := put_run a b ai ao bi bo true (ys.map ao).reverse [] (zs.map bo)
    a.initialState b.initialState none (fun _ => []) (fun _ => [])
  simp only [↓reduceIte, List.reverse_reverse] at h4
  have h5 := ShiTMFanout.iterTwo (run a b ai ao bi bo) _ _ _ _ _ h1 h2
  have h6 := ShiTMFanout.iterTwo (run a b ai ao bi bo) _ _ _ _ _ h5 h3
  have h7 := ShiTMFanout.iterTwo (run a b ai ao bi bo) _ _ _ _ _ h6 h4
  have ht : zs.length+1+((zs.map bo).reverse.length+1)+(ys.length+1)+((ys.map ao).reverse.length+1) =
      2*ys.length+2*zs.length+4 := by simp; omega
  simpa only [ht] using h7

/-- Exact canonical output for two generators run on the same Boolean input. -/
theorem outputs (xs : List Bool) (ys : List (a.Γ a.k₁)) (zs : List (b.Γ b.k₁)) (ta tb : Nat)
    (ha : TM2OutputsInTime a (xs.map ai.symm) (some ys) ta)
    (hb : TM2OutputsInTime b (xs.map bi.symm) (some zs) tb) :
    Nonempty (TM2OutputsInTime (finiteMachine a b ai ao bi bo) xs (some (ys.map ao ++ zs.map bo))
      (ta+tb+2*xs.length+2*ys.length+2*zs.length+9)) := by
  obtain ⟨⟨sa, ha⟩, hsa⟩ := ha
  obtain ⟨⟨sb, hb⟩, hsb⟩ := hb
  have h1 := prepare_run a b ai ao bi bo xs
  have h2 := generators_run a b ai ao bi bo xs ys zs sa sb ha hb
  have h3 := collect_run a b ai ao bi bo ys zs
  have h4 := ShiTMFanout.iterTwo (run a b ai ao bi bo) _ _ _ _ _ h1 h2
  have h5 := ShiTMFanout.iterTwo (run a b ai ao bi bo) _ _ _ _ _ h4 h3
  let tm := finiteMachine a b ai ao bi bo
  have hi : Turing.initList tm xs = cfg a b .reverse a.initialState b.initialState none
      (fun _ => []) (fun _ => []) xs [] [] := by
    apply cfg_ext <;> try rfl
    funext k
    rcases k with k | k | k
    · simp [Turing.initList, tm, finiteMachine, port, cfg, store]
    · simp [Turing.initList, tm, finiteMachine, port, cfg, store]
    · cases k <;> simp [Turing.initList, tm, finiteMachine, port, cfg, store]
  have hf : run a b ai ao bi bo
      (some (cfg a b .finish a.initialState b.initialState none (fun _ => []) (fun _ => [])
        [] [] (ys.map ao ++ zs.map bo))) = some (Turing.haltList tm (ys.map ao ++ zs.map bo)) := by
    simp only [run, ShiTMSubroutine.run, cfg, Option.bind_some, step, machine, stepAux]
    congr 1
    apply cfg_ext <;> try rfl
    funext k
    rcases k with k | k | k
    · simp [Turing.haltList, tm, finiteMachine, port, store]
    · simp [Turing.haltList, tm, finiteMachine, port, store]
    · cases k <;> simp [Turing.haltList, tm, finiteMachine, port, store]
  refine ⟨{
    steps := (2*xs.length+2)+(sa+sb+2)+(2*ys.length+2*zs.length+4)+1
    evals_in_steps := ?_
    steps_le_m := by dsimp at hsa hsb; omega }⟩
  change (run a b ai ao bi bo)^[_] (some (Turing.initList tm xs)) = _
  rw [hi, Function.iterate_succ_apply', h5]
  exact hf

end ShiTMJoint

namespace ShiTMJoint

/-- Two polynomial-time string functions may be evaluated on the same input
and their outputs concatenated in polynomial time. -/
theorem polyTimeComputable_append (f g : PvsNP.Str → PvsNP.Str)
    (hf : PvsNP.PolyTimeComputable f) (hg : PvsNP.PolyTimeComputable g) :
    PvsNP.PolyTimeComputable (fun xs => f xs ++ g xs) := by
  obtain ⟨A⟩ := hf
  obtain ⟨B⟩ := hg
  obtain ⟨ca, hca⟩ := ShiTMStackGrowth.finite_growth A.tm.m
  obtain ⟨cb, hcb⟩ := ShiTMStackGrowth.finite_growth B.tm.m
  let tm := finiteMachine A.tm B.tm A.inputAlphabet A.outputAlphabet B.inputAlphabet B.outputAlphabet
  let P : Polynomial ℕ := Polynomial.C (2*ca+1)*A.time + Polynomial.C (2*cb+1)*B.time +
    Polynomial.C 6*Polynomial.X + Polynomial.C 9
  refine ⟨{
    tm := tm
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := P
    outputsFun := ?_ }⟩
  intro xs
  have ha := A.outputsFun xs
  have hb := B.outputsFun xs
  have hla := QMAReferenceRebuilt.«QMAReferenceValidation.candidate71» ca hca
    (xs.map A.inputAlphabet.symm) ((f xs).map A.outputAlphabet.symm) (A.time.eval xs.length) ha
  have hlb := QMAReferenceRebuilt.«QMAReferenceValidation.candidate71» cb hcb
    (xs.map B.inputAlphabet.symm) ((g xs).map B.outputAlphabet.symm) (B.time.eval xs.length) hb
  simp only [List.length_map] at hla hlb
  have hw := outputs A.tm B.tm A.inputAlphabet A.outputAlphabet B.inputAlphabet B.outputAlphabet
    xs ((f xs).map A.outputAlphabet.symm) ((g xs).map B.outputAlphabet.symm)
    (A.time.eval xs.length) (B.time.eval xs.length) ha hb
  have hw' : Nonempty (TM2OutputsInTime tm xs (some (f xs ++ g xs))
      (A.time.eval xs.length+B.time.eval xs.length+2*xs.length+2*(f xs).length+2*(g xs).length+9)) := by
    simpa [List.length_map, List.map_map, Function.comp_def, tm] using hw
  let h := Classical.choice hw'
  have hbound : A.time.eval xs.length+B.time.eval xs.length+2*xs.length+2*(f xs).length+2*(g xs).length+9 ≤
      P.eval xs.length := by
    simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    nlinarith
  have hout : TM2OutputsInTime tm xs (some (f xs ++ g xs)) (P.eval xs.length) :=
    ⟨⟨h.steps, h.evals_in_steps⟩, h.steps_le_m.trans hbound⟩
  simpa only [Equiv.refl, id_eq, List.map_id] using hout

/-- Prefix a computed output by its own length, using the checked input-length
retention wrapper applied to the identity and then composing. -/
theorem polyTimeComputable_output_prefix (f : PvsNP.Str → PvsNP.Str)
    (hf : PvsNP.PolyTimeComputable f) :
    PvsNP.PolyTimeComputable (fun xs => ShiBQP.encNat (f xs).length ++ f xs) := by
  have hid : PvsNP.PolyTimeComputable (id : PvsNP.Str → PvsNP.Str) :=
    ⟨Turing.idComputableInPolyTime (id : PvsNP.Str → PvsNP.Str)⟩
  have hp := QMAReferenceRebuilt.«ShiTMInputRetention.polyTimeComputable_length_prefix» id hid
  exact ShiTMCenteringPacking.polyTimeComputable_comp f
    (fun xs => ShiBQP.encNat xs.length ++ id xs) hf hp

/-- Construct the length-delimited pair of two outputs on the same input. -/
theorem polyTimeComputable_pair (f g : PvsNP.Str → PvsNP.Str)
    (hf : PvsNP.PolyTimeComputable f) (hg : PvsNP.PolyTimeComputable g) :
    PvsNP.PolyTimeComputable (fun xs => ShiTMCenteringPacking.input (f xs) (g xs)) :=
  polyTimeComputable_append (fun xs => ShiBQP.encNat (f xs).length ++ f xs) g
    (polyTimeComputable_output_prefix f hf) hg

/-- Uniform centering now requires only a uniform source verifier and a
polynomial-time generator for the coin bits. Pairing and assembly are discharged. -/
theorem centeredFamily_uniform_of_coin_generator (F : ShiClassQMA.QMAFamily)
    (bits : Nat → List Bool) (huniform : ShiClassQMAU.UniformQMA F)
    (coin : PvsNP.Str → PvsNP.Str) (hcoin : PvsNP.PolyTimeComputable coin)
    (hbits : ∀ n, coin (ShiBQP.unary n) = bits n) :
    ShiClassQMAU.UniformQMA (ShiQMACenteringCircuit.centeredFamily F bits) := by
  obtain ⟨src, hsrc, hsource⟩ :=
    QMAReferenceRebuilt.«ShiTMInputRetention.uniformQMA_has_length_aware_generator» F huniform
  obtain ⟨assemble, ha, hmap⟩ := ShiTMCenteringPacking.centered_encoding_from_pair_transducer
  let pair : PvsNP.Str → PvsNP.Str := fun xs => ShiTMCenteringPacking.input (coin xs) (src xs)
  have hp : PvsNP.PolyTimeComputable pair := polyTimeComputable_pair coin src hcoin hsrc
  refine ⟨assemble ∘ pair, ShiTMCenteringPacking.polyTimeComputable_comp pair assemble hp ha, ?_⟩
  intro n
  simp only [Function.comp_apply, pair, hbits, hsource]
  exact hmap F bits n

end ShiTMJoint

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMJoint.stepAux_A, ``ShiTMJoint.stepAux_B, ``ShiTMJoint.simulate,
      ``ShiTMJoint.prepare_run, ``ShiTMJoint.generators_run, ``ShiTMJoint.collect_run,
      ``ShiTMJoint.outputs, ``ShiTMJoint.polyTimeComputable_append,
      ``ShiTMJoint.polyTimeComputable_output_prefix, ``ShiTMJoint.polyTimeComputable_pair,
      ``ShiTMJoint.centeredFamily_uniform_of_coin_generator] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected joint-generator axiom {ax} in {name}"
    logInfo m!"JOINT_GENERATOR_CHECKED {name}; axioms {axioms}"
