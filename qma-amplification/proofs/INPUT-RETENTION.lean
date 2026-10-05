import Definitions.Def_ShiTM2_Composite
import Definitions.Def_ShiBQP_Core
import Definitions.Def_ShiClassQMAU
import Theorems.Thm_ShiTM_copy_loop_transfers_stack
import Theorems.Thm_ShiTM_iterate_compM_two_simulation
import Theorems.Thm_ShiTM_initList_haltList_laws
import Theorems.Thm_PvsNP_polyTimeComputable_comp
import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_resource_identities_and_regularity
import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_semantically_eq_ampFamily
import Theorems.Thm_ShiClassQMAAmp_ampFamily_resource_identities_and_depth
import Theorems.Thm_ShiClassQMAAmp_ampFamily_threefold_structure_package
import Theorems.Thm_ShiClassQMA_amplified_acceptWith_le_maj3_of_single_copy_bound
import Theorems.Thm_ShiClassQMA_exists_amplified_witness_maj3_ge_of_single_copy_bound

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false


open Turing Turing.TM2

namespace ShiTMInputRetention

private theorem cfg_ext {K L V : Type} {G : K → Type} {c d : Cfg G L V}
    (hl : c.l = d.l) (hv : c.var = d.var) (hs : c.stk = d.stk) : c = d := by
  cases c; cases d; cases hl; cases hv; cases hs; rfl


@[simp] private theorem fold_reg_fst {A B C X : Type} (f : X → C)
    (s : List X) (v : A × B × C) :
    (s.foldl (fun w x => (w.1, w.2.1, f x)) v).1 = v.1 := by
  induction s generalizing v with
  | nil => rfl
  | cons x s ih => exact ih (v.1, v.2.1, f x)

@[simp] private theorem fold_reg_snd {A B C X : Type} (f : X → C)
    (s : List X) (v : A × B × C) :
    (s.foldl (fun w x => (w.1, w.2.1, f x)) v).2.1 = v.2.1 := by
  induction s generalizing v with
  | nil => rfl
  | cons x s ih => exact ih (v.1, v.2.1, f x)


/-!
An input-preserving wrapper for a Boolean-input/Boolean-output `FinTM2`.

The underlying `ShiTM2.comp (idComputer Bool) tm` already copies the external input into
`tm`.  We add one protected counter stack.  Its first copy pass pushes one `true` for every
input symbol.  When `tm` would halt, the wrapper pushes `false` onto the output and drains the
counter, pushing `true` once per mark.  Thus an output `f s` becomes
`encNat s.length ++ f s` without asking `f s` to determine `s.length`.
-/

abbrev Id : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .halt

abbrev Base (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) : Turing.FinTM2 :=
  { K := ShiTM2.CompK Id tm
    kDecidableEq := ShiTM2.compKDecEq Id tm
    kFin := ShiTM2.compKFintype Id tm
    k₀ := ShiTM2.injK₁ Id tm Id.k₀
    k₁ := ShiTM2.injK₂ Id tm tm.k₁
    Γ := ShiTM2.CompΓ Id tm
    Λ := ShiTM2.CompΛ Id tm
    main := ShiTM2.injΛ₁ Id tm Id.main
    ΛFin := ShiTM2.compΛFintype Id tm
    σ := ShiTM2.Compσ Id tm
    initialState := ShiTM2.compInitialState Id tm
    σFin := ShiTM2.compσFintype Id tm
    Γk₀Fin := ShiTM2.compΓk₀Fintype Id tm
    m := ShiTM2.compM Id tm ein.invFun (ein.invFun false) }

abbrev K (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) : Type :=
  (Base tm ein).K ⊕ Unit

abbrev kBase {tm : Turing.FinTM2} {ein : tm.Γ tm.k₀ ≃ Bool}
    (k : (Base tm ein).K) : K tm ein := Sum.inl k

abbrev kCount (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) : K tm ein :=
  Sum.inr ()

abbrev Gam (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) : K tm ein → Type :=
  Sum.elim (Base tm ein).Γ (fun _ : Unit => Bool)

abbrev PostLabel := Option Bool

abbrev Lam (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) : Type :=
  (Base tm ein).Λ ⊕ PostLabel

abbrev lBase {tm : Turing.FinTM2} {ein : tm.Γ tm.k₀ ≃ Bool}
    (l : (Base tm ein).Λ) : Lam tm ein := Sum.inl l

abbrev lStart (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) : Lam tm ein :=
  Sum.inr none

abbrev lDrain (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) : Lam tm ein :=
  Sum.inr (some false)

abbrev lHalt (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) : Lam tm ein :=
  Sum.inr (some true)

abbrev Sig (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) : Type :=
  (Base tm ein).σ

private def liftStmt (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) :
    Stmt (Base tm ein).Γ (Base tm ein).Λ (Base tm ein).σ →
      Stmt (Gam tm ein) (Lam tm ein) (Sig tm ein)
  | .push k f q => .push (kBase k) f (liftStmt tm ein q)
  | .peek k f q => .peek (kBase k) f (liftStmt tm ein q)
  | .pop k f q => .pop (kBase k) f (liftStmt tm ein q)
  | .load f q => .load f (liftStmt tm ein q)
  | .branch f q₁ q₂ => .branch f (liftStmt tm ein q₁) (liftStmt tm ein q₂)
  | .goto f => .goto (fun s => lBase (f s))
  | .halt => .goto (fun _ => lStart tm ein)

private def countedCopyA (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) :
    Stmt (Gam tm ein) (Lam tm ein) (Sig tm ein) :=
  let tr := ein.invFun
  let dflt := ein.invFun false
  Stmt.pop (kBase (ShiTM2.injK₁ Id tm Id.k₁)) (ShiTM2.loadRegA Id tm tr)
    (Stmt.branch (ShiTM2.regIsSome Id tm)
      (Stmt.push (kBase (ShiTM2.kScr Id tm)) (ShiTM2.pushReg Id tm dflt)
        (Stmt.push (kCount tm ein) (fun _ => true)
          (Stmt.goto (fun _ => lBase (ShiTM2.lcopyA Id tm)))))
      (Stmt.goto (fun _ => lBase (ShiTM2.lcopyB Id tm))))

private def program (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool)
    (eout : tm.Γ tm.k₁ ≃ Bool) :
    Lam tm ein → Stmt (Gam tm ein) (Lam tm ein) (Sig tm ein)
  | Sum.inl (Sum.inl l) =>
      liftStmt tm ein (ShiTM2.trStmt₁ Id tm (Id.m l))
  | Sum.inl (Sum.inr (Sum.inl l)) =>
      liftStmt tm ein (ShiTM2.trStmt₂ Id tm (tm.m l))
  | Sum.inl (Sum.inr (Sum.inr false)) => countedCopyA tm ein
  | Sum.inl (Sum.inr (Sum.inr true)) =>
      liftStmt tm ein (ShiTM2.copyB Id tm (ein.invFun false))
  | Sum.inr none =>
      Stmt.push (kBase (ShiTM2.injK₂ Id tm tm.k₁)) (fun _ => eout.invFun false)
        (Stmt.goto (fun _ => lDrain tm ein))
  | Sum.inr (some false) =>
      Stmt.pop (kCount tm ein)
        (fun s o => (s.1, s.2.1, o.map (fun _ => ein.invFun true)))
        (Stmt.branch (ShiTM2.regIsSome Id tm)
          (Stmt.push (kBase (ShiTM2.injK₂ Id tm tm.k₁)) (fun _ => eout.invFun true)
            (Stmt.goto (fun _ => lDrain tm ein)))
          (Stmt.goto (fun _ => lHalt tm ein)))
  | Sum.inr (some true) => Stmt.halt

private def kDecEq (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) : DecidableEq (K tm ein) :=
  letI : DecidableEq (Base tm ein).K := (Base tm ein).kDecidableEq
  inferInstance

private def kFinite (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) : Fintype (K tm ein) :=
  letI : Fintype (Base tm ein).K := (Base tm ein).kFin
  inferInstance

private def lFinite (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool) : Fintype (Lam tm ein) :=
  letI : Fintype (Base tm ein).Λ := (Base tm ein).ΛFin
  inferInstance

/-- The protected-input machine.  Correctness is proved below rather than built into the data. -/
abbrev machine (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool)
    (eout : tm.Γ tm.k₁ ≃ Bool) : Turing.FinTM2 where
  K := K tm ein
  kDecidableEq := kDecEq tm ein
  kFin := kFinite tm ein
  k₀ := kBase (ShiTM2.injK₁ Id tm Id.k₀)
  k₁ := kBase (ShiTM2.injK₂ Id tm tm.k₁)
  Γ := Gam tm ein
  Λ := Lam tm ein
  main := lBase (ShiTM2.injΛ₁ Id tm Id.main)
  ΛFin := lFinite tm ein
  σ := Sig tm ein
  initialState := (Base tm ein).initialState
  σFin := (Base tm ein).σFin
  Γk₀Fin := (Base tm ein).Γk₀Fin
  m := program tm ein eout

def inputAlphabet (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool)
    (eout : tm.Γ tm.k₁ ≃ Bool) :
    (machine tm ein eout).Γ (machine tm ein eout).k₀ ≃ Bool :=
  Equiv.refl Bool

def outputAlphabet (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool)
    (eout : tm.Γ tm.k₁ ≃ Bool) :
    (machine tm ein eout).Γ (machine tm ein eout).k₁ ≃ Bool := eout

attribute [local simp] kBase kCount lBase lStart lDrain lHalt
  ShiTM2.injK₁ ShiTM2.injK₂ ShiTM2.kScr ShiTM2.injΛ₁ ShiTM2.injΛ₂
  ShiTM2.lcopyA ShiTM2.lcopyB

/-! The published counted-loop lemma stops on a distinguished failing cell.  Input stacks,
however, stop at `[]`.  The next lemmas prove the corresponding empty-stack form. -/

private theorem counted_step_cons {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) {ka kb kc : K}
    (hab : ka ≠ kb) (hac : ka ≠ kc) (hbc : kb ≠ kc) {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool}
    {hpush : σ → Γ kb} {hmark : σ → Γ kc}
    {e : Γ ka → Γ kb} {mk : Γ ka → Γ kc}
    (hM : M lc = Stmt.pop ka fpop
      (Stmt.branch gtest
        (Stmt.push kb hpush (Stmt.push kc hmark (Stmt.goto (fun _ => lc))))
        (Stmt.goto (fun _ => lnext))))
    (hcont : ∀ w y, gtest (fpop w (some y)) = true)
    (hval : ∀ w y, hpush (fpop w (some y)) = e y)
    (hmarkval : ∀ w y, hmark (fpop w (some y)) = mk y)
    (x : Γ ka) (s : List (Γ ka)) (v : σ) (S : ∀ k, List (Γ k))
    (hS : S ka = x :: s) :
    step M ⟨some lc, v, S⟩
      = some ⟨some lc, fpop v (some x), Function.update
            (Function.update (Function.update S ka s) kb (e x :: S kb))
            kc (mk x :: S kc)⟩ := by
  have hstep : step M ⟨some lc, v, S⟩
      = some (stepAux (M lc) v S) := rfl
  rw [hstep, hM]
  simp [stepAux, hS, hcont, hval, hmarkval, Function.update_of_ne
    (Ne.symm hab), Function.update_of_ne (Ne.symm hac),
    Function.update_of_ne (Ne.symm hbc)]

private theorem counted_step_nil {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) {ka kb kc : K} {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool}
    {hpush : σ → Γ kb} {hmark : σ → Γ kc}
    (hM : M lc = Stmt.pop ka fpop
      (Stmt.branch gtest
        (Stmt.push kb hpush (Stmt.push kc hmark (Stmt.goto (fun _ => lc))))
        (Stmt.goto (fun _ => lnext))))
    (hstop : ∀ w, gtest (fpop w none) = false)
    (v : σ) (S : ∀ k, List (Γ k)) (hS : S ka = []) :
    step M ⟨some lc, v, S⟩
      = some ⟨some lnext, fpop v none, Function.update S ka []⟩ := by
  have hstep : step M ⟨some lc, v, S⟩
      = some (stepAux (M lc) v S) := rfl
  rw [hstep, hM]
  simp [stepAux, hS, hstop]

private theorem update_three_eq {K : Type} [DecidableEq K] {Γ : K → Type}
    (ka kb kc : K) (S T : ∀ k, List (Γ k))
    (h : ∀ k, k ≠ ka → k ≠ kb → k ≠ kc → S k = T k)
    (a : List (Γ ka)) (b : List (Γ kb)) (c : List (Γ kc)) :
    Function.update (Function.update (Function.update S ka a) kb b) kc c
      = Function.update (Function.update (Function.update T ka a) kb b) kc c := by
  funext k
  by_cases hc : k = kc
  · subst hc; simp
  · simp only [Function.update_of_ne hc]
    by_cases hb : k = kb
    · subst hb; simp
    · simp only [Function.update_of_ne hb]
      by_cases ha : k = ka
      · subst ha; simp
      · simp only [Function.update_of_ne ha]
        exact h k ha hb hc

/-- A counted two-push copy loop consumes a genuinely finite source stack (no sentinel),
records exactly one mark per source cell, and takes exactly `s.length + 1` steps. -/
theorem counted_copy_until_empty {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) {ka kb kc : K}
    (hab : ka ≠ kb) (hac : ka ≠ kc) (hbc : kb ≠ kc) {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool}
    {hpush : σ → Γ kb} {hmark : σ → Γ kc}
    {e : Γ ka → Γ kb} {mk : Γ ka → Γ kc}
    (hM : M lc = Stmt.pop ka fpop
      (Stmt.branch gtest
        (Stmt.push kb hpush (Stmt.push kc hmark (Stmt.goto (fun _ => lc))))
        (Stmt.goto (fun _ => lnext))))
    (hcont : ∀ w y, gtest (fpop w (some y)) = true)
    (hstop : ∀ w, gtest (fpop w none) = false)
    (hval : ∀ w y, hpush (fpop w (some y)) = e y)
    (hmarkval : ∀ w y, hmark (fpop w (some y)) = mk y)
    (s : List (Γ ka)) (v : σ) (S : ∀ k, List (Γ k)) (hS : S ka = s) :
    (fun c : Option (Cfg Γ Λ σ) => c.bind (step M))^[s.length + 1]
      (some ⟨some lc, v, S⟩)
      = some ⟨some lnext, fpop (s.foldl (fun w y => fpop w (some y)) v) none, Function.update
            (Function.update (Function.update S ka []) kb
              ((s.map e).reverse ++ S kb))
            kc ((s.map mk).reverse ++ S kc)⟩ := by
  induction s generalizing v S with
  | nil =>
      have h1 := counted_step_nil M hM hstop v S hS
      rw [List.length_nil, Function.iterate_one]
      simp only [List.foldl_nil, List.map_nil, List.reverse_nil, List.nil_append, Option.bind_some]
      rw [h1]
      apply congrArg some
      congr 1
      have hz : Function.update S ka [] = S := by
        funext j
        by_cases hj : j = ka
        · subst j; simp [hS]
        · simp [hj]
      simp [hz]
  | cons x s ih =>
      have h1 := counted_step_cons M hab hac hbc hM hcont hval hmarkval x s v S hS
      let S₁ := Function.update
        (Function.update (Function.update S ka s) kb (e x :: S kb))
        kc (mk x :: S kc)
      have hS₁a : S₁ ka = s := by
        simp [S₁, hab, hac]
      have h2 := ih (fpop v (some x)) S₁ hS₁a
      have hS₁b : S₁ kb = e x :: S kb := by simp [S₁, hbc]
      have hS₁c : S₁ kc = mk x :: S kc := by simp [S₁]
      rw [hS₁b, hS₁c] at h2
      have hother : ∀ k, k ≠ ka → k ≠ kb → k ≠ kc → S₁ k = S k := by
        intro k ha hb hc
        simp [S₁, ha, hb, hc]
      have hstk := update_three_eq ka kb kc S₁ S hother
        ([] : List (Γ ka))
        ((s.map e).reverse ++ e x :: S kb)
        ((s.map mk).reverse ++ mk x :: S kc)
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some]
      rw [h1, h2]
      simp only [List.foldl_cons, List.map_cons, List.reverse_cons,
        List.append_assoc, List.cons_append, List.nil_append]
      rw [hstk]

/-- The first handover pass of `machine` both reverses/transcodes the external input onto the
scratch stack and records its exact length on the protected counter. -/
theorem first_pass_retains_input_length (tm : Turing.FinTM2)
    (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool)
    (s : List Bool) (v : Sig tm ein) (S : ∀ k, List (Gam tm ein k))
    (hsrc : S (kBase (ShiTM2.injK₁ Id tm Id.k₁)) = s)
    (hcount : S (kCount tm ein) = []) :
    ∃ (v' : Sig tm ein) (T : ∀ k, List (Gam tm ein k)),
      (fun c : Option (Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein)) =>
          c.bind (step (program tm ein eout)))^[s.length + 1]
        (some ⟨some (lBase (ShiTM2.lcopyA Id tm)), v, S⟩)
        = some ⟨some (lBase (ShiTM2.lcopyB Id tm)), v', T⟩
      ∧ T (kCount tm ein) = List.replicate s.length true
      ∧ T (kBase (ShiTM2.kScr Id tm))
          = List.append (s.map ein.invFun).reverse (S (kBase (ShiTM2.kScr Id tm)))
      ∧ T (kBase (ShiTM2.injK₁ Id tm Id.k₁)) = []
      ∧ v' = (v.1, v.2.1, none)
      ∧ ∀ k, k ≠ kBase (ShiTM2.injK₁ Id tm Id.k₁) →
          k ≠ kBase (ShiTM2.kScr Id tm) → k ≠ kCount tm ein → T k = S k := by
  let ka : K tm ein := kBase (ShiTM2.injK₁ Id tm Id.k₁)
  let kb : K tm ein := kBase (ShiTM2.kScr Id tm)
  let kc : K tm ein := kCount tm ein
  let fp : Sig tm ein → Option (Gam tm ein ka) → Sig tm ein :=
    ShiTM2.loadRegA Id tm ein.invFun
  let gt : Sig tm ein → Bool := ShiTM2.regIsSome Id tm
  let hp : Sig tm ein → Gam tm ein kb :=
    ShiTM2.pushReg Id tm (ein.invFun false)
  let hm : Sig tm ein → Gam tm ein kc := fun _ => true
  let ee : Gam tm ein ka → Gam tm ein kb := ein.invFun
  let mk : Gam tm ein ka → Gam tm ein kc := fun _ => true
  have hab : ka ≠ kb := by simp [ka, kb]
  have hac : ka ≠ kc := by simp [ka, kc]
  have hbc : kb ≠ kc := by simp [kb, kc]
  have hrun := counted_copy_until_empty (program tm ein eout) hab hac hbc
    (lc := lBase (ShiTM2.lcopyA Id tm))
    (lnext := lBase (ShiTM2.lcopyB Id tm))
    (fpop := fp) (gtest := gt) (hpush := hp) (hmark := hm)
    (e := ee) (mk := mk)
    (hM := by rfl)
    (hcont := by intro w y; rfl)
    (hstop := by intro w; rfl)
    (hval := by intro w y; rfl)
    (hmarkval := by intro w y; rfl)
    s v S (by exact hsrc)
  let v' : Sig tm ein := fp (s.foldl (fun w y => fp w (some y)) v) none
  let T : ∀ k, List (Gam tm ein k) :=
    Function.update
      (Function.update (Function.update S ka []) kb
        ((s.map ee).reverse ++ S kb))
      kc ((s.map mk).reverse ++ S kc)
  refine ⟨v', T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hrun
  · simp [T, kc, hcount, mk]
  · simp [T, ka, kb, kc, hbc, ee]
  · simp [T, ka, kb, kc, hab, hac]
  · exact congrArg₂ (fun a b => (a, b, (none : Option (tm.Γ tm.k₀))))
      (fold_reg_fst (fun y => some (ein.invFun y)) s v)
      (fold_reg_snd (fun y => some (ein.invFun y)) s v)
  · intro k hka hkb hkc
    simp [T, ka, kb, kc, hka, hkb, hkc]

/-- The ordinary second handover pass restores the input order on `tm.k₀` and cannot alter
the protected counter. -/
theorem second_pass_preserves_counter (tm : Turing.FinTM2)
    (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool)
    (s : List Bool) (v : Sig tm ein) (S : ∀ k, List (Gam tm ein k))
    (hscr : S (kBase (ShiTM2.kScr Id tm)) = (s.map ein.invFun).reverse)
    (hin : S (kBase (ShiTM2.injK₂ Id tm tm.k₀)) = [])
    (hcount : S (kCount tm ein) = List.replicate s.length true) :
    ∃ (v' : Sig tm ein) (T : ∀ k, List (Gam tm ein k)),
      (fun c : Option (Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein)) =>
          c.bind (step (program tm ein eout)))^[(s.map ein.invFun).length + 1]
        (some ⟨some (lBase (ShiTM2.lcopyB Id tm)), v, S⟩)
        = some ⟨some (lBase (ShiTM2.injΛ₂ Id tm tm.main)), v', T⟩
      ∧ T (kBase (ShiTM2.injK₂ Id tm tm.k₀)) = s.map ein.invFun
      ∧ T (kCount tm ein) = List.replicate s.length true
      ∧ T (kBase (ShiTM2.kScr Id tm)) = []
      ∧ v' = (v.1, v.2.1, none)
      ∧ ∀ k, k ≠ kBase (ShiTM2.kScr Id tm) →
          k ≠ kBase (ShiTM2.injK₂ Id tm tm.k₀) → T k = S k := by
  let ka : K tm ein := kBase (ShiTM2.kScr Id tm)
  let kb : K tm ein := kBase (ShiTM2.injK₂ Id tm tm.k₀)
  let kc : K tm ein := kCount tm ein
  let fp : Sig tm ein → Option (Gam tm ein ka) → Sig tm ein :=
    ShiTM2.loadRegB Id tm
  let gt : Sig tm ein → Bool := ShiTM2.regIsSome Id tm
  let hp : Sig tm ein → Gam tm ein kb :=
    ShiTM2.pushReg Id tm (ein.invFun false)
  let ee : Gam tm ein ka → Gam tm ein kb := fun x => x
  have hab : ka ≠ kb := by simp [ka, kb]
  obtain ⟨hrun, _⟩ := ShiTM.copy_loop_transfers_stack (program tm ein eout) hab
    (lc := lBase (ShiTM2.lcopyB Id tm))
    (lnext := lBase (ShiTM2.injΛ₂ Id tm tm.main))
    (fpop := fp) (gtest := gt) (hpush := hp) (e := ee)
    (hM := by rfl)
    (hcont := by intro w y; rfl)
    (hstop := by intro w; rfl)
    (hval := by intro w y; rfl)
    ((s.map ein.invFun).reverse) v S hscr
  let v' : Sig tm ein := fp
    (((s.map ein.invFun).reverse).foldl (fun w y => fp w (some y)) v) none
  let T : ∀ k, List (Gam tm ein k) :=
    Function.update (Function.update S ka []) kb
      (((((s.map ein.invFun).reverse).map ee).reverse) ++ S kb)
  refine ⟨v', T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.length_reverse] using hrun
  · simp [T, ka, kb, ee, hin]
  · have hca : kc ≠ ka := by simp [kc, ka]
    have hcb : kc ≠ kb := by simp [kc, kb]
    simpa [T, kc, hca, hcb] using hcount
  · simp [T, ka, kb, hab]
  · exact congrArg₂ (fun a b => (a, b, (none : Option (tm.Γ tm.k₀))))
      (fold_reg_fst (fun y => some y) (s.map ein.invFun).reverse v)
      (fold_reg_snd (fun y => some y) (s.map ein.invFun).reverse v)
  · intro k hka hkb
    simp [T, ka, kb, hka, hkb]

private def outerStk (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool)
    (C : List Bool) (S : ∀ k, List ((Base tm ein).Γ k)) :
    ∀ k, List (Gam tm ein k) :=
  fun k => match k with
    | .inl j => S j
    | .inr _ => C

private theorem outerStk_apply (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool)
    (C : List Bool) (S : ∀ k, List ((Base tm ein).Γ k)) (k : (Base tm ein).K) :
    outerStk tm ein C S (kBase k) = S k := by rfl

private theorem update_outerStk (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool)
    [DecidableEq (Base tm ein).K]
    (C : List Bool) (S : ∀ k, List ((Base tm ein).Γ k)) (k : (Base tm ein).K)
    (x : List ((Base tm ein).Γ k)) :
    Function.update (outerStk tm ein C S) (kBase k) x
      = outerStk tm ein C (Function.update S k x) := by
  funext j
  rcases j with j | u
  · by_cases h : j = k
    · subst h; simp [outerStk]
    · simp [outerStk, h]
  · cases u
    simp [outerStk]

private def redirectCfg (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool)
    (C : List Bool) (c : Cfg (Base tm ein).Γ (Base tm ein).Λ (Base tm ein).σ) :
    Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein) :=
  { l := some (c.l.elim (lStart tm ein) lBase)
    var := c.var
    stk := outerStk tm ein C c.stk }

/-- `liftStmt` is a step-exact simulation of a base statement, with the sole semantic change
that a base halt is redirected to the postprocessing entry label. -/
private theorem stepAux_liftStmt (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool)
    (C : List Bool) :
    ∀ (q : Stmt (Base tm ein).Γ (Base tm ein).Λ (Base tm ein).σ)
      (v : (Base tm ein).σ) (S : ∀ k, List ((Base tm ein).Γ k)),
      stepAux (liftStmt tm ein q) v (outerStk tm ein C S)
        = redirectCfg tm ein C (stepAux q v S) := by
  intro q
  induction q with
  | push k f q ih =>
      intro v S
      simp only [liftStmt, stepAux]
      rw [update_outerStk]
      exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      intro v S
      simp only [liftStmt, stepAux, outerStk_apply]
      exact ih (f v (S k).head?) S
  | pop k f q ih =>
      intro v S
      simp only [liftStmt, stepAux, outerStk_apply]
      rw [update_outerStk]
      exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih =>
      intro v S
      simp only [liftStmt, stepAux]
      exact ih (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
      intro v S
      simp only [liftStmt, stepAux]
      cases h : f v <;> simp only [h, cond_false, cond_true]
      · exact ih₂ v S
      · exact ih₁ v S
  | goto f =>
      intro v S
      rfl
  | halt =>
      intro v S
      rfl

private theorem iterate_redirect (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool)
    (W : Lam tm ein → Stmt (Gam tm ein) (Lam tm ein) (Sig tm ein))
    (M : (Base tm ein).Λ →
      Stmt (Base tm ein).Γ (Base tm ein).Λ (Base tm ein).σ)
    (C : List Bool) (n : ℕ)
    (c₀ : Cfg (Base tm ein).Γ (Base tm ein).Λ (Base tm ein).σ)
    (hshape : ∀ j < n, ∃ l v S,
      (fun c : Option (Cfg (Base tm ein).Γ (Base tm ein).Λ (Base tm ein).σ) =>
          c.bind (step M))^[j] (some c₀)
        = some ⟨some l, v, S⟩
      ∧ W (lBase l) = liftStmt tm ein (M l)) :
    (fun c : Option (Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein)) =>
        c.bind (step W))^[n] (some (redirectCfg tm ein C c₀))
      = ((fun c : Option (Cfg (Base tm ein).Γ (Base tm ein).Λ (Base tm ein).σ) =>
          c.bind (step M))^[n] (some c₀)).map (redirectCfg tm ein C) := by
  induction n generalizing c₀ with
  | zero => rfl
  | succ n ih =>
      obtain ⟨l, v, S, hc₀, hprog⟩ := hshape 0 (Nat.zero_lt_succ n)
      simp only [Function.iterate_zero_apply] at hc₀
      have hc₀' : c₀ = (⟨some l, v, S⟩ :
          Cfg (Base tm ein).Γ (Base tm ein).Λ (Base tm ein).σ) := by
        exact Option.some.inj hc₀
      subst c₀
      let c₁ := stepAux (M l) v S
      have hb : step M ⟨some l, v, S⟩ = some c₁ := by rfl
      have hw : step W (redirectCfg tm ein C ⟨some l, v, S⟩)
          = some (redirectCfg tm ein C c₁) := by
        change some (stepAux (W (lBase l)) v (outerStk tm ein C S)) = _
        rw [hprog, stepAux_liftStmt]
      have hshape₁ : ∀ j < n, ∃ l' v' S',
          (fun c : Option (Cfg (Base tm ein).Γ (Base tm ein).Λ (Base tm ein).σ) =>
            c.bind (step M))^[j] (some c₁)
            = some ⟨some l', v', S'⟩
          ∧ W (lBase l') = liftStmt tm ein (M l') := by
        intro j hj
        obtain ⟨l', v', S', hjrun, hjprog⟩ := hshape (j + 1) (by omega)
        refine ⟨l', v', S', ?_, hjprog⟩
        rw [Function.iterate_succ_apply, Option.bind_some, hb] at hjrun
        exact hjrun
      have hi := ih c₁ hshape₁
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Option.bind_some, hw, Option.bind_some, hb]
      exact hi

/-- A complete run of the original generator's second component is simulated step-for-step;
its halt is redirected to `lStart`, and the retained counter is unchanged throughout. -/
theorem second_component_redirects_halt (tm : Turing.FinTM2)
    (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool)
    (T : ∀ k, List ((Base tm ein).Γ k)) (C : List Bool)
    (w₁ : Id.σ) (r : Option (tm.Γ tm.k₀)) (n : ℕ)
    (l : tm.Λ) (v : tm.σ) (S : ∀ k, List (tm.Γ k))
    (u : List (tm.Γ tm.k₁))
    (hlive : ∀ j < n, ∃ l' v' S',
      (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[j]
        (some ⟨some l, v, S⟩)
        = some ⟨some l', v', S'⟩)
    (hfinal : (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[n]
      (some ⟨some l, v, S⟩)
        = some (Turing.haltList tm u)) :
    (fun c : Option (Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein)) =>
        c.bind (step (program tm ein eout)))^[n]
      (some (redirectCfg tm ein C
        (ShiTM2.liftCfg₂ Id tm T w₁ r ⟨some l, v, S⟩)))
      = some (redirectCfg tm ein C
          (ShiTM2.liftCfg₂ Id tm T w₁ r (Turing.haltList tm u))) := by
  let M := ShiTM2.compM Id tm ein.invFun (ein.invFun false)
  let c₀ := ShiTM2.liftCfg₂ Id tm T w₁ r
    (⟨some l, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ)
  have hshape : ∀ j < n, ∃ lb vb Sb,
      (fun c : Option (Cfg (Base tm ein).Γ (Base tm ein).Λ (Base tm ein).σ) =>
          c.bind (step M))^[j] (some c₀)
        = some ⟨some lb, vb, Sb⟩
      ∧ program tm ein eout (lBase lb) = liftStmt tm ein (M lb) := by
    intro j hj
    obtain ⟨l', v', S', hjtm⟩ := hlive j hj
    have hlivej : ∀ i < j, ∃ li vi Si,
        (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[i]
          (some ⟨some l, v, S⟩)
          = some ⟨some li, vi, Si⟩ := by
      intro i hi
      exact hlive i (lt_trans hi hj)
    obtain ⟨hjbase, _⟩ := ShiTM.iterate_compM_two_simulation Id tm
      ein.invFun (ein.invFun false) T w₁ r j l v S hlivej
    rw [hjtm] at hjbase
    refine ⟨ShiTM2.injΛ₂ Id tm l', (w₁, v', r),
      ShiTM2.liftStk₂ Id tm T S', ?_, ?_⟩
    · exact hjbase
    · rfl
  have houter := iterate_redirect tm ein (program tm ein eout) M C n c₀ hshape
  obtain ⟨hbase, _⟩ := ShiTM.iterate_compM_two_simulation Id tm
    ein.invFun (ein.invFun false) T w₁ r n l v S hlive
  dsimp only [M, c₀] at houter
  rw [hbase, hfinal] at houter
  exact houter

private theorem iter3 {A : Type} (f : A → A) (a b c : ℕ) (x y z u : A)
    (hxy : f^[a] x = y) (hyz : f^[b] y = z) (hzu : f^[c] z = u) :
    f^[a + b + c] x = u := by
  rw [show a + b + c = c + (b + a) from by omega,
    Function.iterate_add_apply f c (b + a), Function.iterate_add_apply f b a,
    hxy, hyz, hzu]

/-- Exact post-pass: prepend the retained input length to the generator output and empty the
protected counter.  This is the second half of the input-retention wrapper. -/
theorem postprocess_exact (tm : Turing.FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool)
    (eout : tm.Γ tm.k₁ ≃ Bool) (n : ℕ) (v : Sig tm ein)
    (S : ∀ k, List (Gam tm ein k))
    (hcount : S (kCount tm ein) = List.replicate n true) :
    ∃ (v' : Sig tm ein) (T : ∀ k, List (Gam tm ein k)),
      (fun cf : Option (Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein)) =>
          cf.bind (step (program tm ein eout)))^[n + 3]
        (some ⟨some (lStart tm ein), v, S⟩)
          = some ⟨none, v', T⟩
      ∧ T (kBase (ShiTM2.injK₂ Id tm tm.k₁))
          = List.append ((ShiBQP.encNat n).map eout.invFun)
              (S (kBase (ShiTM2.injK₂ Id tm tm.k₁)))
      ∧ T (kCount tm ein) = []
      ∧ v' = (v.1, v.2.1, none)
      ∧ ∀ k, k ≠ kBase (ShiTM2.injK₂ Id tm tm.k₁) →
          k ≠ kCount tm ein → T k = S k := by
  let ko : K tm ein := kBase (ShiTM2.injK₂ Id tm tm.k₁)
  let kc : K tm ein := kCount tm ein
  let M := program tm ein eout
  let F : Option (Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein)) →
      Option (Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein)) :=
    fun cf => cf.bind (step M)
  let S₁ : ∀ k, List (Gam tm ein k) :=
    Function.update S ko (eout.invFun false :: S ko)
  have hstart : F^[1] (some ⟨some (lStart tm ein), v, S⟩)
      = some ⟨some (lDrain tm ein), v, S₁⟩ := by
    rfl
  have hne : kc ≠ ko := by
    simp [kc, ko]
  have hS₁c : S₁ kc = List.replicate n true := by
    rw [show S₁ kc = S kc by
      exact Function.update_of_ne hne _ _]
    exact hcount
  let fp : Sig tm ein → Option Bool → Sig tm ein :=
    fun s o => (s.1, s.2.1, o.map (fun _ => ein.invFun true))
  let gt : Sig tm ein → Bool := ShiTM2.regIsSome Id tm
  let hp : Sig tm ein → Gam tm ein ko := fun _ => eout.invFun true
  let ee : Bool → Gam tm ein ko := fun _ => eout.invFun true
  obtain ⟨hloop, _⟩ := ShiTM.copy_loop_transfers_stack M hne
    (lc := lDrain tm ein) (lnext := lHalt tm ein)
    (fpop := fp) (gtest := gt) (hpush := hp) (e := ee)
    (hM := by rfl)
    (hcont := by intro w y; rfl)
    (hstop := by intro w; rfl)
    (hval := by intro w y; rfl)
    (List.replicate n true) v S₁ hS₁c
  let v' : Sig tm ein := fp
    ((List.replicate n true).foldl (fun w y => fp w (some y)) v) none
  let T : ∀ k, List (Gam tm ein k) :=
    Function.update (Function.update S₁ kc []) ko
      ((((List.replicate n true).map ee).reverse) ++ S₁ ko)
  have hloop' : F^[n + 1]
      (some ⟨some (lDrain tm ein), v, S₁⟩)
        = some ⟨some (lHalt tm ein), v', T⟩ := by
    rw [List.length_replicate] at hloop
    exact hloop
  have hhalt : F^[1] (some ⟨some (lHalt tm ein), v', T⟩)
      = some ⟨none, v', T⟩ := by
    rfl
  have hrun := iter3 F 1 (n + 1) 1 _ _ _ _ hstart hloop' hhalt
  refine ⟨v', T, ?_, ?_, ?_, ?_, ?_⟩
  · change F^[n + 3] _ = _
    rw [show n + 3 = 1 + (n + 1) + 1 by omega]
    exact hrun
  · simp [T, S₁, ko, kc, hne, ee, ShiBQP.encNat]
  · simp [T, ko, kc, hne]
  · exact congrArg₂ (fun a b => (a, b, (none : Option (tm.Γ tm.k₀))))
      (fold_reg_fst (fun _ : Bool => some (ein.invFun true)) (List.replicate n true) v)
      (fold_reg_snd (fun _ : Bool => some (ein.invFun true)) (List.replicate n true) v)
  · intro k hko hkc
    simp [T, S₁, ko, kc, hko, hkc]

/-- End-to-end from entry to the original generator through final length-prefixing.  The only
counter premise is the invariant supplied by `first_pass_retains_input_length`; no hypothesis
about recovering the input length from the generator output is used. -/
theorem generator_then_postprocess_exact (tm : Turing.FinTM2)
    (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool)
    (T : ∀ k, List ((Base tm ein).Γ k)) (m : ℕ)
    (w₁ : Id.σ) (r : Option (tm.Γ tm.k₀)) (n : ℕ)
    (l : tm.Λ) (v : tm.σ) (S : ∀ k, List (tm.Γ k))
    (u : List (tm.Γ tm.k₁))
    (hlive : ∀ j < n, ∃ l' v' S',
      (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[j]
        (some ⟨some l, v, S⟩)
        = some ⟨some l', v', S'⟩)
    (hfinal : (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[n]
      (some ⟨some l, v, S⟩)
        = some (Turing.haltList tm u)) :
    ∃ (v' : Sig tm ein) (U : ∀ k, List (Gam tm ein k)),
      (fun c : Option (Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein)) =>
          c.bind (step (program tm ein eout)))^[n + m + 3]
        (some (redirectCfg tm ein (List.replicate m true)
          (ShiTM2.liftCfg₂ Id tm T w₁ r ⟨some l, v, S⟩)))
        = some ⟨none, v', U⟩
      ∧ U (kBase (ShiTM2.injK₂ Id tm tm.k₁))
          = (ShiBQP.encNat m).map eout.invFun ++ u
      ∧ U (kCount tm ein) = []
      ∧ v' = (w₁, tm.initialState, none)
      ∧ ∀ k, k ≠ kBase (ShiTM2.injK₂ Id tm tm.k₁) →
          k ≠ kCount tm ein → U k =
            (redirectCfg tm ein (List.replicate m true)
              (ShiTM2.liftCfg₂ Id tm T w₁ r (Turing.haltList tm u))).stk k := by
  let C := List.replicate m true
  let cb := ShiTM2.liftCfg₂ Id tm T w₁ r (Turing.haltList tm u)
  let cw := redirectCfg tm ein C cb
  have hsim :
      (fun c : Option (Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein)) =>
          c.bind (step (program tm ein eout)))^[n]
        (some (redirectCfg tm ein C
          (ShiTM2.liftCfg₂ Id tm T w₁ r ⟨some l, v, S⟩)))
        = some cw := by
    exact second_component_redirects_halt tm ein eout T C w₁ r n l v S u hlive hfinal
  have hcwlabel : cw.l = some (lStart tm ein) := by rfl
  have hcwcount : cw.stk (kCount tm ein) = List.replicate m true := by rfl
  obtain ⟨v', U, hpost, hout, hcount, hv', hframe⟩ :=
    postprocess_exact tm ein eout m cw.var cw.stk hcwcount
  have hpost' :
      (fun c : Option (Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein)) =>
          c.bind (step (program tm ein eout)))^[m + 3] (some cw)
        = some ⟨none, v', U⟩ := by
    rw [show cw = ⟨some (lStart tm ein), cw.var, cw.stk⟩ by
      exact cfg_ext hcwlabel rfl rfl]
    exact hpost
  refine ⟨v', U, ?_, ?_, hcount, ?_, hframe⟩
  · rw [show n + m + 3 = (m + 3) + n by omega,
      Function.iterate_add_apply, hsim, hpost']
  · have hbaseout : cb.stk (ShiTM2.injK₂ Id tm tm.k₁) = u := by
      change (Turing.haltList tm u).stk tm.k₁ = u
      simp [Turing.haltList]
    have hcwout : cw.stk (kBase (ShiTM2.injK₂ Id tm tm.k₁)) = u := by
      exact hbaseout
    rw [hout, hcwout]
    rfl
  · rw [hv']
    rfl


/-- Full exact run of the protected-input wrapper, starting from its ordinary `initList`.
The overhead is `3 * |s| + 6`: one entry step, two copy passes, and the length-emission pass. -/
theorem machine_outputs_length_prefix_exact (tm : Turing.FinTM2)
    (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool)
    (s : List Bool) (u : List (tm.Γ tm.k₁)) (n : ℕ)
    (hlive : ∀ j < n, ∃ l' v' S',
      (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[j]
        (some (Turing.initList tm (s.map ein.invFun)))
        = some ⟨some l', v', S'⟩)
    (hfinal : (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[n]
      (some (Turing.initList tm (s.map ein.invFun)))
        = some (Turing.haltList tm u)) :
    ∃ (v' : Sig tm ein) (U : ∀ k, List (Gam tm ein k)),
      (fun c : Option (Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein)) =>
          c.bind (step (program tm ein eout)))^[n + 3 * s.length + 6]
        (some (Turing.initList (machine tm ein eout) s))
        = some ⟨none, v', U⟩
      ∧ U (kBase (ShiTM2.injK₂ Id tm tm.k₁))
          = (ShiBQP.encNat s.length).map eout.invFun ++ u
      ∧ v' = (machine tm ein eout).initialState
      ∧ ∀ k, k ≠ kBase (ShiTM2.injK₂ Id tm tm.k₁) → U k = [] := by
  let F : Option (Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein)) →
      Option (Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein)) :=
    fun c => c.bind (step (program tm ein eout))
  let c₀ := Turing.initList (machine tm ein eout) s
  let S₀ := c₀.stk
  have hi := ShiTM.initList_haltList_laws (machine tm ein eout) s []
  have hentry : F^[1] (some c₀) = some ⟨some (lBase (ShiTM2.lcopyA Id tm)), (Base tm ein).initialState, S₀⟩ := by
    rfl
  have hsrc : S₀ (kBase (ShiTM2.injK₁ Id tm Id.k₁)) = s := by
    exact hi.2.2.1
  have hs0scr : S₀ (kBase (ShiTM2.kScr Id tm)) = [] := by
    exact hi.2.2.2.1 _ (by simp)
  have hs0count : S₀ (kCount tm ein) = [] := by
    exact hi.2.2.2.1 _ (by simp)
  obtain ⟨v₁, S₁, hpass₁, hc₁, hscr₁, hsource₁, hv₁, hframe₁⟩ :=
    first_pass_retains_input_length tm ein eout s (Base tm ein).initialState S₀
      hsrc hs0count
  have hscr₁' : S₁ (kBase (ShiTM2.kScr Id tm)) = (s.map ein.invFun).reverse := by
    rw [hscr₁, hs0scr]
    exact List.append_nil _
  have hin₁ : S₁ (kBase (ShiTM2.injK₂ Id tm tm.k₀)) = [] := by
    rw [hframe₁ _ (by simp) (by simp) (by simp)]
    exact hi.2.2.2.1 _ (by simp)
  obtain ⟨v₂, S₂, hpass₂, hin₂, hc₂, hscratch₂, hv₂, hframe₂⟩ :=
    second_pass_preserves_counter tm ein eout s v₁ S₁ hscr₁' hin₁ hc₁
  let T : ∀ k, List ((Base tm ein).Γ k) := fun k => S₂ (kBase k)
  have hv₂' : v₂ = (Base tm ein).initialState := by
    rw [hv₂, hv₁]
  have htmstack : ∀ k, S₂ (kBase (ShiTM2.injK₂ Id tm k))
      = (Turing.initList tm (s.map ein.invFun)).stk k := by
    intro k
    by_cases hk : k = tm.k₀
    · subst hk
      rw [hin₂]
      exact (ShiTM.initList_haltList_laws tm (s.map ein.invFun) u).2.2.1.symm
    · rw [hframe₂ _ (by simp) (by simpa using hk),
        hframe₁ _ (by simp) (by simp) (by simp)]
      exact (hi.2.2.2.1 _ (by simp)).trans
        ((ShiTM.initList_haltList_laws tm (s.map ein.invFun) u).2.2.2.1 k hk).symm
  let cb := ShiTM2.liftCfg₂ Id tm T Id.initialState none
    (Turing.initList tm (s.map ein.invFun))
  have hc₂eq : (⟨some (lBase (ShiTM2.injΛ₂ Id tm tm.main)), v₂, S₂⟩ : Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein))
      = redirectCfg tm ein (List.replicate s.length true) cb := by
    apply cfg_ext
    · rfl
    · exact hv₂'
    · funext k
      rcases k with kb | z
      · rcases kb with i | q
        · rfl
        · rcases q with j | z
          · exact htmstack j
          · cases z; rfl
      · cases z; exact hc₂
  obtain ⟨vf, Sf, htail, hout, hfinalcount, hvf, hfinalframe⟩ :=
    generator_then_postprocess_exact tm ein eout T
    s.length Id.initialState none n tm.main tm.initialState
    (Turing.initList tm (s.map ein.invFun)).stk u
    (by
      intro j hj
      obtain ⟨l', v', S', h⟩ := hlive j hj
      exact ⟨l', v', S', by exact h⟩)
    (by exact hfinal)
  refine ⟨vf, Sf, ?_, hout, ?_, ?_⟩
  change F^[n + 3 * s.length + 6] (some c₀) = _
  have hpass₂' : F^[s.length + 1]
      (some ⟨some (lBase (ShiTM2.lcopyB Id tm)), v₁, S₁⟩)
      = some ⟨some (lBase (ShiTM2.injΛ₂ Id tm tm.main)), v₂, S₂⟩ := by
    simpa only [List.length_map] using hpass₂
  rw [show n + 3 * s.length + 6 =
      (n + s.length + 3) + ((s.length + 1) + ((s.length + 1) + 1)) by omega,
    Function.iterate_add_apply F (n + s.length + 3),
    Function.iterate_add_apply F (s.length + 1) ((s.length + 1) + 1),
    Function.iterate_add_apply F (s.length + 1) 1,
    hentry, hpass₁, hpass₂', hc₂eq]
  exact htail
  · exact hvf
  · intro k hkout
    by_cases hkcount : k = kCount tm ein
    · subst k
      exact hfinalcount
    · rw [hfinalframe k hkout hkcount]
      rcases k with kb | z
      · rcases kb with i | q
        · cases i
          change T (ShiTM2.injK₁ Id tm Id.k₁) = []
          change S₂ (kBase (ShiTM2.injK₁ Id tm Id.k₁)) = []
          rw [hframe₂ _ (by simp) (by simp), hsource₁]
        · rcases q with j | z
          · change (Turing.haltList tm u).stk j = []
            apply (ShiTM.initList_haltList_laws tm (s.map ein.invFun) u).2.2.2.2.2.2.2
            intro hj
            subst j
            exact hkout rfl
          · cases z
            change T (ShiTM2.kScr Id tm) = []
            exact hscratch₂
      · cases z
        exact (hkcount rfl).elim

private theorem exact_run_is_haltList (tm : Turing.FinTM2)
    (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool)
    (s : List Bool) (u : List (tm.Γ tm.k₁)) (n : ℕ)
    (hlive : ∀ j < n, ∃ l' v' S',
      (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[j]
        (some (Turing.initList tm (s.map ein.invFun)))
        = some ⟨some l', v', S'⟩)
    (hfinal : (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[n]
      (some (Turing.initList tm (s.map ein.invFun)))
        = some (Turing.haltList tm u)) :
    (fun c : Option (Cfg (Gam tm ein) (Lam tm ein) (Sig tm ein)) =>
        c.bind (step (program tm ein eout)))^[n + 3 * s.length + 6]
      (some (Turing.initList (machine tm ein eout) s))
      = some (Turing.haltList (machine tm ein eout)
          ((ShiBQP.encNat s.length).map eout.invFun ++ u)) := by
  obtain ⟨v', U, hrun, hout, hv, hother⟩ :=
    machine_outputs_length_prefix_exact tm ein eout s u n hlive hfinal
  rw [hrun]
  apply congrArg some
  apply cfg_ext
  · rfl
  · exact hv
  · funext k
    by_cases hk : k = kBase (ShiTM2.injK₂ Id tm tm.k₁)
    · subst k
      exact hout.trans (ShiTM.initList_haltList_laws (machine tm ein eout) []
        ((ShiBQP.encNat s.length).map eout.invFun ++ u)).2.2.2.2.2.2.1.symm
    · exact (hother k hk).trans ((ShiTM.initList_haltList_laws (machine tm ein eout) []
        ((ShiBQP.encNat s.length).map eout.invFun ++ u)).2.2.2.2.2.2.2 k hk).symm

private theorem iterate_none {A : Type} (f : A → Option A) (n : ℕ) :
    (fun c : Option A => c.bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply, Option.bind_none] using ih

private theorem no_early_death {K : Type} [DecidableEq K]
    {Γ : K → Type} {Λ σ : Type} (M : Λ → Stmt Γ Λ σ)
    (n : ℕ) (c₀ c : Cfg Γ Λ σ) (hlive₀ : ∃ l, c₀.l = some l)
    (h : (fun x : Option (Cfg Γ Λ σ) => x.bind (step M))^[n] (some c₀) = some c) :
    ∀ j < n, ∃ l' v' S',
      (fun x : Option (Cfg Γ Λ σ) => x.bind (step M))^[j] (some c₀)
        = some ⟨some l', v', S'⟩ := by
  intro j hj
  have hnon : ∀ i ≤ n,
      (fun x : Option (Cfg Γ Λ σ) => x.bind (step M))^[i] (some c₀) ≠ none := by
    intro i hi hdead
    obtain ⟨d, rfl⟩ : ∃ d, n = d + i := ⟨n - i, by omega⟩
    rw [Function.iterate_add_apply, hdead, iterate_none] at h
    exact Option.some_ne_none c h.symm
  cases hjrun : (fun x : Option (Cfg Γ Λ σ) => x.bind (step M))^[j]
      (some c₀) with
  | none => exact (hnon j (Nat.le_of_lt hj) hjrun).elim
  | some cj =>
      rcases cj with ⟨lj, vj, Sj⟩
      cases lj with
      | none =>
          exfalso
          apply hnon (j + 1) (by omega)
          rw [Function.iterate_succ_apply', hjrun]
          rfl
      | some lj => exact ⟨lj, vj, Sj, rfl⟩

/-- The wrapper lifts any bounded run of `tm` to a bounded run producing the length-prefixed
output.  Its additive overhead is linear in the external input length. -/
theorem outputsInTime_length_prefix (tm : Turing.FinTM2)
    (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool)
    (s : List Bool) (u : List (tm.Γ tm.k₁)) (bound : ℕ)
    (h : Turing.TM2OutputsInTime tm (s.map ein.invFun) (some u) bound) :
    Nonempty (Turing.TM2OutputsInTime (machine tm ein eout) s
      (some ((ShiBQP.encNat s.length).map eout.invFun ++ u))
      (bound + 3 * s.length + 6)) := by
  have h' : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm (s.map ein.invFun)) (some (Turing.haltList tm u)) bound := h
  obtain ⟨⟨n, hn⟩, hnle⟩ := h'
  change n ≤ bound at hnle
  have hn' :
      (fun c : Option (Cfg tm.Γ tm.Λ tm.σ) => c.bind (step tm.m))^[n]
        (some (Turing.initList tm (s.map ein.invFun)))
        = some (Turing.haltList tm u) := by
    exact hn
  have hinitlive : ∃ l, (Turing.initList tm (s.map ein.invFun)).l = some l :=
    ⟨tm.main, rfl⟩
  have hlive := no_early_death tm.m n (Turing.initList tm (s.map ein.invFun))
    (Turing.haltList tm u) hinitlive hn'
  have hrun := exact_run_is_haltList tm ein eout s u n hlive hn'
  refine ⟨{ steps := n + 3 * s.length + 6, evals_in_steps := ?_, steps_le_m := by omega }⟩
  exact hrun

/-- Polynomial-time functions remain polynomial-time after prefixing their input length. -/
theorem polyTimeComputable_length_prefix (f : PvsNP.Str → PvsNP.Str) :
    PvsNP.PolyTimeComputable f →
      PvsNP.PolyTimeComputable (fun s => ShiBQP.encNat s.length ++ f s) := by
  classical
  rintro ⟨h⟩
  let p : Polynomial ℕ :=
    h.time + Polynomial.C 3 * Polynomial.X + Polynomial.C 6
  refine ⟨{
    tm := machine h.tm h.inputAlphabet h.outputAlphabet
    inputAlphabet := inputAlphabet h.tm h.inputAlphabet h.outputAlphabet
    outputAlphabet := outputAlphabet h.tm h.inputAlphabet h.outputAlphabet
    time := p
    outputsFun := ?_ }⟩
  intro s
  have hw := outputsInTime_length_prefix h.tm h.inputAlphabet h.outputAlphabet s
    (List.map h.outputAlphabet.invFun (f s)) (h.time.eval s.length) (h.outputsFun s)
  let hw := Classical.choice hw
  have hp : p.eval s.length = h.time.eval s.length + 3 * s.length + 6 := by
    simp [p, Polynomial.eval_add, Polynomial.eval_mul]
  change Turing.TM2OutputsInTime _ _ _ (p.eval s.length)
  rw [hp]
  simpa [inputAlphabet, outputAlphabet, PvsNP.Str, List.map_append] using hw

/-- The original literature-style uniform generator can always be replaced by a generator
whose output explicitly retains the unary input length.  Thus length-aware uniformity adds no
hypothesis to QMA amplification. -/
theorem uniformQMA_has_length_aware_generator (F : ShiClassQMA.QMAFamily) :
    ShiClassQMAU.UniformQMA F →
      ∃ f : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable f ∧
        ∀ n : ℕ,
          f (ShiBQP.unary n) =
            ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n := by
  rintro ⟨f, hf, hout⟩
  refine ⟨fun s => ShiBQP.encNat s.length ++ f s,
    polyTimeComputable_length_prefix f hf, ?_⟩
  intro n
  change ShiBQP.encNat (ShiBQP.unary n).length ++ f (ShiBQP.unary n) = _
  rw [hout]
  simp [ShiBQP.unary]

open ShiShallow ShiClassQMA ShiClassQMAAmp ShiClassQMAAmpX

private theorem uniform_ampFamilyX_of_retained_transducer
    (F : QMAFamily) (g : PvsNP.Str → PvsNP.Str)
    (hg : PvsNP.PolyTimeComputable g)
    (hmap : ∀ n : ℕ,
      g (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n)
        = ShiClassQMAU.encQMAFamilyAt (ampFamilyX F) n) :
    ShiClassQMAU.UniformQMA F → ShiClassQMAU.UniformQMA (ampFamilyX F) := by
  intro hF
  obtain ⟨f, hf, hout⟩ := uniformQMA_has_length_aware_generator F hF
  refine ⟨g ∘ f, PvsNP.polyTimeComputable_comp f g hf hg, ?_⟩
  intro n
  rw [Function.comp_apply, hout, hmap]

private theorem acceptWith_ampFamilyX_eq (F : QMAFamily) {n : ℕ} (x : Bits n)
    (ψ : QState ((ampFamily F).wit n)) :
    (ampFamilyX F).acceptWith x ψ = (ampFamily F).acceptWith x ψ := by
  unfold QMAFamily.acceptWith
  change
    (∑ y : Bits (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))),
      if y ((ampFamily F).out n) then
        ‖runLayered ((ampFamilyX F).circ n) (witnessInputState (ampFamily F) x ψ) y‖ ^ 2
      else 0)
      = ∑ y : Bits (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))),
          if y ((ampFamily F).out n) then
            ‖runLayered ((ampFamily F).circ n) (witnessInputState (ampFamily F) x ψ) y‖ ^ 2
          else 0
  rw [ampFamilyX_semantically_eq_ampFamily]

/-- Original `QMAU` amplification with no extra length-awareness assumption.  The sole remaining
premise is the concrete polynomial-time transformer on retained encodings. -/
theorem qmaU_amplification_of_retained_encoding_transducer
    (htrans : ∀ F : QMAFamily, ∃ g : PvsNP.Str → PvsNP.Str,
      PvsNP.PolyTimeComputable g ∧ ∀ n : ℕ,
        g (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n)
          = ShiClassQMAU.encQMAFamilyAt (ampFamilyX F) n) :
    ShiClassQMAU.QMAU ((2 : ℝ) / 3) ((1 : ℝ) / 3) ⊆
      ShiClassQMAU.QMAU ((20 : ℝ) / 27) ((7 : ℝ) / 27) := by
  intro L hL
  obtain ⟨F, huniform, hwf, hpoly, hverify⟩ := hL
  obtain ⟨g, hg, hmap⟩ := htrans F
  refine ⟨ampFamilyX F,
    uniform_ampFamilyX_of_retained_transducer F g hg hmap huniform,
    ampFamilyX_resource_identities_and_regularity.2.2.2.2.1 F hwf,
    ampFamilyX_resource_identities_and_regularity.2.2.2.2.2.1 F hpoly, ?_⟩
  intro w
  constructor
  · intro hw
    obtain ⟨ψ, hψ, hb⟩ := (hverify w).1 hw
    obtain ⟨Ψ, hΨ, hamp⟩ :=
      ShiClassQMA.exists_amplified_witness_maj3_ge_of_single_copy_bound
        ampFamily
        ShiClassQMAAmp.ampFamily_resource_identities_and_depth.1
        ShiClassQMAAmp.ampFamily_resource_identities_and_depth.2.1
        ShiClassQMAAmp.ampFamily_resource_identities_and_depth.2.2.1
        ShiClassQMAAmp.ampFamily_threefold_structure_package.1
        ((2 : ℝ) / 3) (by norm_num) (by norm_num) F w ⟨ψ, hψ, hb⟩
    refine ⟨Ψ, hΨ, ?_⟩
    calc
      (20 : ℝ) / 27 = 3 * ((2 : ℝ) / 3) ^ 2 - 2 * ((2 : ℝ) / 3) ^ 3 := by norm_num
      _ ≤ (ampFamily F).acceptWith (ShiBQP.toBits w) Ψ := hamp
      _ = (ampFamilyX F).acceptWith (ShiBQP.toBits w) Ψ :=
        (acceptWith_ampFamilyX_eq F _ Ψ).symm
  · intro hw Ψ hΨ
    have hamp := ShiClassQMA.amplified_acceptWith_le_maj3_of_single_copy_bound
      ampFamily
      ShiClassQMAAmp.ampFamily_resource_identities_and_depth.1
      ShiClassQMAAmp.ampFamily_resource_identities_and_depth.2.1
      ShiClassQMAAmp.ampFamily_resource_identities_and_depth.2.2.1
      ShiClassQMAAmp.ampFamily_threefold_structure_package.1
      ((1 : ℝ) / 3) (by norm_num) (by norm_num) F w ((hverify w).2 hw) Ψ hΨ
    calc
      (ampFamilyX F).acceptWith (ShiBQP.toBits w) Ψ
          = (ampFamily F).acceptWith (ShiBQP.toBits w) Ψ :=
            acceptWith_ampFamilyX_eq F _ Ψ
      _ ≤ 3 * ((1 : ℝ) / 3) ^ 2 - 2 * ((1 : ℝ) / 3) ^ 3 := hamp
      _ = (7 : ℝ) / 27 := by norm_num

end ShiTMInputRetention
