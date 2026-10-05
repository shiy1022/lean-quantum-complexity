import Definitions.Def_PvsNP
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_PvsNP_tagged_transducers_untaggers_and_projections
import Theorems.Thm_ShiTM_initList_haltList_laws
import Theorems.Thm_ShiTM_outputsInTime_of_run_to_halt

namespace BQPReferenceValidation.Source3
/-
TRANSDUCE-2.  A GENERAL SYMBOLWISE TRANSDUCER over the tagged input alphabet `Bool ⊕ Bool`
and an ARBITRARY finite output alphabet: for every `φ : Bool ⊕ Bool → List Γo` there is a
three-stack machine which, started with `s` on its input stack, halts with `s.flatMap φ` on
its output stack in `|s| + |s.flatMap φ| + 3` steps.

WHY THIS SHAPE.  A single `Turing.TM2.Stmt` is a finite TREE of pushes, so one step can emit
more than one symbol but never a number of symbols depending on the input length.  Making the
per-symbol output `φ c` an arbitrary FINITE LIST is therefore exactly the right generality:
it is realised by a fixed four-way branch (the four elements of `Bool ⊕ Bool`) whose arms are
the fixed push chains `emit (φ c)`.  Nothing weaker suffices for the untagger, where
`|φ c| ∈ {0,1}` varies with `c`; nothing stronger is implementable by one statement.

THE MACHINE.  Three stacks `Sin, Sscr, Sout` (`k₀ = Sin`, `k₁ = Sout`, alphabets
`Bool ⊕ Bool`, `Γo`, `Γo`), THREE labels `l1, l2, lh`, and state register
`Option (Bool ⊕ Bool) × Option Γo`:

    l1 : pop Sin into the left register; if empty goto l2, else branch on the four symbols
         and push the fixed list `φ c` onto Sscr, goto l1
    l2 : pop Sscr into the right register; if empty goto lh, else push it onto Sout, goto l2
    lh : halt

A pop/push pass REVERSES, so the loop at `l1` leaves `(s.flatMap φ).reverse` on the scratch
stack and the loop at `l2` reverses it back: two passes, faithful transfer.  Pushing `φ c` in
order makes the first pass accumulate `(φ c).reverse` on top of what is already there, which
is `((c :: t).flatMap φ).reverse` exactly because `reverse` is an anti-homomorphism.

THE OUTPUT-LENGTH BOUND is conjunct (2) and is what discharges the intermediate-length
hypothesis `q` of any polynomial-time composition lemma: `|s.flatMap φ| ≤ M * |s|` whenever
`M` bounds every `|φ c|`.  Conjunct (3) records that the `|φ c| ≤ 1` case is exactly
`List.filterMap`, i.e. the untagger/retagger/tag-flip family.

THE CONSUMERS.  Conjunct (1) is the polynomial-time certificate at an arbitrary output
alphabet and an arbitrary target encoding; conjuncts (2)-(3) instantiate it at the UNTAGGERS
`Bool ⊕ Bool → Bool`, which is precisely the hypothesis
`Nonempty (TM2ComputableInPolyTime encodePair id u)` of the accepted alphabet bridge, and
conjunct (4) is the length bound that discharges that bridge's `q` at `q = X`.  Chaining
(2) and (4) into the bridge turns EVERY polynomial-time decision procedure on plain strings
into a polynomial-time checking relation; that chaining is the bridge's job, not this
file's.

NOT CLAIMED: nothing about a machine that runs a component on PART of its input while the
rest survives; sequential composition consumes its input, and that gap needs a different
composite, not a different transducer.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Turing Turing.TM2

/-! ### 0.  List arithmetic -/

private lemma fmNil {α β : Type} (f : α → List β) : ([] : List α).flatMap f = [] := by simp

private lemma fmCons {α β : Type} (f : α → List β) (a : α) (l : List α) :
    (a :: l).flatMap f = f a ++ l.flatMap f := by simp

private lemma flatMapLen {Γo : Type} (φ : Bool ⊕ Bool → List Γo) (M : ℕ)
    (hM : ∀ c, (φ c).length ≤ M) :
    ∀ L : List (Bool ⊕ Bool), (L.flatMap φ).length ≤ M * L.length := by
  intro L
  induction L with
  | nil => rw [fmNil]; simp
  | cons c t ih =>
      rw [fmCons, List.length_append, List.length_cons, Nat.mul_succ]
      have h := hM c
      omega

private lemma flatMapToList {Γo : Type} (ψ : Bool ⊕ Bool → Option Γo) :
    ∀ L : List (Bool ⊕ Bool), L.flatMap (fun c => (ψ c).toList) = L.filterMap ψ := by
  intro L
  induction L with
  | nil => rfl
  | cons c t ih =>
      rw [fmCons, ih, List.filterMap_cons]
      cases h : ψ c with
      | none => simp
      | some b => simp

/-! ### 1.  The machine datum: three stacks, three labels -/

private inductive TStk : Type
  | Sin | Sscr | Sout
  deriving DecidableEq

private instance : Fintype TStk where
  elems := ⟨[TStk.Sin, TStk.Sscr, TStk.Sout], by decide⟩
  complete := fun x => by cases x <;> decide

@[reducible] private def TGam (Γo : Type) : TStk → Type
  | TStk.Sin => Bool ⊕ Bool
  | TStk.Sscr => Γo
  | TStk.Sout => Γo

private inductive TLbl : Type
  | l1 | l2 | lh
  deriving DecidableEq

private instance : Fintype TLbl where
  elems := ⟨[TLbl.l1, TLbl.l2, TLbl.lh], by decide⟩
  complete := fun x => by cases x <;> decide

private abbrev TSg (Γo : Type) : Type := Option (Bool ⊕ Bool) × Option Γo

/-- The fixed push chain emitting a finite list onto the scratch stack. -/
private def emit {Γo : Type} (l : List Γo) (cont : Stmt (TGam Γo) TLbl (TSg Γo)) :
    Stmt (TGam Γo) TLbl (TSg Γo) :=
  l.foldr (fun b s => Stmt.push TStk.Sscr (fun _ => b) s) cont

private def isSm {Γo : Type} (v : TSg Γo) : Bool := v.1.isSome

private def isInlB {Γo : Type} (v : TSg Γo) : Bool :=
  match v.1 with
  | Option.some (Sum.inl _) => true
  | _ => false

private def bitB {Γo : Type} (v : TSg Γo) : Bool :=
  match v.1 with
  | Option.some (Sum.inl b) => b
  | Option.some (Sum.inr b) => b
  | Option.none => false

/-- The four-way dispatch on the popped input symbol. -/
private def tbody {Γo : Type} (φ : Bool ⊕ Bool → List Γo) : Stmt (TGam Γo) TLbl (TSg Γo) :=
  Stmt.branch isSm
    (Stmt.branch isInlB
      (Stmt.branch bitB
        (emit (φ (Sum.inl true)) (Stmt.goto (fun _ => TLbl.l1)))
        (emit (φ (Sum.inl false)) (Stmt.goto (fun _ => TLbl.l1))))
      (Stmt.branch bitB
        (emit (φ (Sum.inr true)) (Stmt.goto (fun _ => TLbl.l1)))
        (emit (φ (Sum.inr false)) (Stmt.goto (fun _ => TLbl.l1)))))
    (Stmt.goto (fun _ => TLbl.l2))

private def tprog {Γo : Type} [Inhabited Γo] (φ : Bool ⊕ Bool → List Γo) :
    TLbl → Stmt (TGam Γo) TLbl (TSg Γo)
  | TLbl.l1 => Stmt.pop TStk.Sin (fun _ o => (o, Option.none)) (tbody φ)
  | TLbl.l2 =>
      Stmt.pop TStk.Sscr (fun _ o => (Option.none, o))
        (Stmt.branch (fun v : TSg Γo => v.2.isSome)
          (Stmt.push TStk.Sout (fun v : TSg Γo => v.2.getD default)
            (Stmt.goto (fun _ => TLbl.l2)))
          (Stmt.goto (fun _ => TLbl.lh)))
  | TLbl.lh => Stmt.halt

private lemma tprog_l1 {Γo : Type} [Inhabited Γo] (φ : Bool ⊕ Bool → List Γo) :
    tprog φ TLbl.l1 = Stmt.pop TStk.Sin (fun _ o => (o, Option.none)) (tbody φ) := rfl

private lemma tprog_l2 {Γo : Type} [Inhabited Γo] (φ : Bool ⊕ Bool → List Γo) :
    tprog φ TLbl.l2 =
      Stmt.pop TStk.Sscr (fun _ o => (Option.none, o))
        (Stmt.branch (fun v : TSg Γo => v.2.isSome)
          (Stmt.push TStk.Sout (fun v : TSg Γo => v.2.getD default)
            (Stmt.goto (fun _ => TLbl.l2)))
          (Stmt.goto (fun _ => TLbl.lh))) := rfl

@[reducible] private def TMt {Γo : Type} [Inhabited Γo] [Fintype Γo]
    (φ : Bool ⊕ Bool → List Γo) : Turing.FinTM2 where
  K := TStk
  k₀ := TStk.Sin
  k₁ := TStk.Sout
  Γ := TGam Γo
  Λ := TLbl
  main := TLbl.l1
  σ := TSg Γo
  initialState := (Option.none, Option.none)
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := tprog φ

/-! ### 2.  The emission chain and the four-way dispatch -/

private lemma emitStep {Γo : Type} (cont : Stmt (TGam Γo) TLbl (TSg Γo)) :
    ∀ (l : List Γo) (v : TSg Γo) (S : ∀ k, List (TGam Γo k)),
      TM2.stepAux (emit l cont) v S
        = TM2.stepAux cont v (Function.update S TStk.Sscr (l.reverse ++ S TStk.Sscr)) := by
  intro l
  induction l with
  | nil =>
      intro v S
      have h : Function.update S TStk.Sscr (S TStk.Sscr) = S := Function.update_eq_self _ _
      have h0 : emit ([] : List Γo) cont = cont := rfl
      rw [h0, List.reverse_nil, List.nil_append, h]
  | cons b t ih =>
      intro v S
      have h0 : emit (b :: t) cont
          = Stmt.push TStk.Sscr (fun _ => (b : TGam Γo TStk.Sscr)) (emit t cont) := rfl
      rw [h0]
      show TM2.stepAux (emit t cont) v (Function.update S TStk.Sscr (b :: S TStk.Sscr)) = _
      rw [ih v (Function.update S TStk.Sscr (b :: S TStk.Sscr)), Function.update_self,
        Function.update_idem]
      have h1 : t.reverse ++ b :: S TStk.Sscr = (b :: t).reverse ++ S TStk.Sscr := by simp
      rw [h1]

private lemma tbodySome {Γo : Type} (φ : Bool ⊕ Bool → List Γo) (c : Bool ⊕ Bool)
    (S : ∀ k, List (TGam Γo k)) :
    TM2.stepAux (tbody φ) ((Option.some c, Option.none) : TSg Γo) S
      = TM2.stepAux (emit (φ c) (Stmt.goto (fun _ => TLbl.l1)))
          ((Option.some c, Option.none) : TSg Γo) S := by
  rcases c with b | b <;> cases b <;> rfl

private lemma tbodyNone {Γo : Type} (φ : Bool ⊕ Bool → List Γo) (w : Option Γo)
    (S : ∀ k, List (TGam Γo k)) :
    TM2.stepAux (tbody φ) ((Option.none, w) : TSg Γo) S
      = (⟨Option.some TLbl.l2, (Option.none, w), S⟩ : Cfg (TGam Γo) TLbl (TSg Γo)) := rfl

/-! ### 3.  Pass one: read the input, emit onto the scratch stack -/

private lemma loop1 {Γo : Type} [Inhabited Γo] (φ : Bool ⊕ Bool → List Γo) :
    ∀ (L : List (Bool ⊕ Bool)) (S : ∀ k, List (TGam Γo k)) (v : TSg Γo), S TStk.Sin = L →
      (fun cf : Option (Cfg (TGam Γo) TLbl (TSg Γo)) => cf.bind (TM2.step (tprog φ)))^[
          L.length + 1] (Option.some ⟨Option.some TLbl.l1, v, S⟩)
        = Option.some ⟨Option.some TLbl.l2, (Option.none, Option.none),
            Function.update (Function.update S TStk.Sin []) TStk.Sscr
              ((L.flatMap φ).reverse ++ S TStk.Sscr)⟩ := by
  intro L
  induction L with
  | nil =>
      intro S v hS
      have e1 : TM2.step (tprog φ) (⟨Option.some TLbl.l1, v, S⟩ : Cfg (TGam Γo) TLbl (TSg Γo))
          = Option.some ⟨Option.some TLbl.l2, (Option.none, Option.none),
              Function.update S TStk.Sin []⟩ := by
        have h0 : TM2.step (tprog φ)
              (⟨Option.some TLbl.l1, v, S⟩ : Cfg (TGam Γo) TLbl (TSg Γo))
            = Option.some (TM2.stepAux (tprog φ TLbl.l1) v S) := rfl
        rw [h0, tprog_l1]
        show Option.some (TM2.stepAux (tbody φ) ((S TStk.Sin).head?, Option.none)
          (Function.update S TStk.Sin (S TStk.Sin).tail)) = _
        rw [hS, List.head?_nil, List.tail_nil, tbodyNone]
      have h2 : Function.update (Function.update S TStk.Sin ([] : List (TGam Γo TStk.Sin)))
            TStk.Sscr (S TStk.Sscr) = Function.update S TStk.Sin [] := by
        have h3 : Function.update S TStk.Sin ([] : List (TGam Γo TStk.Sin)) TStk.Sscr
            = S TStk.Sscr := Function.update_of_ne (by decide) _ _
        rw [← h3]
        exact Function.update_eq_self _ _
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one]
      rw [show (Option.some (⟨Option.some TLbl.l1, v, S⟩ : Cfg (TGam Γo) TLbl (TSg Γo))).bind
            (TM2.step (tprog φ)) = TM2.step (tprog φ) ⟨Option.some TLbl.l1, v, S⟩ from rfl, e1,
        fmNil, List.reverse_nil, List.nil_append, h2]
  | cons c t ih =>
      intro S v hS
      have e1 : TM2.step (tprog φ) (⟨Option.some TLbl.l1, v, S⟩ : Cfg (TGam Γo) TLbl (TSg Γo))
          = Option.some ⟨Option.some TLbl.l1, (Option.some c, Option.none),
              Function.update (Function.update S TStk.Sin t) TStk.Sscr
                ((φ c).reverse ++ S TStk.Sscr)⟩ := by
        have h0 : TM2.step (tprog φ)
              (⟨Option.some TLbl.l1, v, S⟩ : Cfg (TGam Γo) TLbl (TSg Γo))
            = Option.some (TM2.stepAux (tprog φ TLbl.l1) v S) := rfl
        rw [h0, tprog_l1]
        show Option.some (TM2.stepAux (tbody φ) ((S TStk.Sin).head?, Option.none)
          (Function.update S TStk.Sin (S TStk.Sin).tail)) = _
        rw [hS, List.head?_cons, List.tail_cons, tbodySome, emitStep]
        have h4 : Function.update S TStk.Sin t TStk.Sscr = S TStk.Sscr :=
          Function.update_of_ne (by decide) _ _
        rw [h4]
        rfl
      set S2 : ∀ k, List (TGam Γo k) :=
        Function.update (Function.update S TStk.Sin t) TStk.Sscr
          ((φ c).reverse ++ S TStk.Sscr) with hS2
      have hS2in : S2 TStk.Sin = t := by
        rw [hS2, Function.update_of_ne (by decide : TStk.Sin ≠ TStk.Sscr),
          Function.update_self]
      have hS2scr : S2 TStk.Sscr = (φ c).reverse ++ S TStk.Sscr := by
        rw [hS2, Function.update_self]
      have hlen : ((c :: t).length + 1) = (t.length + 1) + 1 := by simp
      rw [hlen, Function.iterate_succ_apply]
      rw [show (Option.some (⟨Option.some TLbl.l1, v, S⟩ : Cfg (TGam Γo) TLbl (TSg Γo))).bind
            (TM2.step (tprog φ)) = TM2.step (tprog φ) ⟨Option.some TLbl.l1, v, S⟩ from rfl, e1]
      rw [ih S2 (Option.some c, Option.none) hS2in]
      have hlist : (t.flatMap φ).reverse ++ S2 TStk.Sscr
          = ((c :: t).flatMap φ).reverse ++ S TStk.Sscr := by
        rw [hS2scr, fmCons, List.reverse_append, List.append_assoc]
      have hfun : Function.update (Function.update S2 TStk.Sin []) TStk.Sscr
            ((t.flatMap φ).reverse ++ S2 TStk.Sscr)
          = Function.update (Function.update S TStk.Sin []) TStk.Sscr
            (((c :: t).flatMap φ).reverse ++ S TStk.Sscr) := by
        rw [hlist]
        funext j
        by_cases h1 : j = TStk.Sscr
        · subst h1
          rw [Function.update_self, Function.update_self]
        · by_cases h2 : j = TStk.Sin
          · subst h2
            rw [Function.update_of_ne h1, Function.update_of_ne h1, Function.update_self,
              Function.update_self]
          · rw [Function.update_of_ne h1, Function.update_of_ne h1, Function.update_of_ne h2,
              Function.update_of_ne h2, hS2, Function.update_of_ne h1,
              Function.update_of_ne h2]
      exact congrArg (fun T => (Option.some (⟨Option.some TLbl.l2,
        ((Option.none : Option (Bool ⊕ Bool)), (Option.none : Option Γo)), T⟩ :
          Cfg (TGam Γo) TLbl (TSg Γo)))) hfun

/-! ### 4.  Pass two: reverse the scratch stack onto the output stack -/

private lemma loop2 {Γo : Type} [Inhabited Γo] (φ : Bool ⊕ Bool → List Γo) :
    ∀ (L : List Γo) (S : ∀ k, List (TGam Γo k)) (v : TSg Γo), S TStk.Sscr = L →
      (fun cf : Option (Cfg (TGam Γo) TLbl (TSg Γo)) => cf.bind (TM2.step (tprog φ)))^[
          L.length + 1] (Option.some ⟨Option.some TLbl.l2, v, S⟩)
        = Option.some ⟨Option.some TLbl.lh, (Option.none, Option.none),
            Function.update (Function.update S TStk.Sscr []) TStk.Sout
              (L.reverse ++ S TStk.Sout)⟩ := by
  intro L
  induction L with
  | nil =>
      intro S v hS
      have e1 : TM2.step (tprog φ) (⟨Option.some TLbl.l2, v, S⟩ : Cfg (TGam Γo) TLbl (TSg Γo))
          = Option.some ⟨Option.some TLbl.lh, (Option.none, Option.none),
              Function.update S TStk.Sscr []⟩ := by
        have h0 : TM2.step (tprog φ)
              (⟨Option.some TLbl.l2, v, S⟩ : Cfg (TGam Γo) TLbl (TSg Γo))
            = Option.some (TM2.stepAux (tprog φ TLbl.l2) v S) := rfl
        rw [h0, tprog_l2]
        simp only [TM2.stepAux, hS, List.head?_nil, List.tail_nil, Option.isSome_none,
          cond_false]
      have h2 : Function.update (Function.update S TStk.Sscr ([] : List (TGam Γo TStk.Sscr)))
            TStk.Sout (S TStk.Sout) = Function.update S TStk.Sscr [] := by
        have h3 : Function.update S TStk.Sscr ([] : List (TGam Γo TStk.Sscr)) TStk.Sout
            = S TStk.Sout := Function.update_of_ne (by decide) _ _
        rw [← h3]
        exact Function.update_eq_self _ _
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one]
      rw [show (Option.some (⟨Option.some TLbl.l2, v, S⟩ : Cfg (TGam Γo) TLbl (TSg Γo))).bind
            (TM2.step (tprog φ)) = TM2.step (tprog φ) ⟨Option.some TLbl.l2, v, S⟩ from rfl, e1,
        List.reverse_nil, List.nil_append, h2]
  | cons b t ih =>
      intro S v hS
      have e1 : TM2.step (tprog φ) (⟨Option.some TLbl.l2, v, S⟩ : Cfg (TGam Γo) TLbl (TSg Γo))
          = Option.some ⟨Option.some TLbl.l2, (Option.none, Option.some b),
              Function.update (Function.update S TStk.Sscr t) TStk.Sout
                (b :: S TStk.Sout)⟩ := by
        have h0 : TM2.step (tprog φ)
              (⟨Option.some TLbl.l2, v, S⟩ : Cfg (TGam Γo) TLbl (TSg Γo))
            = Option.some (TM2.stepAux (tprog φ TLbl.l2) v S) := rfl
        rw [h0, tprog_l2]
        simp only [TM2.stepAux, hS, List.head?_cons, List.tail_cons, Option.isSome_some,
          cond_true, Option.getD_some,
          Function.update_of_ne (by decide : TStk.Sout ≠ TStk.Sscr)]
      set S2 : ∀ k, List (TGam Γo k) :=
        Function.update (Function.update S TStk.Sscr t) TStk.Sout (b :: S TStk.Sout) with hS2
      have hS2scr : S2 TStk.Sscr = t := by
        rw [hS2, Function.update_of_ne (by decide : TStk.Sscr ≠ TStk.Sout),
          Function.update_self]
      have hS2out : S2 TStk.Sout = b :: S TStk.Sout := by rw [hS2, Function.update_self]
      have hlen : ((b :: t).length + 1) = (t.length + 1) + 1 := by simp
      rw [hlen, Function.iterate_succ_apply]
      rw [show (Option.some (⟨Option.some TLbl.l2, v, S⟩ : Cfg (TGam Γo) TLbl (TSg Γo))).bind
            (TM2.step (tprog φ)) = TM2.step (tprog φ) ⟨Option.some TLbl.l2, v, S⟩ from rfl, e1]
      rw [ih S2 (Option.none, Option.some b) hS2scr]
      have hlist : t.reverse ++ S2 TStk.Sout = (b :: t).reverse ++ S TStk.Sout := by
        rw [hS2out, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      have hfun : Function.update (Function.update S2 TStk.Sscr []) TStk.Sout
            (t.reverse ++ S2 TStk.Sout)
          = Function.update (Function.update S TStk.Sscr []) TStk.Sout
            ((b :: t).reverse ++ S TStk.Sout) := by
        rw [hlist]
        funext j
        by_cases h1 : j = TStk.Sout
        · subst h1
          rw [Function.update_self, Function.update_self]
        · by_cases h2 : j = TStk.Sscr
          · subst h2
            rw [Function.update_of_ne h1, Function.update_of_ne h1, Function.update_self,
              Function.update_self]
          · rw [Function.update_of_ne h1, Function.update_of_ne h1, Function.update_of_ne h2,
              Function.update_of_ne h2, hS2, Function.update_of_ne h1,
              Function.update_of_ne h2]
      exact congrArg (fun T => (Option.some (⟨Option.some TLbl.lh,
        ((Option.none : Option (Bool ⊕ Bool)), (Option.none : Option Γo)), T⟩ :
          Cfg (TGam Γo) TLbl (TSg Γo)))) hfun

/-! ### 5.  The whole run -/

private lemma transRun {Γo : Type} [Inhabited Γo] [Fintype Γo] (φ : Bool ⊕ Bool → List Γo)
    (inp : List (Bool ⊕ Bool)) :
    Nonempty (Turing.TM2OutputsInTime (TMt φ) inp (Option.some (inp.flatMap φ))
      (inp.length + (inp.flatMap φ).length + 3)) := by
  classical
  obtain ⟨S0, hinit, hk0, hS0scr, hS0out⟩ :
      ∃ S0 : ∀ j, List (TGam Γo j),
        Turing.initList (TMt φ) inp
            = ⟨Option.some TLbl.l1, ((Option.none : Option (Bool ⊕ Bool)),
                (Option.none : Option Γo)), S0⟩
        ∧ S0 TStk.Sin = inp ∧ S0 TStk.Sscr = [] ∧ S0 TStk.Sout = [] := by
    refine ⟨(Turing.initList (TMt φ) inp).stk, rfl, ?_, ?_, ?_⟩
    · exact (ShiTM.initList_haltList_laws (TMt φ) inp []).2.2.1
    · exact (ShiTM.initList_haltList_laws (TMt φ) inp []).2.2.2.1 TStk.Sscr
        (by decide : TStk.Sscr ≠ TStk.Sin)
    · exact (ShiTM.initList_haltList_laws (TMt φ) inp []).2.2.2.1 TStk.Sout
        (by decide : TStk.Sout ≠ TStk.Sin)
  have hph1 := loop1 φ inp S0 (Option.none, Option.none) hk0
  obtain ⟨A, hA1, hAin, hAscr, hAout⟩ :
      ∃ A : ∀ j, List (TGam Γo j),
        (fun cf : Option (Cfg (TGam Γo) TLbl (TSg Γo)) => cf.bind (TM2.step (tprog φ)))^[
            inp.length + 1] (Option.some ⟨Option.some TLbl.l1,
              ((Option.none : Option (Bool ⊕ Bool)), (Option.none : Option Γo)), S0⟩)
          = Option.some ⟨Option.some TLbl.l2, (Option.none, Option.none), A⟩
        ∧ A TStk.Sin = [] ∧ A TStk.Sscr = (inp.flatMap φ).reverse ∧ A TStk.Sout = [] := by
    refine ⟨_, hph1, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by decide : TStk.Sin ≠ TStk.Sscr), Function.update_self]
    · rw [Function.update_self, hS0scr, List.append_nil]
    · rw [Function.update_of_ne (by decide : TStk.Sout ≠ TStk.Sscr),
        Function.update_of_ne (by decide : TStk.Sout ≠ TStk.Sin), hS0out]
  have hph2 := loop2 φ ((inp.flatMap φ).reverse) A (Option.none, Option.none) hAscr
  obtain ⟨T, hT2, hTin, hTscr, hTout⟩ :
      ∃ T : ∀ j, List (TGam Γo j),
        (fun cf : Option (Cfg (TGam Γo) TLbl (TSg Γo)) => cf.bind (TM2.step (tprog φ)))^[
            (inp.flatMap φ).reverse.length + 1]
            (Option.some ⟨Option.some TLbl.l2,
              ((Option.none : Option (Bool ⊕ Bool)), (Option.none : Option Γo)), A⟩)
          = Option.some ⟨Option.some TLbl.lh, (Option.none, Option.none), T⟩
        ∧ T TStk.Sin = [] ∧ T TStk.Sscr = [] ∧ T TStk.Sout = inp.flatMap φ := by
    refine ⟨_, hph2, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by decide : TStk.Sin ≠ TStk.Sout),
        Function.update_of_ne (by decide : TStk.Sin ≠ TStk.Sscr), hAin]
    · rw [Function.update_of_ne (by decide : TStk.Sscr ≠ TStk.Sout), Function.update_self]
    · rw [Function.update_self, hAout, List.append_nil, List.reverse_reverse]
  have hN : (fun cf : Option (Cfg (TGam Γo) TLbl (TSg Γo)) => cf.bind (TM2.step (tprog φ)))^[
        inp.length + 1] (Option.some (Turing.initList (TMt φ) inp))
      = Option.some (⟨Option.some TLbl.l2, (Option.none, Option.none), A⟩ :
          Cfg (TGam Γo) TLbl (TSg Γo)) := by
    rw [hinit]
    exact hA1
  have hbase := (ShiTM.outputsInTime_of_run_to_halt (TMt φ) inp (inp.flatMap φ)).2
    TLbl.lh ⟨Option.some TLbl.l2, (Option.none, Option.none), A⟩ T (inp.length + 1)
    ((inp.flatMap φ).reverse.length + 1) rfl hN hT2 hTout
    (by
      intro k hk
      cases k with
      | Sin => exact hTin
      | Sscr => exact hTscr
      | Sout => exact absurd rfl hk)
  have hlen : (inp.flatMap φ).reverse.length + 1 + (inp.length + 1) + 1
      ≤ inp.length + (inp.flatMap φ).length + 3 := by
    have h1 : (inp.flatMap φ).reverse.length = (inp.flatMap φ).length := by simp
    omega
  obtain ⟨e⟩ := hbase
  exact ⟨⟨e.toEvalsTo, le_trans e.steps_le_m hlen⟩⟩

private lemma mapRefl {α : Type} : ∀ l : List α, List.map (Equiv.refl α).invFun l = l := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, ih]; rfl

/-! ### 6.  The untagger family -/

private lemma fmAppend {α β : Type} (f : α → List β) : ∀ l₁ l₂ : List α,
    (l₁ ++ l₂).flatMap f = l₁.flatMap f ++ l₂.flatMap f := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; rw [List.nil_append, fmNil, List.nil_append]
  | cons a t ih => intro l₂; rw [List.cons_append, fmCons, fmCons, ih, List.append_assoc]

private def phiL : Bool ⊕ Bool → List Bool := Sum.elim (fun b => [b]) (fun _ => [])

private def phiR : Bool ⊕ Bool → List Bool := Sum.elim (fun _ => []) (fun b => [b])

private lemma phiL_len : ∀ c : Bool ⊕ Bool, (phiL c).length ≤ 1 := by
  intro c
  rcases c with b | b <;> simp [phiL]

private lemma phiR_len : ∀ c : Bool ⊕ Bool, (phiR c).length ≤ 1 := by
  intro c
  rcases c with b | b <;> simp [phiR]

private lemma untagL (p : PvsNP.Str × PvsNP.Str) :
    (PvsNP.encodePair p).flatMap phiL = p.1 := by
  have he : PvsNP.encodePair p = p.1.map Sum.inl ++ p.2.map Sum.inr := rfl
  have h1 : ∀ l : PvsNP.Str, (l.map Sum.inl).flatMap phiL = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => rw [List.map_cons, fmCons, ih]; rfl
  have h2 : ∀ l : PvsNP.Str, (l.map Sum.inr).flatMap phiL = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => rw [List.map_cons, fmCons, ih]; rfl
  rw [he, fmAppend, h1, h2, List.append_nil]

private lemma untagR (p : PvsNP.Str × PvsNP.Str) :
    (PvsNP.encodePair p).flatMap phiR = p.2 := by
  have he : PvsNP.encodePair p = p.1.map Sum.inl ++ p.2.map Sum.inr := rfl
  have h1 : ∀ l : PvsNP.Str, (l.map Sum.inl).flatMap phiR = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => rw [List.map_cons, fmCons, ih]; rfl
  have h2 : ∀ l : PvsNP.Str, (l.map Sum.inr).flatMap phiR = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => rw [List.map_cons, fmCons, ih]; rfl
  rw [he, fmAppend, h1, h2, List.nil_append]

private lemma toListLen {Γo : Type} (ψ : Bool ⊕ Bool → Option Γo) :
    ∀ c : Bool ⊕ Bool, ((ψ c).toList).length ≤ 1 := by
  intro c
  cases h : ψ c with
  | none => simp
  | some b => simp

/-! ### 7.  The polynomial-time certificate -/

private lemma transCert {Γo : Type} [Inhabited Γo] [Fintype Γo]
    (φ : Bool ⊕ Bool → List Γo) (M : ℕ) (hM : ∀ c, (φ c).length ≤ M)
    (β : Type) (eb : β → List Γo) (f : PvsNP.Str × PvsNP.Str → β)
    (hf : ∀ p, eb (f p) = (PvsNP.encodePair p).flatMap φ) :
    ∃ c : Turing.TM2ComputableInPolyTime PvsNP.encodePair eb f,
      c.time = Polynomial.C (M + 1) * Polynomial.X + Polynomial.C 3 := by
  refine ⟨{ tm := TMt φ
            inputAlphabet := Equiv.refl (Bool ⊕ Bool)
            outputAlphabet := Equiv.refl Γo
            time := Polynomial.C (M + 1) * Polynomial.X + Polynomial.C 3
            outputsFun := ?_ }, rfl⟩
  intro p
  have hbound : (PvsNP.encodePair p).length + ((PvsNP.encodePair p).flatMap φ).length + 3
      ≤ (Polynomial.C (M + 1) * Polynomial.X + Polynomial.C 3).eval
          (PvsNP.encodePair p).length := by
    have h1 := flatMapLen φ M hM (PvsNP.encodePair p)
    have hev : (Polynomial.C (M + 1) * Polynomial.X + Polynomial.C 3).eval
        (PvsNP.encodePair p).length = (M + 1) * (PvsNP.encodePair p).length + 3 := by simp
    have h2 : (M + 1) * (PvsNP.encodePair p).length
        = M * (PvsNP.encodePair p).length + (PvsNP.encodePair p).length := by ring
    rw [hev]
    omega
  have key : Turing.TM2OutputsInTime (TMt φ)
      (List.map (Equiv.refl (Bool ⊕ Bool)).invFun (PvsNP.encodePair p))
      (Option.some (List.map (Equiv.refl Γo).invFun (eb (f p))))
      ((Polynomial.C (M + 1) * Polynomial.X + Polynomial.C 3).eval
        (PvsNP.encodePair p).length) := by
    rw [mapRefl, mapRefl, hf p]
    have e := (transRun φ (PvsNP.encodePair p)).some
    exact ⟨e.toEvalsTo, le_trans e.steps_le_m hbound⟩
  exact key

private lemma untagNonempty (ψ : Bool ⊕ Bool → Option Bool) :
    Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair (id : PvsNP.Str → PvsNP.Str)
      (fun p : PvsNP.Str × PvsNP.Str => (PvsNP.encodePair p).filterMap ψ)) := by
  obtain ⟨c, -⟩ := transCert (fun c => (ψ c).toList) 1 (toListLen ψ) PvsNP.Str
    (id : PvsNP.Str → PvsNP.Str)
    (fun p : PvsNP.Str × PvsNP.Str => (PvsNP.encodePair p).filterMap ψ)
    (by
      intro p
      rw [flatMapToList]
      rfl)
  exact ⟨c⟩

/-! ### 9.  Statement -/

theorem _root_.BQPReferenceValidation.candidate3 :
    -- (1) THE GENERAL SYMBOLWISE TRANSDUCER, with a polynomial-time certificate, over an
    -- ARBITRARY finite output alphabet and an ARBITRARY target encoding: whenever `eb ∘ f`
    -- is `s ↦ (encodePair s).flatMap φ`, the function `f` is polynomial-time computable out
    -- of the tagged alphabet, with the time polynomial exhibited.
    (∀ (Γo : Type) [Inhabited Γo] [Fintype Γo] (φ : Bool ⊕ Bool → List Γo) (M : ℕ),
        (∀ c, (φ c).length ≤ M) →
        ∀ (β : Type) (eb : β → List Γo) (f : PvsNP.Str × PvsNP.Str → β),
          (∀ p, eb (f p) = (PvsNP.encodePair p).flatMap φ) →
          ∃ c : Turing.TM2ComputableInPolyTime PvsNP.encodePair eb f,
            c.time = Polynomial.C (M + 1) * Polynomial.X + Polynomial.C 3)
  ∧ -- (2) THE UNTAGGER FAMILY: every symbolwise drop-or-keep rule on the tagged alphabet is
    -- a polynomial-time transducer INTO the plain alphabet.  This is exactly the hypothesis
    -- `Nonempty (TM2ComputableInPolyTime encodePair id u)` of the alphabet bridge.
    (∀ ψ : Bool ⊕ Bool → Option Bool,
        Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair
          (id : PvsNP.Str → PvsNP.Str)
          (fun p : PvsNP.Str × PvsNP.Str => (PvsNP.encodePair p).filterMap ψ)))
  ∧ -- (3) the two projections, in the shape the bridge consumes
    (Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair (id : PvsNP.Str → PvsNP.Str)
        (fun p : PvsNP.Str × PvsNP.Str => p.1))
      ∧ Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair
          (id : PvsNP.Str → PvsNP.Str) (fun p : PvsNP.Str × PvsNP.Str => p.2)))
  ∧ -- (4) THE OUTPUT-LENGTH BOUND, which discharges the intermediate-length hypothesis `q`
    -- of the composition lemma at `q = X`.
    (∀ (ψ : Bool ⊕ Bool → Option Bool) (p : PvsNP.Str × PvsNP.Str),
        ((PvsNP.encodePair p).filterMap ψ).length ≤ (PvsNP.encodePair p).length)
  ∧ -- (5) NON-VACUITY at a length-TWO rule: the injective tagged-to-plain pairing
    -- `inl b ↦ 0b`, `inr b ↦ 1b`, which is not a filter-map, together with its value at a
    -- concrete pair.
    (Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair (id : PvsNP.Str → PvsNP.Str)
        (fun p : PvsNP.Str × PvsNP.Str =>
          (PvsNP.encodePair p).flatMap (Sum.elim (fun b => [false, b]) (fun b => [true, b]))))
      ∧ (PvsNP.encodePair ([true], [false])).flatMap
          (Sum.elim (fun b => [false, b]) (fun b => [true, b]))
          = [false, true, true, false]) := by
  have hproj1 : Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair
      (id : PvsNP.Str → PvsNP.Str) (fun p : PvsNP.Str × PvsNP.Str => p.1)) := by
    obtain ⟨c, -⟩ := transCert phiL 1 phiL_len PvsNP.Str (id : PvsNP.Str → PvsNP.Str)
      (fun p : PvsNP.Str × PvsNP.Str => p.1) (fun p => (untagL p).symm)
    exact ⟨c⟩
  have hproj2 : Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair
      (id : PvsNP.Str → PvsNP.Str) (fun p : PvsNP.Str × PvsNP.Str => p.2)) := by
    obtain ⟨c, -⟩ := transCert phiR 1 phiR_len PvsNP.Str (id : PvsNP.Str → PvsNP.Str)
      (fun p : PvsNP.Str × PvsNP.Str => p.2) (fun p => (untagR p).symm)
    exact ⟨c⟩
  refine ⟨?_, untagNonempty, ⟨hproj1, hproj2⟩, ?_, ?_, ?_⟩
  · intro Γo _ _ φ M hM β eb f hf
    exact transCert φ M hM β eb f hf
  · intro ψ p
    have h := flatMapLen (fun c => (ψ c).toList) 1 (toListLen ψ) (PvsNP.encodePair p)
    rw [flatMapToList] at h
    omega
  · obtain ⟨c, -⟩ := transCert (Sum.elim (fun b => [false, b]) (fun b => [true, b])) 2
      (by intro c; rcases c with b | b <;> simp) PvsNP.Str (id : PvsNP.Str → PvsNP.Str)
      (fun p : PvsNP.Str × PvsNP.Str =>
        (PvsNP.encodePair p).flatMap (Sum.elim (fun b => [false, b]) (fun b => [true, b])))
      (fun p => rfl)
    exact ⟨c⟩
  · rfl

end BQPReferenceValidation.Source3

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate3
    let target ← getConstInfo ``PvsNP.tagged_transducers_untaggers_and_projections
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: PvsNP.tagged_transducers_untaggers_and_projections"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: PvsNP.tagged_transducers_untaggers_and_projections"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: PvsNP.tagged_transducers_untaggers_and_projections"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate3
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED PvsNP.tagged_transducers_untaggers_and_projections; axioms {axioms}"
