import Definitions.Def_ShiClassPP
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_ShiBQP_single_run_checker_is_polynomial_time_and_counts_branches_by_phase
import Theorems.Thm_ShiTM_initList_haltList_laws

namespace BQPReferenceValidation.Source19
/-
CHECK-1f.  The SINGLE-RUN repair of CHECK-1e's counting conjunct.

CHECK-1e's checking relation compares the phases of TWO INDEPENDENT folds of the same
program from the same all-zero tape and DISCARDS both final tapes, so it counts ordered
branch pairs with NO endpoint constraint.  `acceptProb` only ever sums pairs of paths that
land on the SAME basis string, so that count is an upper bound, generally strict, and no
restatement that keeps the pair structure can repair it: two independent folds can never
compare endpoints.

This file replaces the pair relation by a SINGLE-RUN one,

  R dg (enc Q, w) = decide (ev Q w = some dg.val),

counted at `hc Q` rather than `hc Q + hc Q`.  The endpoint constraint is then discharged
INSIDE the program: the intended consumer compiles `U`, the output-wire test, `U†` and a
test that the tape has returned to `x‖0` as ONE program `Q`, so that a single `ev` over `Q`
on the concatenated witness already computes `⟨x|U†ΠU|x⟩`.  Adjoints are inside the opcode
set (`T† = +7` is seven 3s, `S† = +6` is three 4s, `H` and `X` are self-inverse) and a
"wire = 0" test is opcode 5, opcode 8, opcode 5.

The circuit is presented to the checker as a head-relative op stream: each op is four bits,

  0  move the head one wire left            1  move the head one wire right
  2  Hadamard at the head (branches)        3  T at the head (phase 1)
  4  S at the head (phase 2)                5  X at the head
  6  read the head bit into the control     7  xor the control into the head bit  (CNOT)
  8  accept-test: kill this branch unless the head bit is 1
  9..15  unknown gate: kill the run

The machine, the opcode table, the encoding and the polynomial `24n + 48` are those of
CHECK-1e; only the second pass is removed, which can only lower the step count, so the same
time polynomial still bounds it.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Turing Turing.TM2

/-! ### 1.  Stacks, labels, register -/

private inductive Stk : Type
  | kin | kout | kprog | kprogB | kwitR | kwit | ktl | ktr
  deriving DecidableEq

private instance : Fintype Stk where
  elems := ⟨[Stk.kin, Stk.kout, Stk.kprog, Stk.kprogB, Stk.kwitR, Stk.kwit, Stk.ktl, Stk.ktr],
    by decide⟩
  complete := fun x => by cases x <;> decide

@[reducible] private def Gam : Stk → Type
  | Stk.kin => Bool ⊕ Bool
  | _ => Bool

private inductive Lbl : Type
  | la | lrw | ld1 | lmd1 | lmd2 | lmid | lrs | lfin | ldw | ldl | ldr | ldb | lrst | lhlt
  deriving DecidableEq

private instance : Fintype Lbl where
  elems := ⟨[Lbl.la, Lbl.lrw, Lbl.ld1, Lbl.lmd1, Lbl.lmd2, Lbl.lmid, Lbl.lrs, Lbl.lfin,
    Lbl.ldw, Lbl.ldl, Lbl.ldr, Lbl.ldb, Lbl.lrst, Lbl.lhlt], by decide⟩
  complete := fun x => by cases x <;> decide

private structure Reg : Type where
  p : ZMod 8
  ct : Bool
  de : Bool
  bd : Bool
  p1 : ZMod 8
  d1 : Bool
  ph2 : Bool
  fin : Bool
  ib : Bool
  ip : Bool
  z0 : Bool
  z1 : Bool
  z2 : Bool
  z3 : Bool
  zc : Bool
  zw : Bool
  deriving DecidableEq

private abbrev RegProd : Type :=
  ZMod 8 × Bool × Bool × Bool × ZMod 8 × Bool × Bool × Bool × Bool × Bool × Bool × Bool ×
    Bool × Bool × Bool × Bool

private def regEquiv : Reg ≃ RegProd where
  toFun v :=
    (v.p, v.ct, v.de, v.bd, v.p1, v.d1, v.ph2, v.fin, v.ib, v.ip, v.z0, v.z1, v.z2, v.z3,
      v.zc, v.zw)
  invFun q :=
    { p := q.1, ct := q.2.1, de := q.2.2.1, bd := q.2.2.2.1, p1 := q.2.2.2.2.1,
      d1 := q.2.2.2.2.2.1, ph2 := q.2.2.2.2.2.2.1, fin := q.2.2.2.2.2.2.2.1,
      ib := q.2.2.2.2.2.2.2.2.1, ip := q.2.2.2.2.2.2.2.2.2.1,
      z0 := q.2.2.2.2.2.2.2.2.2.2.1, z1 := q.2.2.2.2.2.2.2.2.2.2.2.1,
      z2 := q.2.2.2.2.2.2.2.2.2.2.2.2.1, z3 := q.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      zc := q.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, zw := q.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }
  left_inv v := by cases v; rfl
  right_inv q := by rfl

private instance : Fintype Reg := Fintype.ofEquiv RegProd regEquiv.symm

private def R0 : Reg :=
  { p := 0, ct := false, de := false, bd := false, p1 := 0, d1 := false, ph2 := false,
    fin := false, ib := false, ip := false, z0 := false, z1 := false, z2 := false,
    z3 := false, zc := false, zw := false }

/-! ### 2.  The one-branch gate walk -/

private abbrev St : Type := ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool

private def sA : St → ℕ → St
  | (ph, tl, tr, c, de, bd, w), 0 => (ph, tl.tail, tl.headI :: tr, c, de, bd, w)
  | (ph, tl, tr, c, de, bd, w), 1 => (ph, tr.headI :: tl, tr.tail, c, de, bd, w)
  | (ph, tl, tr, c, de, bd, w), 2 =>
      (ph + (if tr.headI && w.headI then 4 else 0), tl, w.headI :: tr.tail, c, de,
        bd || w.isEmpty, w.tail)
  | (ph, tl, tr, c, de, bd, w), 3 =>
      (ph + (if tr.headI then 1 else 0), tl, tr.headI :: tr.tail, c, de, bd, w)
  | (ph, tl, tr, c, de, bd, w), 4 =>
      (ph + (if tr.headI then 2 else 0), tl, tr.headI :: tr.tail, c, de, bd, w)
  | (ph, tl, tr, c, de, bd, w), 5 => (ph, tl, (!tr.headI) :: tr.tail, c, de, bd, w)
  | (ph, tl, tr, c, de, bd, w), 6 => (ph, tl, tr.headI :: tr.tail, tr.headI, de, bd, w)
  | (ph, tl, tr, c, de, bd, w), 7 => (ph, tl, (xor tr.headI c) :: tr.tail, c, de, bd, w)
  | (ph, tl, tr, c, de, bd, w), 8 => (ph, tl, tr.headI :: tr.tail, c, de || !tr.headI, bd, w)
  | (ph, tl, tr, c, de, bd, w), _ => (ph, tl, tr.headI :: tr.tail, c, de, true, w)

private def sT (s : St) (c : ℕ) : St := sA s (c % 16)

private def cval (b0 b1 b2 b3 : Bool) : ℕ :=
  (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) + (if b3 then 8 else 0)

private def rb : List Bool → St → St
  | b0 :: b1 :: b2 :: b3 :: r, s => rb r (sT s (cval b0 b1 b2 b3))
  | [], s => s
  | [b0], s => sT s (cval b0 false false false)
  | [b0, b1], s => sT s (cval b0 b1 false false)
  | [b0, b1, b2], s => sT s (cval b0 b1 b2 false)

private def pd : List Bool → List Bool
  | b0 :: b1 :: b2 :: b3 :: r => b0 :: b1 :: b2 :: b3 :: pd r
  | [] => []
  | [b0] => [b0, false, false, false]
  | [b0, b1] => [b0, b1, false, false]
  | [b0, b1, b2] => [b0, b1, b2, false]

private def gc : List Bool → ℕ
  | _ :: _ :: _ :: _ :: r => 1 + gc r
  | [] => 0
  | _ => 1

private def initSt (w : List Bool) : St := (0, [], [], false, false, false, w)

private def Rf (dg : ZMod 8) (q : PvsNP.Str × PvsNP.Str) : Bool :=
  let s := rb q.1.reverse (initSt q.2)
  !s.2.2.2.2.2.1 && !s.2.2.2.2.1 && s.2.2.2.2.2.2.isEmpty && decide (s.1 = dg)

/-! ### 3.  The machine -/

private def fIn : Reg → Option (Bool ⊕ Bool) → Reg
  | v, none => { v with fin := true }
  | v, some (Sum.inl b) => { v with fin := false, ib := b, ip := true }
  | v, some (Sum.inr b) => { v with fin := false, ib := b, ip := false }

private def fDr : Reg → Option Bool → Reg
  | v, none => { v with fin := true }
  | v, some b => { v with fin := false, ib := b }

private def fRd0 : Reg → Option Bool → Reg
  | v, none => { v with fin := true }
  | v, some b => { v with fin := false, z0 := b }

private def fRd1 (v : Reg) (o : Option Bool) : Reg := { v with z1 := o.getD false }
private def fRd2 (v : Reg) (o : Option Bool) : Reg := { v with z2 := o.getD false }
private def fRd3 (v : Reg) (o : Option Bool) : Reg := { v with z3 := o.getD false }

private def cd (v : Reg) : ℕ := cval v.z0 v.z1 v.z2 v.z3

private def fCell (v : Reg) (o : Option Bool) : Reg := { v with zc := o.getD false }

private def gateEff (v : Reg) : Reg :=
  match cd v with
  | 0 => v
  | 1 => v
  | 2 => v
  | 3 => { v with p := v.p + (if v.zc then 1 else 0) }
  | 4 => { v with p := v.p + (if v.zc then 2 else 0) }
  | 5 => v
  | 6 => { v with ct := v.zc }
  | 7 => v
  | 8 => { v with de := v.de || !v.zc }
  | _ => { v with bd := true }

private def fCellG (v : Reg) (o : Option Bool) : Reg := gateEff { v with zc := o.getD false }

private def gateCell (v : Reg) : Bool :=
  match cd v with
  | 5 => !v.zc
  | 7 => xor v.zc v.ct
  | _ => v.zc

private def fWit (v : Reg) (o : Option Bool) : Reg :=
  { v with
    zw := o.getD false, bd := v.bd || o.isNone,
    p := v.p + (if v.zc && o.getD false then 4 else 0) }

private def fPk (v : Reg) (o : Option Bool) : Reg := { v with fin := o.isSome }

private def mid (v : Reg) : Reg :=
  { v with p1 := v.p, d1 := v.de, p := 0, ct := false, de := false, ph2 := true }

private def acc (dg : ZMod 8) (v : Reg) : Bool :=
  !v.bd && !v.de && !v.fin && decide (v.p = dg)

private def prog (dg : ZMod 8) : Lbl → Stmt Gam Lbl Reg
  | Lbl.la =>
      Stmt.pop Stk.kin fIn
        (Stmt.branch (fun v => v.fin)
          (Stmt.goto (fun _ => Lbl.lrw))
          (Stmt.branch (fun v => v.ip)
            (Stmt.push Stk.kprog (fun v => v.ib) (Stmt.goto (fun _ => Lbl.la)))
            (Stmt.push Stk.kwitR (fun v => v.ib) (Stmt.goto (fun _ => Lbl.la)))))
  | Lbl.lrw =>
      Stmt.pop Stk.kwitR fDr
        (Stmt.branch (fun v => v.fin)
          (Stmt.goto (fun _ => Lbl.ld1))
          (Stmt.push Stk.kwit (fun v => v.ib) (Stmt.goto (fun _ => Lbl.lrw))))
  | Lbl.ld1 =>
      Stmt.pop Stk.kprog fRd0
        (Stmt.branch (fun v => v.fin)
          (Stmt.goto (fun _ => Lbl.lfin))
          (Stmt.pop Stk.kprog fRd1
            (Stmt.pop Stk.kprog fRd2
              (Stmt.pop Stk.kprog fRd3
                (Stmt.push Stk.kprogB (fun v => v.z0)
                  (Stmt.push Stk.kprogB (fun v => v.z1)
                    (Stmt.push Stk.kprogB (fun v => v.z2)
                      (Stmt.push Stk.kprogB (fun v => v.z3)
                        (Stmt.branch (fun v => decide (cd v = 0))
                          (Stmt.pop Stk.ktl fCell
                            (Stmt.push Stk.ktr (fun v => v.zc)
                              (Stmt.goto (fun _ => Lbl.ld1))))
                          (Stmt.branch (fun v => decide (cd v = 1))
                            (Stmt.pop Stk.ktr fCell
                              (Stmt.push Stk.ktl (fun v => v.zc)
                                (Stmt.goto (fun _ => Lbl.ld1))))
                            (Stmt.branch (fun v => decide (cd v = 2))
                              (Stmt.pop Stk.ktr fCell
                                (Stmt.pop Stk.kwit fWit
                                  (Stmt.push Stk.ktr (fun v => v.zw)
                                    (Stmt.goto (fun _ => Lbl.ld1)))))
                              (Stmt.pop Stk.ktr fCellG
                                (Stmt.push Stk.ktr gateCell
                                  (Stmt.goto (fun _ => Lbl.ld1)))))))))))))))
  | Lbl.lmd1 =>
      Stmt.pop Stk.ktl fDr
        (Stmt.branch (fun v => v.fin)
          (Stmt.goto (fun _ => Lbl.lmd2)) (Stmt.goto (fun _ => Lbl.lmd1)))
  | Lbl.lmd2 =>
      Stmt.pop Stk.ktr fDr
        (Stmt.branch (fun v => v.fin)
          (Stmt.goto (fun _ => Lbl.lmid)) (Stmt.goto (fun _ => Lbl.lmd2)))
  | Lbl.lmid => Stmt.load mid (Stmt.goto (fun _ => Lbl.lrs))
  | Lbl.lrs =>
      Stmt.pop Stk.kprogB fDr
        (Stmt.branch (fun v => v.fin)
          (Stmt.goto (fun _ => Lbl.ld1))
          (Stmt.push Stk.kprog (fun v => v.ib) (Stmt.goto (fun _ => Lbl.lrs))))
  | Lbl.lfin =>
      Stmt.peek Stk.kwit fPk
        (Stmt.push Stk.kout (fun v => acc dg v) (Stmt.goto (fun _ => Lbl.ldw)))
  | Lbl.ldw =>
      Stmt.pop Stk.kwit fDr
        (Stmt.branch (fun v => v.fin)
          (Stmt.goto (fun _ => Lbl.ldl)) (Stmt.goto (fun _ => Lbl.ldw)))
  | Lbl.ldl =>
      Stmt.pop Stk.ktl fDr
        (Stmt.branch (fun v => v.fin)
          (Stmt.goto (fun _ => Lbl.ldr)) (Stmt.goto (fun _ => Lbl.ldl)))
  | Lbl.ldr =>
      Stmt.pop Stk.ktr fDr
        (Stmt.branch (fun v => v.fin)
          (Stmt.goto (fun _ => Lbl.ldb)) (Stmt.goto (fun _ => Lbl.ldr)))
  | Lbl.ldb =>
      Stmt.pop Stk.kprogB fDr
        (Stmt.branch (fun v => v.fin)
          (Stmt.goto (fun _ => Lbl.lrst)) (Stmt.goto (fun _ => Lbl.ldb)))
  | Lbl.lrst => Stmt.load (fun _ => R0) (Stmt.goto (fun _ => Lbl.lhlt))
  | Lbl.lhlt => Stmt.halt

@[reducible] private def TMc (dg : ZMod 8) : Turing.FinTM2 where
  K := Stk
  k₀ := Stk.kin
  k₁ := Stk.kout
  Γ := Gam
  Λ := Lbl
  main := Lbl.la
  σ := Reg
  initialState := R0
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := prog dg

/-! ### 4.  One-node step lemmas -/

private lemma aux_step (M : Lbl → Stmt Gam Lbl Reg) (l : Lbl) (v : Reg)
    (S : ∀ j, List (Gam j)) :
    TM2.step M ⟨some l, v, S⟩ = some (stepAux (M l) v S) := rfl

private lemma aux_pop {k : Stk} (f : Reg → Option (Gam k) → Reg) (Q : Stmt Gam Lbl Reg)
    (v : Reg) (S : ∀ j, List (Gam j)) :
    stepAux (Stmt.pop k f Q) v S
      = stepAux Q (f v (S k).head?) (Function.update S k (S k).tail) := rfl

private lemma aux_peek {k : Stk} (f : Reg → Option (Gam k) → Reg) (Q : Stmt Gam Lbl Reg)
    (v : Reg) (S : ∀ j, List (Gam j)) :
    stepAux (Stmt.peek k f Q) v S = stepAux Q (f v (S k).head?) S := rfl

private lemma aux_push {k : Stk} (g : Reg → Gam k) (Q : Stmt Gam Lbl Reg)
    (v : Reg) (S : ∀ j, List (Gam j)) :
    stepAux (Stmt.push k g Q) v S = stepAux Q v (Function.update S k (g v :: S k)) := rfl

private lemma aux_load (a : Reg → Reg) (Q : Stmt Gam Lbl Reg) (v : Reg)
    (S : ∀ j, List (Gam j)) : stepAux (Stmt.load a Q) v S = stepAux Q (a v) S := rfl

private lemma aux_branch (f : Reg → Bool) (Q1 Q2 : Stmt Gam Lbl Reg) (v : Reg)
    (S : ∀ j, List (Gam j)) :
    stepAux (Stmt.branch f Q1 Q2) v S = cond (f v) (stepAux Q1 v S) (stepAux Q2 v S) := rfl

private lemma aux_goto (lf : Reg → Lbl) (v : Reg) (S : ∀ j, List (Gam j)) :
    stepAux (Stmt.goto lf) v S = ⟨some (lf v), v, S⟩ := rfl

private lemma hdI (l : List Bool) : (l.head?).getD false = l.headI := by cases l <;> rfl

private lemma hdN (l : List Bool) : (l.head?).isNone = l.isEmpty := by cases l <;> rfl

private lemma hdS (l : List Bool) : (l.head?).isSome = !l.isEmpty := by cases l <;> rfl

private lemma one_step (dg : ZMod 8) (c c' : Cfg Gam Lbl Reg)
    (h : TM2.step (prog dg) c = some c') :
    (fun cf : Option (Cfg Gam Lbl Reg) => cf.bind (TM2.step (prog dg)))^[1] (some c)
      = some c' := by
  simpa using h

/-! ### 5.  Two generic loops -/

private def Same (v w : Reg) : Prop :=
  w.p = v.p ∧ w.ct = v.ct ∧ w.de = v.de ∧ w.bd = v.bd ∧ w.p1 = v.p1 ∧ w.d1 = v.d1 ∧
    w.ph2 = v.ph2

private lemma Same_upd (v : Reg) (f i : Bool) : Same v { v with fin := f, ib := i } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma Same_trans {u v w : Reg} (h1 : Same u v) (h2 : Same v w) : Same u w := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h2
  exact ⟨by rw [b1, a1], by rw [b2, a2], by rw [b3, a3], by rw [b4, a4], by rw [b5, a5],
    by rw [b6, a6], by rw [b7, a7]⟩

private lemma drainLoop (dg : ZMod 8) (k : Stk) (l l' : Lbl)
    (f : Reg → Option (Gam k) → Reg)
    (hf0 : ∀ v, f v none = { v with fin := true })
    (hf1 : ∀ v y, ∃ b : Bool, f v (some y) = { v with fin := false, ib := b })
    (hM : prog dg l = Stmt.pop k f
            (Stmt.branch (fun v => v.fin)
              (Stmt.goto (fun _ => l')) (Stmt.goto (fun _ => l)))) :
    ∀ (u : List (Gam k)) (v : Reg) (S : ∀ j, List (Gam j)), S k = u →
      ∃ (w : Reg) (T : ∀ j, List (Gam j)),
        Same v w ∧ T k = [] ∧ (∀ j, j ≠ k → T j = S j) ∧
        (fun cf : Option (Cfg Gam Lbl Reg) => cf.bind (TM2.step (prog dg)))^[u.length + 1]
            (some ⟨some l, v, S⟩) = some ⟨some l', w, T⟩ := by
  intro u
  induction u with
  | nil =>
      intro v S hS
      refine ⟨{ v with fin := true }, Function.update S k [],
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, Function.update_self k [] S,
        fun j hj => Function.update_of_ne hj [] S, ?_⟩
      refine one_step dg _ _ ?_
      rw [aux_step, hM, aux_pop, hS]
      simp only [List.head?_nil, List.tail_nil, hf0, aux_branch, aux_goto]
      rfl
  | cons y u ih =>
      intro v S hS
      obtain ⟨b, hb⟩ := hf1 v y
      have hstep : TM2.step (prog dg) ⟨some l, v, S⟩
          = some ⟨some l, { v with fin := false, ib := b }, Function.update S k u⟩ := by
        rw [aux_step, hM, aux_pop, hS]
        simp only [List.head?_cons, List.tail_cons, hb, aux_branch, aux_goto]
        rfl
      obtain ⟨w, T, hsame, hTk, hTo, hit⟩ :=
        ih { v with fin := false, ib := b } (Function.update S k u)
          (Function.update_self k u S)
      refine ⟨w, T, Same_trans (Same_upd v false b) hsame, hTk, ?_, ?_⟩
      · intro j hj
        rw [hTo j hj]
        exact Function.update_of_ne hj u S
      · have hlen : (y :: u).length + 1 = (u.length + 1) + 1 := by simp
        rw [hlen, Function.iterate_succ_apply]
        show ((fun cf : Option (Cfg Gam Lbl Reg) => cf.bind (TM2.step (prog dg)))^[u.length + 1])
            (TM2.step (prog dg) ⟨some l, v, S⟩) = _
        rw [hstep]
        exact hit

private lemma xferLoop (dg : ZMod 8) (k k' : Stk) (l l' : Lbl) (hne : k' ≠ k)
    (f : Reg → Option (Gam k) → Reg) (g : Reg → Gam k') (emb : Gam k → Gam k')
    (hf0 : ∀ v, f v none = { v with fin := true })
    (hf1 : ∀ v y, ∃ b : Bool, f v (some y) = { v with fin := false, ib := b })
    (hg : ∀ v y, g (f v (some y)) = emb y)
    (hfin : ∀ v y, (f v (some y)).fin = false)
    (hM : prog dg l = Stmt.pop k f
            (Stmt.branch (fun v => v.fin)
              (Stmt.goto (fun _ => l'))
              (Stmt.push k' g (Stmt.goto (fun _ => l))))) :
    ∀ (u : List (Gam k)) (v : Reg) (S : ∀ j, List (Gam j)), S k = u →
      ∃ (w : Reg) (T : ∀ j, List (Gam j)),
        Same v w ∧ T k = [] ∧ T k' = (u.map emb).reverse ++ S k' ∧
        (∀ j, j ≠ k → j ≠ k' → T j = S j) ∧
        (fun cf : Option (Cfg Gam Lbl Reg) => cf.bind (TM2.step (prog dg)))^[u.length + 1]
            (some ⟨some l, v, S⟩) = some ⟨some l', w, T⟩ := by
  intro u
  induction u with
  | nil =>
      intro v S hS
      refine ⟨{ v with fin := true }, Function.update S k [],
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, Function.update_self k [] S, ?_,
        fun j hj _ => Function.update_of_ne hj [] S, ?_⟩
      · simp only [List.map_nil, List.reverse_nil, List.nil_append]
        exact Function.update_of_ne hne [] S
      · refine one_step dg _ _ ?_
        rw [aux_step, hM, aux_pop, hS]
        simp only [List.head?_nil, List.tail_nil, hf0, aux_branch, aux_goto]
        rfl
  | cons y u ih =>
      intro v S hS
      obtain ⟨b, hb⟩ := hf1 v y
      have hstep : TM2.step (prog dg) ⟨some l, v, S⟩
          = some ⟨some l, f v (some y),
              Function.update (Function.update S k u) k' (emb y :: S k')⟩ := by
        rw [aux_step, hM, aux_pop, hS]
        simp only [List.head?_cons, List.tail_cons, aux_branch, hfin, cond_false, aux_push,
          aux_goto]
        have h1 : (Function.update S k u) k' = S k' := Function.update_of_ne hne u S
        rw [h1, hg]
      have hS1k : (Function.update (Function.update S k u) k' (emb y :: S k')) k = u := by
        rw [Function.update_of_ne (Ne.symm hne) _ _, Function.update_self]
      obtain ⟨w, T, hsame, hTk, hTk', hTo, hit⟩ :=
        ih (f v (some y)) (Function.update (Function.update S k u) k' (emb y :: S k')) hS1k
      refine ⟨w, T, ?_, hTk, ?_, ?_, ?_⟩
      · refine Same_trans ?_ hsame
        rw [hb]; exact Same_upd v false b
      · rw [hTk', Function.update_self]
        simp [List.reverse_cons]
      · intro j hj hj'
        rw [hTo j hj hj', Function.update_of_ne hj' _ _, Function.update_of_ne hj _ _]
      · have hlen : (y :: u).length + 1 = (u.length + 1) + 1 := by simp
        rw [hlen, Function.iterate_succ_apply]
        show ((fun cf : Option (Cfg Gam Lbl Reg) => cf.bind (TM2.step (prog dg)))^[u.length + 1])
            (TM2.step (prog dg) ⟨some l, v, S⟩) = _
        rw [hstep]
        exact hit

/-! ### 6.  The input-splitting loop -/

private def inls : List (Bool ⊕ Bool) → List Bool
  | [] => []
  | Sum.inl b :: t => b :: inls t
  | Sum.inr _ :: t => inls t

private def inrs : List (Bool ⊕ Bool) → List Bool
  | [] => []
  | Sum.inl _ :: t => inrs t
  | Sum.inr b :: t => b :: inrs t

private lemma inls_enc (x y : PvsNP.Str) : inls (x.map Sum.inl ++ y.map Sum.inr) = x := by
  induction x with
  | nil =>
      simp only [List.map_nil, List.nil_append]
      induction y with
      | nil => rfl
      | cons b t ih => simpa [inls] using ih
  | cons b t ih => simpa [inls] using ih

private lemma inrs_enc (x y : PvsNP.Str) : inrs (x.map Sum.inl ++ y.map Sum.inr) = y := by
  induction x with
  | nil =>
      simp only [List.map_nil, List.nil_append]
      induction y with
      | nil => rfl
      | cons b t ih => simpa [inrs] using ih
  | cons b t ih => simpa [inrs] using ih

private lemma laLoop (dg : ZMod 8) :
    ∀ (u : List (Gam Stk.kin)) (v : Reg) (S : ∀ j, List (Gam j)), S Stk.kin = u →
      ∃ (w : Reg) (T : ∀ j, List (Gam j)),
        Same v w ∧ T Stk.kin = [] ∧
        (T Stk.kprog : List Bool) = (inls u).reverse ++ (S Stk.kprog : List Bool) ∧
        (T Stk.kwitR : List Bool) = (inrs u).reverse ++ (S Stk.kwitR : List Bool) ∧
        (∀ j, j ≠ Stk.kin → j ≠ Stk.kprog → j ≠ Stk.kwitR → T j = S j) ∧
        (fun cf : Option (Cfg Gam Lbl Reg) => cf.bind (TM2.step (prog dg)))^[u.length + 1]
            (some ⟨some Lbl.la, v, S⟩) = some ⟨some Lbl.lrw, w, T⟩ := by
  intro u
  induction u with
  | nil =>
      intro v S hS
      refine ⟨{ v with fin := true }, Function.update S Stk.kin [],
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, Function.update_self _ _ _, ?_, ?_,
        fun j hj _ _ => Function.update_of_ne hj _ _, ?_⟩
      · simp only [inls, List.reverse_nil, List.nil_append]
        exact Function.update_of_ne (by decide) _ _
      · simp only [inrs, List.reverse_nil, List.nil_append]
        exact Function.update_of_ne (by decide) _ _
      · refine one_step dg _ _ ?_
        rw [aux_step]
        simp only [prog]
        rw [aux_pop, hS]
        simp only [List.head?_nil, List.tail_nil, fIn, aux_branch, aux_goto]
        rfl
  | cons yy u ih =>
      intro v S hS
      match yy with
      | Sum.inl b =>
          have hstep : TM2.step (prog dg) ⟨some Lbl.la, v, S⟩
              = some ⟨some Lbl.la, { v with fin := false, ib := b, ip := true },
                  Function.update (Function.update S Stk.kin u) Stk.kprog
                    (b :: (S Stk.kprog : List Bool))⟩ := by
            rw [aux_step]
            simp only [prog]
            rw [aux_pop, hS]
            simp only [List.head?_cons, List.tail_cons, fIn, aux_branch, aux_push, aux_goto]
            have h1 : (Function.update S Stk.kin u) Stk.kprog = (S Stk.kprog : List Bool) :=
              Function.update_of_ne (by decide) _ _
            rw [h1]
            rfl
          have hS1k : (Function.update (Function.update S Stk.kin u) Stk.kprog
              (b :: (S Stk.kprog : List Bool))) Stk.kin = u := by
            rw [Function.update_of_ne (by decide) _ _, Function.update_self]
          obtain ⟨w, T, hsame, hTi, hTp, hTw, hTo, hit⟩ :=
            ih { v with fin := false, ib := b, ip := true } _ hS1k
          refine ⟨w, T, Same_trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hsame, hTi, ?_, ?_, ?_, ?_⟩
          · rw [hTp, Function.update_self]
            simp [inls, List.reverse_cons]
          · rw [hTw, Function.update_of_ne (by decide) _ _, Function.update_of_ne (by decide) _ _]
            simp [inrs]
          · intro j hj hj' hj''
            rw [hTo j hj hj' hj'', Function.update_of_ne hj' _ _, Function.update_of_ne hj _ _]
          · have hlen : (Sum.inl b :: u).length + 1 = (u.length + 1) + 1 := by simp
            rw [hlen, Function.iterate_succ_apply]
            show ((fun cf : Option (Cfg Gam Lbl Reg) =>
              cf.bind (TM2.step (prog dg)))^[u.length + 1])
                (TM2.step (prog dg) ⟨some Lbl.la, v, S⟩) = _
            rw [hstep]
            exact hit
      | Sum.inr b =>
          have hstep : TM2.step (prog dg) ⟨some Lbl.la, v, S⟩
              = some ⟨some Lbl.la, { v with fin := false, ib := b, ip := false },
                  Function.update (Function.update S Stk.kin u) Stk.kwitR
                    (b :: (S Stk.kwitR : List Bool))⟩ := by
            rw [aux_step]
            simp only [prog]
            rw [aux_pop, hS]
            simp only [List.head?_cons, List.tail_cons, fIn, aux_branch, aux_push, aux_goto]
            have h1 : (Function.update S Stk.kin u) Stk.kwitR = (S Stk.kwitR : List Bool) :=
              Function.update_of_ne (by decide) _ _
            rw [h1]
            rfl
          have hS1k : (Function.update (Function.update S Stk.kin u) Stk.kwitR
              (b :: (S Stk.kwitR : List Bool))) Stk.kin = u := by
            rw [Function.update_of_ne (by decide) _ _, Function.update_self]
          obtain ⟨w, T, hsame, hTi, hTp, hTw, hTo, hit⟩ :=
            ih { v with fin := false, ib := b, ip := false } _ hS1k
          refine ⟨w, T, Same_trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hsame, hTi, ?_, ?_, ?_, ?_⟩
          · rw [hTp, Function.update_of_ne (by decide) _ _, Function.update_of_ne (by decide) _ _]
            simp [inls]
          · rw [hTw, Function.update_self]
            simp [inrs, List.reverse_cons]
          · intro j hj hj' hj''
            rw [hTo j hj hj' hj'', Function.update_of_ne hj'' _ _, Function.update_of_ne hj _ _]
          · have hlen : (Sum.inr b :: u).length + 1 = (u.length + 1) + 1 := by simp
            rw [hlen, Function.iterate_succ_apply]
            show ((fun cf : Option (Cfg Gam Lbl Reg) =>
              cf.bind (TM2.step (prog dg)))^[u.length + 1])
                (TM2.step (prog dg) ⟨some Lbl.la, v, S⟩) = _
            rw [hstep]
            exact hit

/-! ### 7.  The interpreter loop -/

private def Corr (s : St) (v : Reg) (S : ∀ j, List (Gam j)) : Prop :=
  v.p = s.1 ∧ (S Stk.ktl : List Bool) = s.2.1 ∧ (S Stk.ktr : List Bool) = s.2.2.1 ∧
    v.ct = s.2.2.2.1 ∧ v.de = s.2.2.2.2.1 ∧ v.bd = s.2.2.2.2.2.1 ∧
    (S Stk.kwit : List Bool) = s.2.2.2.2.2.2

private lemma cval_lt (b0 b1 b2 b3 : Bool) : cval b0 b1 b2 b3 < 16 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

private lemma sT_cval (s : St) (b0 b1 b2 b3 : Bool) :
    sT s (cval b0 b1 b2 b3) = sA s (cval b0 b1 b2 b3) := by
  rw [sT, Nat.mod_eq_of_lt (cval_lt b0 b1 b2 b3)]

private lemma chunkStep (dg : ZMod 8) (b0 b1 b2 b3 : Bool) (t rest : List Bool) (s : St)
    (v : Reg) (S : ∀ j, List (Gam j))
    (hb1 : t.headI = b1) (hb2 : t.tail.headI = b2) (hb3 : t.tail.tail.headI = b3)
    (hr : t.tail.tail.tail = rest)
    (hC : Corr s v S) (hp : (S Stk.kprog : List Bool) = b0 :: t) :
    ∃ (w : Reg) (T : ∀ j, List (Gam j)),
      w.ph2 = v.ph2 ∧ w.p1 = v.p1 ∧ w.d1 = v.d1 ∧
      Corr (sT s (cval b0 b1 b2 b3)) w T ∧
      (T Stk.kprog : List Bool) = rest ∧
      (T Stk.kprogB : List Bool) = b3 :: b2 :: b1 :: b0 :: (S Stk.kprogB : List Bool) ∧
      (∀ j, j ≠ Stk.kprog → j ≠ Stk.kprogB → j ≠ Stk.ktl → j ≠ Stk.ktr → j ≠ Stk.kwit →
        T j = S j) ∧
      TM2.step (prog dg) ⟨some Lbl.ld1, v, S⟩ = some ⟨some Lbl.ld1, w, T⟩ := by
  obtain ⟨hp0, htl, htr, hct, hde, hbd, hw⟩ := hC
  set v3 : Reg := { v with fin := false, z0 := b0, z1 := b1, z2 := b2, z3 := b3 } with hv3
  set S2 : ∀ j, List (Gam j) :=
    Function.update (Function.update S Stk.kprog rest) Stk.kprogB
      (b3 :: b2 :: b1 :: b0 :: (S Stk.kprogB : List Bool)) with hS2
  have hS2p : (S2 Stk.kprog : List Bool) = rest := by
    rw [hS2, Function.update_of_ne (by decide) _ _, Function.update_self]
  have hS2b : (S2 Stk.kprogB : List Bool)
      = b3 :: b2 :: b1 :: b0 :: (S Stk.kprogB : List Bool) := by
    rw [hS2, Function.update_self]
  have hS2o : ∀ j, j ≠ Stk.kprog → j ≠ Stk.kprogB → S2 j = S j := by
    intro j h1 h2
    rw [hS2, Function.update_of_ne h2 _ _, Function.update_of_ne h1 _ _]
  have hS2tl : (S2 Stk.ktl : List Bool) = s.2.1 := by
    rw [hS2o _ (by decide) (by decide), htl]
  have hS2tr : (S2 Stk.ktr : List Bool) = s.2.2.1 := by
    rw [hS2o _ (by decide) (by decide), htr]
  have hS2w : (S2 Stk.kwit : List Bool) = s.2.2.2.2.2.2 := by
    rw [hS2o _ (by decide) (by decide), hw]
  have hcd : cd v3 = cval b0 b1 b2 b3 := rfl
  have hpre : TM2.step (prog dg) ⟨some Lbl.ld1, v, S⟩
      = some (stepAux
          (Stmt.branch (fun v => decide (cd v = 0))
            (Stmt.pop Stk.ktl fCell
              (Stmt.push Stk.ktr (fun v => v.zc) (Stmt.goto (fun _ => Lbl.ld1))))
            (Stmt.branch (fun v => decide (cd v = 1))
              (Stmt.pop Stk.ktr fCell
                (Stmt.push Stk.ktl (fun v => v.zc) (Stmt.goto (fun _ => Lbl.ld1))))
              (Stmt.branch (fun v => decide (cd v = 2))
                (Stmt.pop Stk.ktr fCell
                  (Stmt.pop Stk.kwit fWit
                    (Stmt.push Stk.ktr (fun v => v.zw) (Stmt.goto (fun _ => Lbl.ld1)))))
                (Stmt.pop Stk.ktr fCellG
                  (Stmt.push Stk.ktr gateCell (Stmt.goto (fun _ => Lbl.ld1)))))))
          v3 S2) := by
    rw [aux_step]
    simp only [prog]
    rw [aux_pop, hp]
    simp only [List.head?_cons, List.tail_cons, fRd0, aux_branch, cond_false, aux_pop,
      aux_push, fRd1, fRd2, fRd3]
    have e2 : ∀ l1 l2 : List Bool,
        Function.update (Function.update S Stk.kprog l1) Stk.kprog l2
          = Function.update S Stk.kprog l2 := by
      intro l1 l2
      funext j
      by_cases hj : j = Stk.kprog
      · subst hj
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_of_ne hj]
    rw [Function.update_self, e2, Function.update_self, e2, Function.update_self, e2]
    rw [hdI, hdI, hdI, hb1, hb2, hb3, hr]
    have e5 : (Function.update S Stk.kprog rest) Stk.kprogB = (S Stk.kprogB : List Bool) :=
      Function.update_of_ne (by decide) _ _
    rw [e5]
    have e6 : ∀ l1 l2 : List Bool,
        Function.update (Function.update (Function.update S Stk.kprog rest) Stk.kprogB l1)
            Stk.kprogB l2
          = Function.update (Function.update S Stk.kprog rest) Stk.kprogB l2 := by
      intro l1 l2
      funext j
      by_cases hj : j = Stk.kprogB
      · subst hj
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_of_ne hj]
    rw [Function.update_self, e6, Function.update_self, e6, Function.update_self, e6]
  by_cases h0 : cval b0 b1 b2 b3 = 0
  · refine ⟨{ v3 with zc := ((S2 Stk.ktl : List Bool).head?).getD false },
      Function.update (Function.update S2 Stk.ktl (S2 Stk.ktl : List Bool).tail) Stk.ktr
        (((S2 Stk.ktl : List Bool).head?).getD false :: (S2 Stk.ktr : List Bool)),
      rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sT_cval, h0]
      obtain ⟨ph, tl, tr, ctv, dev, bdv, ww⟩ := s
      simp only at hp0 htl htr hct hde hbd hw hS2tl hS2tr hS2w ⊢
      refine ⟨hp0, ?_, ?_, hct, hde, hbd, ?_⟩
      · rw [Function.update_of_ne (by decide) _ _, Function.update_self, hS2tl]
        rfl
      · rw [Function.update_self, hdI, hS2tl, hS2tr]
        rfl
      · rw [Function.update_of_ne (by decide) _ _, Function.update_of_ne (by decide) _ _, hS2w]
        rfl
    · rw [Function.update_of_ne (by decide) _ _, Function.update_of_ne (by decide) _ _, hS2p]
    · rw [Function.update_of_ne (by decide) _ _, Function.update_of_ne (by decide) _ _, hS2b]
    · intro j h1 h2 h3 h4 _
      rw [Function.update_of_ne h4 _ _, Function.update_of_ne h3 _ _, hS2o j h1 h2]
    · rw [hpre]
      have e0 : (decide (cd v3 = 0)) = true := by simp [hcd, h0]
      simp only [aux_branch, e0, aux_pop, aux_push, aux_goto, fCell, cond_true]
      rw [Function.update_of_ne (show Stk.ktr ≠ Stk.ktl by decide)]
  · by_cases h1 : cval b0 b1 b2 b3 = 1
    · refine ⟨{ v3 with zc := ((S2 Stk.ktr : List Bool).head?).getD false },
        Function.update (Function.update S2 Stk.ktr (S2 Stk.ktr : List Bool).tail) Stk.ktl
          (((S2 Stk.ktr : List Bool).head?).getD false :: (S2 Stk.ktl : List Bool)),
        rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [sT_cval, h1]
        obtain ⟨ph, tl, tr, ctv, dev, bdv, ww⟩ := s
        simp only at hp0 htl htr hct hde hbd hw hS2tl hS2tr hS2w ⊢
        refine ⟨hp0, ?_, ?_, hct, hde, hbd, ?_⟩
        · rw [Function.update_self, hdI, hS2tl, hS2tr]
          rfl
        · rw [Function.update_of_ne (by decide) _ _, Function.update_self, hS2tr]
          rfl
        · rw [Function.update_of_ne (by decide) _ _, Function.update_of_ne (by decide) _ _, hS2w]
          rfl
      · rw [Function.update_of_ne (by decide) _ _, Function.update_of_ne (by decide) _ _, hS2p]
      · rw [Function.update_of_ne (by decide) _ _, Function.update_of_ne (by decide) _ _, hS2b]
      · intro j hh1 hh2 hh3 hh4 _
        rw [Function.update_of_ne hh3 _ _, Function.update_of_ne hh4 _ _, hS2o j hh1 hh2]
      · rw [hpre]
        have e0 : (decide (cd v3 = 0)) = false := by rw [hcd]; exact decide_eq_false h0
        have e1 : (decide (cd v3 = 1)) = true := by simp [hcd, h1]
        simp only [aux_branch, e0, e1, aux_pop, aux_push, aux_goto, fCell, cond_true,
          cond_false]
        rw [Function.update_of_ne (show Stk.ktl ≠ Stk.ktr by decide)]
    · by_cases h2 : cval b0 b1 b2 b3 = 2
      · refine ⟨fWit { v3 with zc := ((S2 Stk.ktr : List Bool).head?).getD false }
            ((S2 Stk.kwit : List Bool).head?),
          Function.update (Function.update (Function.update S2 Stk.ktr
              (S2 Stk.ktr : List Bool).tail) Stk.kwit (S2 Stk.kwit : List Bool).tail) Stk.ktr
            ((((S2 Stk.kwit : List Bool).head?).getD false) :: (S2 Stk.ktr : List Bool).tail),
          rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · rw [sT_cval, h2]
          obtain ⟨ph, tl, tr, ctv, dev, bdv, ww⟩ := s
          simp only at hp0 htl htr hct hde hbd hw hS2tl hS2tr hS2w ⊢
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [sA, fWit, hv3, hdI, hdN, hS2tl, hS2tr, hS2w, hp0, hct, hde, hbd,
              Function.update_self,
              Function.update_of_ne (show Stk.ktl ≠ Stk.ktr by decide),
              Function.update_of_ne (show Stk.ktl ≠ Stk.kwit by decide),
              Function.update_of_ne (show Stk.kwit ≠ Stk.ktr by decide)]
        · rw [Function.update_of_ne (by decide) _ _, Function.update_of_ne (by decide) _ _,
            Function.update_of_ne (by decide) _ _, hS2p]
        · rw [Function.update_of_ne (by decide) _ _, Function.update_of_ne (by decide) _ _,
            Function.update_of_ne (by decide) _ _, hS2b]
        · intro j hh1 hh2 hh3 hh4 hh5
          rw [Function.update_of_ne hh4 _ _, Function.update_of_ne hh5 _ _,
            Function.update_of_ne hh4 _ _, hS2o j hh1 hh2]
        · rw [hpre]
          have e0 : (decide (cd v3 = 0)) = false := by rw [hcd]; exact decide_eq_false h0
          have e1 : (decide (cd v3 = 1)) = false := by rw [hcd]; exact decide_eq_false h1
          have e2 : (decide (cd v3 = 2)) = true := by simp [hcd, h2]
          simp only [aux_branch, e0, e1, e2, aux_pop, aux_push, aux_goto, fCell, cond_true,
            cond_false]
          have e7 : (Function.update S2 Stk.ktr (S2 Stk.ktr : List Bool).tail) Stk.kwit
              = (S2 Stk.kwit : List Bool) := Function.update_of_ne (by decide) _ _
          rw [e7, Function.update_of_ne (show Stk.ktr ≠ Stk.kwit by decide),
            Function.update_self]
          simp only [fWit]
      · refine ⟨fCellG v3 ((S2 Stk.ktr : List Bool).head?),
          Function.update (Function.update S2 Stk.ktr (S2 Stk.ktr : List Bool).tail) Stk.ktr
            (gateCell (fCellG v3 ((S2 Stk.ktr : List Bool).head?))
              :: (S2 Stk.ktr : List Bool).tail),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [fCellG]; unfold gateEff; split <;> rfl
        · rw [fCellG]; unfold gateEff; split <;> rfl
        · rw [fCellG]; unfold gateEff; split <;> rfl
        · have hcv : cd { v3 with zc := ((S2 Stk.ktr : List Bool).head?).getD false }
              = cval b0 b1 b2 b3 := rfl
          rw [sT_cval, fCellG]
          obtain ⟨ph, tl, tr, ctv, dev, bdv, ww⟩ := s
          simp only at hp0 htl htr hct hde hbd hw hS2tl hS2tr hS2w ⊢
          rw [hdI, hS2tr] at hcv ⊢
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · revert h0 h1 h2 hcv
            cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> intro h0 h1 h2 hcv <;>
              simp_all [cval, sA, gateEff, cd]
          · rw [Function.update_of_ne (by decide) _ _, Function.update_of_ne (by decide) _ _,
              hS2tl]
            revert h0 h1 h2
            cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> intro h0 h1 h2 <;>
              simp_all [cval, sA]
          · rw [Function.update_self]
            revert h0 h1 h2 hcv
            cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> intro h0 h1 h2 hcv <;>
              simp_all [cval, sA, gateEff, gateCell, cd]
          · revert h0 h1 h2 hcv
            cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> intro h0 h1 h2 hcv <;>
              simp_all [cval, sA, gateEff, cd]
          · revert h0 h1 h2 hcv
            cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> intro h0 h1 h2 hcv <;>
              simp_all [cval, sA, gateEff, cd]
          · revert h0 h1 h2 hcv
            cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> intro h0 h1 h2 hcv <;>
              simp_all [cval, sA, gateEff, cd]
          · rw [Function.update_of_ne (by decide) _ _, Function.update_of_ne (by decide) _ _,
              hS2w]
            revert h0 h1 h2
            cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> intro h0 h1 h2 <;>
              simp_all [cval, sA]
        · rw [Function.update_of_ne (by decide) _ _, Function.update_of_ne (by decide) _ _, hS2p]
        · rw [Function.update_of_ne (by decide) _ _, Function.update_of_ne (by decide) _ _, hS2b]
        · intro j hh1 hh2 hh3 hh4 _
          rw [Function.update_of_ne hh4 _ _, Function.update_of_ne hh4 _ _, hS2o j hh1 hh2]
        · rw [hpre]
          have e0 : (decide (cd v3 = 0)) = false := by rw [hcd]; exact decide_eq_false h0
          have e1 : (decide (cd v3 = 1)) = false := by rw [hcd]; exact decide_eq_false h1
          have e2 : (decide (cd v3 = 2)) = false := by rw [hcd]; exact decide_eq_false h2
          simp only [aux_branch, e0, e1, e2, aux_pop, aux_push, aux_goto, cond_false]
          rw [Function.update_self]

private lemma exitStep (dg : ZMod 8) (v : Reg) (S : ∀ j, List (Gam j))
    (hp : (S Stk.kprog : List Bool) = []) :
    TM2.step (prog dg) ⟨some Lbl.ld1, v, S⟩
      = some ⟨some Lbl.lfin, { v with fin := true }, S⟩ := by
  rw [aux_step]
  simp only [prog]
  rw [aux_pop, hp]
  simp only [List.head?_nil, List.tail_nil, fRd0, aux_branch, aux_goto]
  have hS : Function.update S Stk.kprog ([] : List Bool) = S := by
    conv_rhs => rw [← Function.update_eq_self Stk.kprog S]
    rw [hp]
  simp [hS]

private lemma gc_cons (b0 : Bool) (t : List Bool) : gc (b0 :: t) = 1 + gc t.tail.tail.tail := by
  cases t with
  | nil => rfl
  | cons b1 t1 =>
      cases t1 with
      | nil => rfl
      | cons b2 t2 => cases t2 with | nil => rfl | cons b3 t3 => rfl

private lemma rb_cons (b0 : Bool) (t : List Bool) (s : St) :
    rb (b0 :: t) s
      = rb t.tail.tail.tail (sT s (cval b0 t.headI t.tail.headI t.tail.tail.headI)) := by
  cases t with
  | nil => rfl
  | cons b1 t1 =>
      cases t1 with
      | nil => rfl
      | cons b2 t2 => cases t2 with | nil => rfl | cons b3 t3 => rfl

private lemma pd_cons (b0 : Bool) (t : List Bool) :
    pd (b0 :: t)
      = b0 :: t.headI :: t.tail.headI :: t.tail.tail.headI :: pd t.tail.tail.tail := by
  cases t with
  | nil => rfl
  | cons b1 t1 =>
      cases t1 with
      | nil => rfl
      | cons b2 t2 => cases t2 with | nil => rfl | cons b3 t3 => rfl

private lemma len_drop3 (t : List Bool) : t.tail.tail.tail.length ≤ t.length := by
  cases t with
  | nil => simp
  | cons b1 t1 =>
      cases t1 with
      | nil => simp
      | cons b2 t2 =>
          cases t2 with
          | nil => simp
          | cons b3 t3 => simp only [List.tail_cons, List.length_cons]; omega

private lemma runLoop (dg : ZMod 8) :
    ∀ (n : ℕ) (bits : List Bool), bits.length ≤ n →
      ∀ (s : St) (v : Reg) (S : ∀ j, List (Gam j)),
      Corr s v S → (S Stk.kprog : List Bool) = bits →
      ∃ (w : Reg) (T : ∀ j, List (Gam j)),
        w.ph2 = v.ph2 ∧ w.p1 = v.p1 ∧ w.d1 = v.d1 ∧
        Corr (rb bits s) w T ∧
        (T Stk.kprog : List Bool) = [] ∧
        (T Stk.kprogB : List Bool) = (pd bits).reverse ++ (S Stk.kprogB : List Bool) ∧
        (∀ j, j ≠ Stk.kprog → j ≠ Stk.kprogB → j ≠ Stk.ktl → j ≠ Stk.ktr → j ≠ Stk.kwit →
          T j = S j) ∧
        (fun cf : Option (Cfg Gam Lbl Reg) => cf.bind (TM2.step (prog dg)))^[gc bits + 1]
            (some ⟨some Lbl.ld1, v, S⟩)
          = some ⟨some Lbl.lfin, w, T⟩ := by
  intro n
  induction n with
  | zero =>
      intro bits hb s v S hC hp
      have hnil : bits = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hb)
      subst hnil
      refine ⟨{ v with fin := true }, S, rfl, rfl, rfl, hC, hp, by simp [pd],
        fun j _ _ _ _ _ => rfl, ?_⟩
      show (fun cf : Option (Cfg Gam Lbl Reg) => cf.bind (TM2.step (prog dg)))^[0 + 1] _ = _
      refine one_step dg _ _ ?_
      exact exitStep dg v S hp
  | succ n ih =>
      intro bits hb s v S hC hp
      cases bits with
      | nil =>
          refine ⟨{ v with fin := true }, S, rfl, rfl, rfl, hC, hp, by simp [pd],
            fun j _ _ _ _ _ => rfl, ?_⟩
          show (fun cf : Option (Cfg Gam Lbl Reg) => cf.bind (TM2.step (prog dg)))^[0 + 1] _ = _
          refine one_step dg _ _ ?_
          exact exitStep dg v S hp
      | cons b0 t =>
          obtain ⟨w1, T1, e1, e2, e3, hC1, hp1, hb1, hfr1, hstep1⟩ :=
            chunkStep dg b0 t.headI t.tail.headI t.tail.tail.headI t t.tail.tail.tail s v S
              rfl rfl rfl rfl hC hp
          have hlen : t.tail.tail.tail.length ≤ n := by
            have h := len_drop3 t
            simp only [List.length_cons] at hb
            omega
          obtain ⟨w2, T2, f1, f2, f3, hC2, hp2, hb2, hfr2, hstep2⟩ :=
            ih t.tail.tail.tail hlen _ w1 T1 hC1 hp1
          refine ⟨w2, T2, by rw [f1, e1], by rw [f2, e2], by rw [f3, e3], ?_, hp2, ?_, ?_, ?_⟩
          · rw [rb_cons]; exact hC2
          · rw [hb2, hb1, pd_cons]
            simp [List.reverse_cons]
          · intro j hj1 hj2 hj3 hj4 hj5
            rw [hfr2 j hj1 hj2 hj3 hj4 hj5, hfr1 j hj1 hj2 hj3 hj4 hj5]
          · rw [gc_cons]
            have hh : 1 + gc t.tail.tail.tail + 1 = (gc t.tail.tail.tail + 1) + 1 := by omega
            rw [hh, Function.iterate_succ_apply]
            show ((fun cf : Option (Cfg Gam Lbl Reg) =>
                cf.bind (TM2.step (prog dg)))^[gc t.tail.tail.tail + 1])
                (TM2.step (prog dg) ⟨some Lbl.ld1, v, S⟩) = _
            rw [hstep1, hstep2]

/-! ### 8.  Arithmetic of the walk -/

private lemma sA_lens (s : St) (m : ℕ) :
    (sA s m).2.1.length + (sA s m).2.2.1.length ≤ s.2.1.length + s.2.2.1.length + 1 ∧
      (sA s m).2.2.2.2.2.2.length ≤ s.2.2.2.2.2.2.length := by
  obtain ⟨ph, tl, tr, ctv, dev, bdv, ww⟩ := s
  match m with
  | 0 => refine ⟨?_, ?_⟩ <;> simp only [sA, List.length_cons, List.length_tail] <;> omega
  | 1 => refine ⟨?_, ?_⟩ <;> simp only [sA, List.length_cons, List.length_tail] <;> omega
  | 2 => refine ⟨?_, ?_⟩ <;> simp only [sA, List.length_cons, List.length_tail] <;> omega
  | 3 => refine ⟨?_, ?_⟩ <;> simp only [sA, List.length_cons, List.length_tail] <;> omega
  | 4 => refine ⟨?_, ?_⟩ <;> simp only [sA, List.length_cons, List.length_tail] <;> omega
  | 5 => refine ⟨?_, ?_⟩ <;> simp only [sA, List.length_cons, List.length_tail] <;> omega
  | 6 => refine ⟨?_, ?_⟩ <;> simp only [sA, List.length_cons, List.length_tail] <;> omega
  | 7 => refine ⟨?_, ?_⟩ <;> simp only [sA, List.length_cons, List.length_tail] <;> omega
  | 8 => refine ⟨?_, ?_⟩ <;> simp only [sA, List.length_cons, List.length_tail] <;> omega
  | (k + 9) =>
      refine ⟨?_, ?_⟩ <;> simp only [sA, List.length_cons, List.length_tail] <;> omega

private lemma rb_lens : ∀ (n : ℕ) (u : List Bool), u.length ≤ n → ∀ s : St,
    (rb u s).2.1.length + (rb u s).2.2.1.length ≤ s.2.1.length + s.2.2.1.length + u.length ∧
      (rb u s).2.2.2.2.2.2.length ≤ s.2.2.2.2.2.2.length := by
  intro n
  induction n with
  | zero =>
      intro u hu s
      have h : u = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hu)
      subst h
      exact ⟨by simp [rb], by simp [rb]⟩
  | succ n ih =>
      intro u hu s
      cases u with
      | nil => exact ⟨by simp [rb], by simp [rb]⟩
      | cons b0 t =>
          have hd3 : t.tail.tail.tail.length ≤ t.length := len_drop3 t
          have hlen : t.tail.tail.tail.length ≤ n := by
            simp only [List.length_cons] at hu
            omega
          obtain ⟨g1, g2⟩ := ih t.tail.tail.tail hlen
            (sT s (cval b0 t.headI t.tail.headI t.tail.tail.headI))
          obtain ⟨k1, k2⟩ := sA_lens s ((cval b0 t.headI t.tail.headI t.tail.tail.headI) % 16)
          have hsts : sT s (cval b0 t.headI t.tail.headI t.tail.tail.headI)
              = sA s ((cval b0 t.headI t.tail.headI t.tail.tail.headI) % 16) := rfl
          rw [hsts] at g1 g2
          rw [rb_cons, hsts]
          simp only [List.length_cons]
          constructor
          · omega
          · omega

private lemma gc_le : ∀ (n : ℕ) (u : List Bool), u.length ≤ n → gc u ≤ u.length := by
  intro n
  induction n with
  | zero =>
      intro u hu
      have h : u = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hu)
      subst h; simp [gc]
  | succ n ih =>
      intro u hu
      cases u with
      | nil => simp [gc]
      | cons b0 t =>
          have hd3 : t.tail.tail.tail.length ≤ t.length := len_drop3 t
          have hlen : t.tail.tail.tail.length ≤ n := by
            simp only [List.length_cons] at hu
            omega
          have h := ih t.tail.tail.tail hlen
          rw [gc_cons]
          simp only [List.length_cons]
          omega

private lemma pd_len : ∀ (n : ℕ) (u : List Bool), u.length ≤ n →
    (pd u).length ≤ u.length + 3 := by
  intro n
  induction n with
  | zero =>
      intro u hu
      have h : u = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hu)
      subst h; simp [pd]
  | succ n ih =>
      intro u hu
      cases u with
      | nil => simp [pd]
      | cons b0 t =>
          cases t with
          | nil => simp [pd]
          | cons b1 t1 =>
              cases t1 with
              | nil => simp [pd]
              | cons b2 t2 =>
                  cases t2 with
                  | nil => simp [pd]
                  | cons b3 r =>
                      have hlen : r.length ≤ n := by
                        simp only [List.length_cons] at hu
                        omega
                      have h := ih r hlen
                      simp only [pd, List.length_cons]
                      omega

private lemma rb_pd : ∀ (n : ℕ) (u : List Bool), u.length ≤ n → ∀ s : St,
    rb (pd u) s = rb u s := by
  intro n
  induction n with
  | zero =>
      intro u hu s
      have h : u = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hu)
      subst h; rfl
  | succ n ih =>
      intro u hu s
      cases u with
      | nil => rfl
      | cons b0 t =>
          have hd3 : t.tail.tail.tail.length ≤ t.length := len_drop3 t
          have hlen : t.tail.tail.tail.length ≤ n := by
            simp only [List.length_cons] at hu
            omega
          rw [pd_cons, rb_cons, rb_cons]
          exact ih t.tail.tail.tail hlen _

/-! ### 9.  The program encoding and the branch evaluator -/

private def ob (c : ℕ) : List Bool :=
  [decide (c % 2 = 1), decide (c / 2 % 2 = 1), decide (c / 4 % 2 = 1), decide (c / 8 % 2 = 1)]

private def encP (P : List ℕ) : PvsNP.Str := (P.flatMap ob).reverse

private def hcnt : List ℕ → ℕ
  | [] => 0
  | c :: P => (if c % 16 = 2 then 1 else 0) + hcnt P

private def evP (P : List ℕ) (bs : List Bool) : Option ℕ :=
  match P.foldl sT (0, [], [], false, false, false, bs) with
  | (ph, _, _, _, de, bd, w) => if de || bd || !w.isEmpty then none else some ph.val

private lemma cval_ob (c : ℕ) :
    cval (decide (c % 2 = 1)) (decide (c / 2 % 2 = 1)) (decide (c / 4 % 2 = 1))
      (decide (c / 8 % 2 = 1)) = c % 16 := by
  by_cases h0 : c % 2 = 1 <;> by_cases h1 : c / 2 % 2 = 1 <;> by_cases h2 : c / 4 % 2 = 1 <;>
    by_cases h3 : c / 8 % 2 = 1 <;> simp [cval, h0, h1, h2, h3] <;> omega

private lemma sT_mod (s : St) (c : ℕ) : sT s (c % 16) = sT s c := by
  show sA s (c % 16 % 16) = sA s (c % 16)
  congr 1
  omega

private lemma rb_flat (P : List ℕ) : ∀ s : St, rb (P.flatMap ob) s = P.foldl sT s := by
  induction P with
  | nil => intro s; rfl
  | cons c P ih =>
      intro s
      have h1 : (c :: P).flatMap ob = ob c ++ P.flatMap ob := by simp [List.flatMap_cons]
      rw [h1]
      show rb (decide (c % 2 = 1) :: decide (c / 2 % 2 = 1) :: decide (c / 4 % 2 = 1) ::
        decide (c / 8 % 2 = 1) :: P.flatMap ob) s = _
      rw [rb, cval_ob, sT_mod, List.foldl_cons, ih]

private lemma encP_rev (P : List ℕ) : (encP P).reverse = P.flatMap ob := by
  rw [encP, List.reverse_reverse]

private lemma encP_len (P : List ℕ) : (encP P).length = 4 * P.length := by
  induction P with
  | nil => rfl
  | cons c P ih =>
      rw [encP, List.length_reverse, List.flatMap_cons, List.length_append]
      rw [encP, List.length_reverse] at ih
      simp only [ob, List.length_cons, List.length_nil, List.length_cons]
      omega

private def setW (s : St) (w : List Bool) : St :=
  (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1, w)

private def setB (s : St) : St :=
  (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, true, s.2.2.2.2.2.2)

private lemma sA_wit (s : St) (m : ℕ) :
    (sA s m).2.2.2.2.2.2 = if m = 2 then s.2.2.2.2.2.2.tail else s.2.2.2.2.2.2 := by
  obtain ⟨ph, tl, tr, ctv, dev, bdv, ww⟩ := s
  match m with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | (k + 9) => simp [sA]

private lemma sA_frame (s : St) (z : List Bool) (m : ℕ) (h : m = 2 → s.2.2.2.2.2.2 ≠ []) :
    sA (setW s (s.2.2.2.2.2.2 ++ z)) m = setW (sA s m) ((sA s m).2.2.2.2.2.2 ++ z) := by
  obtain ⟨ph, tl, tr, ctv, dev, bdv, ww⟩ := s
  match m with
  | 0 => rfl
  | 1 => rfl
  | 2 =>
      have hw : ww ≠ [] := h rfl
      cases ww with
      | nil => exact absurd rfl hw
      | cons a u => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | (k + 9) => simp [sA, setW]

private lemma sA_bad (s : St) (m : ℕ) : sA (setB s) m = setB (sA s m) := by
  obtain ⟨ph, tl, tr, ctv, dev, bdv, ww⟩ := s
  match m with
  | 0 => rfl
  | 1 => rfl
  | 2 => simp [sA, setB]
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | (k + 9) => simp [sA, setB]

private lemma fold_bad (P : List ℕ) : ∀ s : St, P.foldl sT (setB s) = setB (P.foldl sT s) := by
  induction P with
  | nil => intro s; rfl
  | cons c P ih =>
      intro s
      rw [List.foldl_cons, List.foldl_cons]
      show P.foldl sT (sA (setB s) (c % 16)) = _
      rw [sA_bad]
      exact ih (sA s (c % 16))

private lemma fold_wit (P : List ℕ) : ∀ s : St, hcnt P ≤ s.2.2.2.2.2.2.length →
    (P.foldl sT s).2.2.2.2.2.2 = s.2.2.2.2.2.2.drop (hcnt P) := by
  induction P with
  | nil => intro s _; rfl
  | cons c P ih =>
      intro s hs
      have hc : hcnt (c :: P) = (if c % 16 = 2 then 1 else 0) + hcnt P := rfl
      have hstep : (sT s c).2.2.2.2.2.2
          = if c % 16 = 2 then s.2.2.2.2.2.2.tail else s.2.2.2.2.2.2 := sA_wit s (c % 16)
      rw [List.foldl_cons]
      by_cases h2 : c % 16 = 2
      · rw [hc, if_pos h2] at hs
        have hlen : hcnt P ≤ (sT s c).2.2.2.2.2.2.length := by
          rw [hstep, if_pos h2, List.length_tail]
          omega
        rw [ih (sT s c) hlen, hstep, if_pos h2, hc, if_pos h2]
        rw [← List.drop_one, List.drop_drop]
      · rw [hc, if_neg h2] at hs
        have hlen : hcnt P ≤ (sT s c).2.2.2.2.2.2.length := by
          rw [hstep, if_neg h2]
          omega
        rw [ih (sT s c) hlen, hstep, if_neg h2, hc, if_neg h2, Nat.zero_add]

private lemma fold_frame (P : List ℕ) : ∀ (s : St) (z : List Bool),
    hcnt P ≤ s.2.2.2.2.2.2.length →
    P.foldl sT (setW s (s.2.2.2.2.2.2 ++ z))
      = setW (P.foldl sT s) ((P.foldl sT s).2.2.2.2.2.2 ++ z) := by
  induction P with
  | nil => intro s z _; rfl
  | cons c P ih =>
      intro s z hs
      have hc : hcnt (c :: P) = (if c % 16 = 2 then 1 else 0) + hcnt P := rfl
      have hw2 : (sT s c).2.2.2.2.2.2
          = if c % 16 = 2 then s.2.2.2.2.2.2.tail else s.2.2.2.2.2.2 := sA_wit s (c % 16)
      have hne : c % 16 = 2 → s.2.2.2.2.2.2 ≠ [] := by
        intro h2 hnil
        rw [hc, if_pos h2, hnil] at hs
        simp at hs
      have hstep : sA (setW s (s.2.2.2.2.2.2 ++ z)) (c % 16)
          = setW (sA s (c % 16)) ((sA s (c % 16)).2.2.2.2.2.2 ++ z) := sA_frame s z (c % 16) hne
      have hlen : hcnt P ≤ (sT s c).2.2.2.2.2.2.length := by
        by_cases h2 : c % 16 = 2
        · rw [hc, if_pos h2] at hs
          rw [hw2, if_pos h2, List.length_tail]
          omega
        · rw [hc, if_neg h2] at hs
          rw [hw2, if_neg h2]
          omega
      rw [List.foldl_cons, List.foldl_cons]
      show P.foldl sT (sA (setW s (s.2.2.2.2.2.2 ++ z)) (c % 16)) = _
      rw [hstep]
      exact ih (sT s c) z hlen

/-! ### 10.  The checker equation -/

private lemma zbridge : ∀ a b d : ZMod 8, ((a.val + 8 - b.val % 8) % 8 = d.val) ↔ (a - b = d) := by
  decide

private lemma vbridge : ∀ a d : ZMod 8, (a.val = d.val) ↔ (a = d) := by
  decide

private lemma Rf_eq (dg : ZMod 8) (P : List ℕ) (w : PvsNP.Str) :
    Rf dg (encP P, w) = decide (evP P w = some dg.val) := by
  have hrev : (encP P).reverse = P.flatMap ob := encP_rev P
  have hs : rb (encP P).reverse (initSt w) = P.foldl sT (initSt w) := by
    rw [hrev, rb_flat]
  set F : St := P.foldl sT (initSt w) with hFdef
  have hev : evP P w
      = if F.2.2.2.2.1 || F.2.2.2.2.2.1 || !F.2.2.2.2.2.2.isEmpty then none
        else some F.1.val := by
    rw [evP]
    rfl
  rw [Rf]
  simp only [hs, hev]
  cases ha : F.2.2.2.2.1 <;> cases hb : F.2.2.2.2.2.1 <;>
    cases hc : F.2.2.2.2.2.2.isEmpty <;>
    simp [ha, hb, hc, vbridge]

/-! ### 11.  The machine computes the checker in linear time -/

private lemma machineRun (dg : ZMod 8) (x y : PvsNP.Str) :
    Nonempty (Turing.TM2OutputsInTime (TMc dg)
      (x.map Sum.inl ++ y.map Sum.inr) (some [Rf dg (x, y)])
      (24 * (x.length + y.length) + 48)) := by
  classical
  set inp : List (Bool ⊕ Bool) := x.map Sum.inl ++ y.map Sum.inr with hinp
  set S0 : ∀ j, List (Gam j) := (Turing.initList (TMc dg) inp).stk with hS0
  obtain ⟨hl, hvar, hk0, hko, hhl, hhvar, hhk1, hhko⟩ :=
    ShiTM.initList_haltList_laws (TMc dg) inp ([Rf dg (x, y)] : List Bool)
  have hinit : Turing.initList (TMc dg) inp = ⟨some Lbl.la, R0, S0⟩ := rfl
  -- stage 1: read the input pair onto `kprog` and `kwitR`
  obtain ⟨w1, T1, sm1, hT1in, hT1p, hT1w, hfr1, hit1⟩ := laLoop dg inp R0 S0 hk0
  have hz1 : (S0 Stk.kprog : List Bool) = [] :=
    hko Stk.kprog (show Stk.kprog ≠ Stk.kin by decide)
  have hz2 : (S0 Stk.kwitR : List Bool) = [] :=
    hko Stk.kwitR (show Stk.kwitR ≠ Stk.kin by decide)
  have hT1p' : (T1 Stk.kprog : List Bool) = x.reverse := by
    rw [hT1p, hinp, inls_enc, hz1]
    simp
  have hT1w' : (T1 Stk.kwitR : List Bool) = y.reverse := by
    rw [hT1w, hinp, inrs_enc, hz2]
    simp
  have hT1o : ∀ j, j ≠ Stk.kin → j ≠ Stk.kprog → j ≠ Stk.kwitR → T1 j = [] := by
    intro j h1 h2 h3
    rw [hfr1 j h1 h2 h3]
    exact hko j (show j ≠ Stk.kin from h1)
  -- stage 2: reverse the witness onto `kwit`
  obtain ⟨w2, T2, sm2, hT2wR, hT2w, hfr2, hit2⟩ :=
    xferLoop dg Stk.kwitR Stk.kwit Lbl.lrw Lbl.ld1 (by decide) fDr (fun v => v.ib) id
      (fun v => rfl) (fun v yb => ⟨yb, rfl⟩) (fun v yb => rfl) (fun v yb => rfl) rfl
      y.reverse w1 T1 hT1w'
  have hT2w' : (T2 Stk.kwit : List Bool) = y := by
    rw [hT2w, hT1o Stk.kwit (by decide) (by decide) (by decide)]
    simp
  have hT2p : (T2 Stk.kprog : List Bool) = x.reverse := by
    rw [hfr2 Stk.kprog (by decide) (by decide)]
    exact hT1p'
  have hT2o : ∀ j, j ≠ Stk.kin → j ≠ Stk.kprog → j ≠ Stk.kwitR → j ≠ Stk.kwit → T2 j = [] := by
    intro j h1 h2 h3 h4
    rw [hfr2 j h3 h4]
    exact hT1o j h1 h2 h3
  have hT2in : (T2 Stk.kin : List (Bool ⊕ Bool)) = [] := by
    rw [hfr2 Stk.kin (by decide) (by decide)]
    exact hT1in
  -- stage 3: the single interpreter pass
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := Same_trans sm1 sm2
  have hC2 : Corr (initSt y) w2 T2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hT2w'⟩
    · rw [q1]; rfl
    · rw [hT2o Stk.ktl (by decide) (by decide) (by decide) (by decide)]; rfl
    · rw [hT2o Stk.ktr (by decide) (by decide) (by decide) (by decide)]; rfl
    · rw [q2]; rfl
    · rw [q3]; rfl
    · rw [q4]; rfl
  obtain ⟨w3, T3, r1, r2, r3, hC3, hT3p, hT3B, hfr3, hit3⟩ :=
    runLoop dg x.reverse.length x.reverse le_rfl (initSt y) w2 T2 hC2 hT2p
  set s1 : St := rb x.reverse (initSt y) with hs1def
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC3
  have hT3B' : (T3 Stk.kprogB : List Bool) = (pd x.reverse).reverse := by
    rw [hT3B, hT2o Stk.kprogB (by decide) (by decide) (by decide) (by decide)]
    simp
  have hT3o : ∀ j, j ≠ Stk.kin → j ≠ Stk.kprog → j ≠ Stk.kwitR → j ≠ Stk.kwit →
      j ≠ Stk.kprogB → j ≠ Stk.ktl → j ≠ Stk.ktr → T3 j = [] := by
    intro j h1 h2 h3 h4 h5 h6 h7
    rw [hfr3 j h2 h5 h6 h7 h4]
    exact hT2o j h1 h2 h3 h4
  have hT3in : (T3 Stk.kin : List (Bool ⊕ Bool)) = [] := by
    rw [hfr3 Stk.kin (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hT2in
  have hT3wR : (T3 Stk.kwitR : List Bool) = [] := by
    rw [hfr3 Stk.kwitR (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hT2wR
  have hT3out : (T3 Stk.kout : List Bool) = [] := by
    rw [hfr3 Stk.kout (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hT2o Stk.kout (by decide) (by decide) (by decide) (by decide)
  -- stage 4: the answer
  have hacc : acc dg (fPk w3 ((T3 Stk.kwit : List Bool).head?)) = Rf dg (x, y) := by
    have e1 : (fPk w3 ((T3 Stk.kwit : List Bool).head?)).bd = s1.2.2.2.2.2.1 := c6
    have e2 : (fPk w3 ((T3 Stk.kwit : List Bool).head?)).de = s1.2.2.2.2.1 := c5
    have e3 : (fPk w3 ((T3 Stk.kwit : List Bool).head?)).p = s1.1 := c1
    have e6 : (fPk w3 ((T3 Stk.kwit : List Bool).head?)).fin
        = !s1.2.2.2.2.2.2.isEmpty := by
      show ((T3 Stk.kwit : List Bool).head?).isSome = _
      rw [hdS, c7]
    rw [acc, e1, e2, e3, e6, Rf]
    simp only [← hs1def, Bool.not_not]
  have hit9 : TM2.step (prog dg) ⟨some Lbl.lfin, w3, T3⟩
      = some ⟨some Lbl.ldw, fPk w3 ((T3 Stk.kwit : List Bool).head?),
          Function.update T3 Stk.kout ([Rf dg (x, y)] : List Bool)⟩ := by
    rw [aux_step]
    simp only [prog]
    rw [aux_peek, aux_push, aux_goto, hacc, hT3out]
  set T9 : ∀ j, List (Gam j) :=
    Function.update T3 Stk.kout ([Rf dg (x, y)] : List Bool) with hT9def
  set w9 : Reg := fPk w3 ((T3 Stk.kwit : List Bool).head?) with hw9def
  have hT9o : ∀ j, j ≠ Stk.kout → T9 j = T3 j := by
    intro j hj
    rw [hT9def]
    exact Function.update_of_ne hj _ _
  have hT9out : (T9 Stk.kout : List Bool) = [Rf dg (x, y)] := by
    rw [hT9def, Function.update_self]
  -- stages 5..8: drain
  obtain ⟨w10, T10, sm10, hT10, hfr10, hit10⟩ :=
    drainLoop dg Stk.kwit Lbl.ldw Lbl.ldl fDr (fun v => rfl) (fun v yb => ⟨yb, rfl⟩) rfl
      (T9 Stk.kwit) w9 T9 rfl
  obtain ⟨w11, T11, sm11, hT11, hfr11, hit11⟩ :=
    drainLoop dg Stk.ktl Lbl.ldl Lbl.ldr fDr (fun v => rfl) (fun v yb => ⟨yb, rfl⟩) rfl
      (T10 Stk.ktl) w10 T10 rfl
  obtain ⟨w12, T12, sm12, hT12, hfr12, hit12⟩ :=
    drainLoop dg Stk.ktr Lbl.ldr Lbl.ldb fDr (fun v => rfl) (fun v yb => ⟨yb, rfl⟩) rfl
      (T11 Stk.ktr) w11 T11 rfl
  obtain ⟨w13, T13, sm13, hT13, hfr13, hit13⟩ :=
    drainLoop dg Stk.kprogB Lbl.ldb Lbl.lrst fDr (fun v => rfl) (fun v yb => ⟨yb, rfl⟩) rfl
      (T12 Stk.kprogB) w12 T12 rfl
  -- stage 9 and the halt step
  have hit14 : TM2.step (prog dg) ⟨some Lbl.lrst, w13, T13⟩
      = some ⟨some Lbl.lhlt, R0, T13⟩ := by
    rw [aux_step]
    simp only [prog]
    rw [aux_load, aux_goto]
  have hit15 : TM2.step (prog dg) ⟨some Lbl.lhlt, R0, T13⟩ = some ⟨none, R0, T13⟩ := by
    rw [aux_step]
    simp only [prog]
    rfl
  -- the final stacks
  have hT13out : (T13 Stk.kout : List Bool) = [Rf dg (x, y)] := by
    rw [hfr13 Stk.kout (by decide), hfr12 Stk.kout (by decide), hfr11 Stk.kout (by decide),
      hfr10 Stk.kout (by decide)]
    exact hT9out
  have hT13o : ∀ j, j ≠ Stk.kout → T13 j = [] := by
    intro j hj
    by_cases h1 : j = Stk.kprogB
    · subst h1; exact hT13
    · rw [hfr13 j h1]
      by_cases h2 : j = Stk.ktr
      · subst h2; exact hT12
      · rw [hfr12 j h2]
        by_cases h3 : j = Stk.ktl
        · subst h3; exact hT11
        · rw [hfr11 j h3]
          by_cases h4 : j = Stk.kwit
          · subst h4; exact hT10
          · rw [hfr10 j h4, hT9o j hj]
            by_cases h5 : j = Stk.kin
            · subst h5; exact hT3in
            · by_cases h6 : j = Stk.kprog
              · subst h6; exact hT3p
              · by_cases h7 : j = Stk.kwitR
                · subst h7; exact hT3wR
                · exact hT3o j h5 h6 h7 h4 h1 h3 h2
  -- assemble the run
  have comp : ∀ (a b : ℕ) (e0 e1 e2 : Cfg Gam Lbl Reg),
      (fun cf : Option (Cfg Gam Lbl Reg) => cf.bind (TM2.step (prog dg)))^[a] (some e0)
          = some e1 →
      (fun cf : Option (Cfg Gam Lbl Reg) => cf.bind (TM2.step (prog dg)))^[b] (some e1)
          = some e2 →
      (fun cf : Option (Cfg Gam Lbl Reg) => cf.bind (TM2.step (prog dg)))^[b + a] (some e0)
          = some e2 := by
    intro a b e0 e1 e2 hA hB
    rw [Function.iterate_add_apply, hA]
    exact hB
  have z1 : (fun cf : Option (Cfg Gam Lbl Reg) => cf.bind (TM2.step (prog dg)))^[
      inp.length + 1] (some (Turing.initList (TMc dg) inp))
      = some ⟨some Lbl.lrw, w1, T1⟩ := by
    rw [hinit]; exact hit1
  have z2 := comp _ _ _ _ _ z1 hit2
  have z3 := comp _ _ _ _ _ z2 hit3
  have z4 := comp _ _ _ _ _ z3 (one_step dg _ _ hit9)
  have z5 := comp _ _ _ _ _ z4 hit10
  have z6 := comp _ _ _ _ _ z5 hit11
  have z7 := comp _ _ _ _ _ z6 hit12
  have z8 := comp _ _ _ _ _ z7 hit13
  have z9 := comp _ _ _ _ _ z8 (one_step dg _ _ hit14)
  have z10 := comp _ _ _ _ _ z9 (one_step dg _ _ hit15)
  -- the halting configuration
  have hcfg : (⟨none, R0, T13⟩ : Cfg Gam Lbl Reg)
      = Turing.haltList (TMc dg) ([Rf dg (x, y)] : List Bool) := by
    have hstk : T13 = (Turing.haltList (TMc dg) ([Rf dg (x, y)] : List Bool)).stk := by
      funext j
      by_cases hj : j = Stk.kout
      · subst hj
        rw [hT13out]
        exact hhk1.symm
      · rw [hT13o j hj]
        exact (hhko j hj).symm
    rw [hstk]
    rfl
  -- the length bounds
  have hL1 : inp.length = x.length + y.length := by
    rw [hinp]
    simp
  have hL3 : gc x.reverse ≤ x.length := by
    have := gc_le x.reverse.length x.reverse le_rfl
    simpa using this
  have hrb1 := rb_lens x.reverse.length x.reverse le_rfl (initSt y)
  have hL4 : (T3 Stk.ktl).length + (T3 Stk.ktr).length ≤ x.length := by
    rw [c2, c3]
    have h := hrb1.1
    rw [← hs1def] at h
    simpa [initSt] using h
  have hL4w : (T3 Stk.kwit).length ≤ y.length := by
    rw [c7]
    have h := hrb1.2
    rw [← hs1def] at h
    simpa [initSt] using h
  have hL5 : (T9 Stk.kwit).length ≤ y.length := by
    rw [hT9o Stk.kwit (by decide)]
    exact hL4w
  have hL6 : (T10 Stk.ktl).length + (T11 Stk.ktr).length ≤ x.length := by
    have e1 : (T10 Stk.ktl : List Bool) = (T3 Stk.ktl : List Bool) := by
      rw [hfr10 Stk.ktl (by decide), hT9o Stk.ktl (by decide)]
    have e2 : (T11 Stk.ktr : List Bool) = (T3 Stk.ktr : List Bool) := by
      rw [hfr11 Stk.ktr (by decide), hfr10 Stk.ktr (by decide), hT9o Stk.ktr (by decide)]
    rw [e1, e2]
    exact hL4
  have hL7 : (T12 Stk.kprogB).length ≤ x.length + 3 := by
    have e1 : (T12 Stk.kprogB : List Bool) = (T3 Stk.kprogB : List Bool) := by
      rw [hfr12 Stk.kprogB (by decide), hfr11 Stk.kprogB (by decide),
        hfr10 Stk.kprogB (by decide), hT9o Stk.kprogB (by decide)]
    rw [e1, hT3B', List.length_reverse]
    have := pd_len x.reverse.length x.reverse le_rfl
    simpa using this
  have hrx : x.reverse.length = x.length := by simp
  have hry : y.reverse.length = y.length := by simp
  have hz := z10
  rw [hcfg] at hz
  refine ⟨⟨⟨_, hz⟩, ?_⟩⟩
  simp only [hL1, hrx, hry]
  omega

/-! ### 12.  The polynomial-time certificate -/

private lemma mapid (l : List (Bool ⊕ Bool)) :
    List.map (Equiv.cast (rfl : Gam Stk.kin = (Bool ⊕ Bool))).invFun l = l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, ih]; rfl

private lemma mapidB (l : List Bool) :
    List.map (Equiv.cast (rfl : Gam Stk.kout = Bool)).invFun l = l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, ih]; rfl

private lemma polyChk (dg : ZMod 8) :
    ∃ c : Turing.TM2ComputableInPolyTime PvsNP.encodePair Computability.encodeBool (Rf dg),
      c.time = Polynomial.C 24 * Polynomial.X + Polynomial.C 48 := by
  classical
  refine ⟨{ tm := TMc dg
            inputAlphabet := Equiv.cast rfl
            outputAlphabet := Equiv.cast rfl
            time := Polynomial.C 24 * Polynomial.X + Polynomial.C 48
            outputsFun := ?_ }, rfl⟩
  intro a
  obtain ⟨x, y⟩ := a
  have hin : PvsNP.encodePair (x, y) = x.map Sum.inl ++ y.map Sum.inr := rfl
  have hlen : (PvsNP.encodePair (x, y)).length = x.length + y.length := by
    rw [hin]; simp
  have hev : (Polynomial.C 24 * Polynomial.X + Polynomial.C 48).eval
      (PvsNP.encodePair (x, y)).length = 24 * (x.length + y.length) + 48 := by
    rw [hlen]; simp
  rw [hev, hin, mapid, mapidB]
  exact (machineRun dg x y).some

/-! ### 13.  The single-run count -/

private lemma countId (dg : ZMod 8) (P : List ℕ) :
    ShiClassPP.countAccept (Rf dg) (encP P) (hcnt P)
      = (Finset.univ.filter (fun b : Fin (hcnt P) → Bool =>
          evP P (List.ofFn b) = some dg.val)).card := by
  classical
  rw [ShiClassPP.countAccept]
  refine congrArg Finset.card ?_
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Rf_eq, decide_eq_true_eq]

private lemma hcnt_append (P Q : List ℕ) : hcnt (P ++ Q) = hcnt P + hcnt Q := by
  induction P with
  | nil => simp [hcnt]
  | cons c P ih => simp only [List.cons_append, hcnt, ih]; omega

private lemma encP_append (P Q : List ℕ) : encP (P ++ Q) = encP Q ++ encP P := by
  simp [encP, List.flatMap_append, List.reverse_append]

private lemma foldl_app (P Q : List ℕ) (s : St) :
    (P ++ Q).foldl sT s = Q.foldl sT (P.foldl sT s) := by
  induction P generalizing s with
  | nil => rfl
  | cons c P ih =>
      simp only [List.cons_append, List.foldl_cons]
      exact ih (sT s c)

/-! ### 14.  The result -/

theorem _root_.BQPReferenceValidation.candidate19 :
    ∃ (sTr : (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool) → ℕ →
          (ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool))
      (enc : List ℕ → PvsNP.Str) (hc : List ℕ → ℕ) (ev : List ℕ → List Bool → Option ℕ)
      (R : ZMod 8 → PvsNP.Str × PvsNP.Str → Bool) (pol : Polynomial ℕ),
    -- (I) the one-branch gate walk: phase exponent mod 8 and moving head on the basis string
    (∀ (ph : ZMod 8) (tl tr : List Bool) (ct de bd : Bool) (w : List Bool),
        sTr (ph, tl, tr, ct, de, bd, w) 0 = (ph, tl.tail, tl.headI :: tr, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 1 = (ph, tr.headI :: tl, tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 2
          = (ph + (if tr.headI && w.headI then 4 else 0), tl, w.headI :: tr.tail, ct, de,
              bd || w.isEmpty, w.tail)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 3
          = (ph + (if tr.headI then 1 else 0), tl, tr.headI :: tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 4
          = (ph + (if tr.headI then 2 else 0), tl, tr.headI :: tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 5 = (ph, tl, (!tr.headI) :: tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 6 = (ph, tl, tr.headI :: tr.tail, tr.headI, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 7
          = (ph, tl, (xor tr.headI ct) :: tr.tail, ct, de, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 8
          = (ph, tl, tr.headI :: tr.tail, ct, de || !tr.headI, bd, w)
      ∧ sTr (ph, tl, tr, ct, de, bd, w) 9 = (ph, tl, tr.headI :: tr.tail, ct, de, true, w)
      ∧ (∀ c : ℕ, sTr (ph, tl, tr, ct, de, bd, w) c
            = sTr (ph, tl, tr, ct, de, bd, w) (c % 16)))
    -- (II) the encoding, the Hadamard count, the one-branch evaluator
    ∧ enc [] = []
    ∧ (∀ (c : ℕ) (P : List ℕ), enc (c :: P)
          = enc P ++ [decide (c / 8 % 2 = 1), decide (c / 4 % 2 = 1),
                      decide (c / 2 % 2 = 1), decide (c % 2 = 1)])
    ∧ (∀ P : List ℕ, (enc P).length = 4 * P.length)
    ∧ hc [] = 0
    ∧ (∀ (c : ℕ) (P : List ℕ), hc (c :: P) = (if c % 16 = 2 then 1 else 0) + hc P)
    ∧ (∀ (P : List ℕ) (bs : List Bool),
        ev P bs = (match P.foldl sTr (0, [], [], false, false, false, bs) with
                   | (ph, _, _, _, de, bd, w) =>
                       if de || bd || !w.isEmpty then none else some ph.val))
    -- (II') concatenation laws, so a DOUBLED program `U ++ test ++ U†` is budgeted exactly
    ∧ (∀ P Q : List ℕ, hc (P ++ Q) = hc P + hc Q)
    ∧ (∀ P Q : List ℕ, enc (P ++ Q) = enc Q ++ enc P)
    ∧ (∀ (P Q : List ℕ)
          (s : ZMod 8 × List Bool × List Bool × Bool × Bool × Bool × List Bool),
        (P ++ Q).foldl sTr s = Q.foldl sTr (P.foldl sTr s))
    -- (III) the evaluator IS a polynomial-time checking relation, total on every input
    ∧ (∀ dg : ZMod 8, PvsNP.PolyTimeChecker (R dg))
    ∧ (∀ dg : ZMod 8, ∃ c : Turing.TM2ComputableInPolyTime PvsNP.encodePair
          Computability.encodeBool (R dg), c.time = pol)
    ∧ (∀ n : ℕ, pol.eval n = 24 * n + 48)
    ∧ pol.eval 16 = 432
    -- (IV) SINGLE RUN: it accepts exactly the surviving branches at phase `dg`, counted
    -- at `hc Q` — no pair structure, so the endpoint constraint is carried by `Q` itself
    ∧ (∀ (dg : ZMod 8) (Q : List ℕ) (w : PvsNP.Str),
        R dg (enc Q, w) = decide (ev Q w = some dg.val))
    ∧ (∀ (dg : ZMod 8) (Q : List ℕ),
        ShiClassPP.countAccept (R dg) (enc Q) (hc Q)
          = (Finset.univ.filter (fun b : Fin (hc Q) → Bool =>
              ev Q (List.ofFn b) = some dg.val)).card)
    -- (V) non-vacuity, on the two-Hadamard circuit `H, T, H`
    ∧ hc [2, 3, 2] = 2
    ∧ (enc [2, 3, 2]).length = 12
    ∧ ev [2, 3, 2] [false, false] = some 0
    ∧ ev [2, 3, 2] [false, true] = some 0
    ∧ ev [2, 3, 2] [true, false] = some 1
    ∧ ev [2, 3, 2] [true, true] = some 5
    ∧ ev [2, 3, 2] [true] = none
    ∧ ev [2, 3, 2, 8] [true, false] = none
    ∧ ev [2, 3, 2, 8] [true, true] = some 5
    ∧ ev [9] [] = none
    ∧ R 0 (enc [2, 3, 2], [false, false]) = true
    ∧ R 1 (enc [2, 3, 2], [false, false]) = false
    ∧ R 1 (enc [2, 3, 2], [true, false]) = true
    ∧ R 5 (enc [2, 3, 2], [true, true]) = true
    ∧ R 0 (enc [2, 3, 2], [true]) = false
    ∧ R 0 (enc [2, 3, 2], [true, true, true]) = false
    ∧ ShiClassPP.countAccept (R 0) (enc [2, 3, 2]) (hc [2, 3, 2]) = 2
    ∧ ShiClassPP.countAccept (R 1) (enc [2, 3, 2]) (hc [2, 3, 2]) = 1
    ∧ ShiClassPP.countAccept (R 2) (enc [2, 3, 2]) (hc [2, 3, 2]) = 0
    -- (VI) the DOUBLED-CIRCUIT witness: `U = H`, output-wire test, `U† = H`, then the
    -- endpoint test "wire 0 is back to 0" written as `X`, test, `X`.  Exactly one of the
    -- four branch strings survives, at phase 0, and `(1/2)^1 * 1 = 1/2 = ⟨0|H Π H|0⟩`.
    ∧ hc [2, 8, 2, 5, 8, 5] = 2
    ∧ hc [2, 8, 2, 5, 8, 5] = hc [2] + hc [2]
    ∧ ev [2, 8, 2, 5, 8, 5] [true, false] = some 0
    ∧ ev [2, 8, 2, 5, 8, 5] [false, false] = none
    ∧ ev [2, 8, 2, 5, 8, 5] [false, true] = none
    ∧ ev [2, 8, 2, 5, 8, 5] [true, true] = none
    ∧ ShiClassPP.countAccept (R 0) (enc [2, 8, 2, 5, 8, 5])
        (hc [2, 8, 2, 5, 8, 5]) = 1
    ∧ ShiClassPP.countAccept (R 1) (enc [2, 8, 2, 5, 8, 5])
        (hc [2, 8, 2, 5, 8, 5]) = 0
    ∧ ShiClassPP.countAccept (R 3) (enc [2, 8, 2, 5, 8, 5])
        (hc [2, 8, 2, 5, 8, 5]) = 0
    ∧ ShiClassPP.countAccept (R 4) (enc [2, 8, 2, 5, 8, 5])
        (hc [2, 8, 2, 5, 8, 5]) = 0 := by
  classical
  refine ⟨sT, encP, hcnt, evP, Rf, Polynomial.C 24 * Polynomial.X + Polynomial.C 48,
    fun ph tl tr ct de bd w =>
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun c => (sT_mod _ c).symm⟩,
    rfl, ?_, encP_len, rfl, fun c P => rfl, fun P bs => rfl,
    hcnt_append, encP_append, foldl_app,
    ?_, ?_, ?_, ?_, ?_, ?_,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide,
    ?_, ?_, ?_,
    by decide, by decide, by decide, by decide, by decide, by decide,
    ?_, ?_, ?_, ?_⟩
  · intro c P
    simp [encP, List.flatMap_cons, List.reverse_append, ob]
  · intro dg
    obtain ⟨c, -⟩ := polyChk dg
    exact ⟨c⟩
  · exact fun dg => polyChk dg
  · intro n
    simp
  · simp
  · exact fun dg Q w => Rf_eq dg Q w
  · exact fun dg Q => countId dg Q
  · rw [countId]; decide
  · rw [countId]; decide
  · rw [countId]; decide
  · rw [countId]; decide
  · rw [countId]; decide
  · rw [countId]; decide
  · rw [countId]; decide

end BQPReferenceValidation.Source19

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate19
    let target ← getConstInfo ``ShiBQP.single_run_checker_is_polynomial_time_and_counts_branches_by_phase
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.single_run_checker_is_polynomial_time_and_counts_branches_by_phase"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.single_run_checker_is_polynomial_time_and_counts_branches_by_phase"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.single_run_checker_is_polynomial_time_and_counts_branches_by_phase"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate19
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.single_run_checker_is_polynomial_time_and_counts_branches_by_phase; axioms {axioms}"
