import Definitions.Def_ShiBQP_Core
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_PvsNP_polyTimeComputable_comp
import Theorems.Thm_ShiBQP_uniform_family_encoding_is_polynomial_time_computable_from_the_input
import Theorems.Thm_ShiTM_initList_haltList_laws

namespace BQPReferenceValidation.Source22
/-
READ-1.  Reading the circuit description: from `ShiBQP.Uniform F` to a polynomial-time
string function that a checker can call on an input `x` of length `n` to obtain
`ShiBQP.encFamilyAt F n`.

The only missing ingredient was the length-to-unary transducer `x ↦ unary x.length`,
which did not exist in the development; it is built here as an explicit two-stack
`Turing.FinTM2` (drain the input stack, emit one mark per symbol) and in the slightly
more general form `x ↦ (if keep then 1^|x| else []) ++ c`, so that the SAME machine also
supplies the transducer needed to discharge `Uniform` for the concrete witness family.

Composition is `PvsNP.polyTimeComputable_comp` (cited, proved on the platform); the
`initList`/`haltList` interface facts are `ShiTM.initList_haltList_laws` (also cited).

Note on encodings: `PvsNP.PolyTimeComputable f` is
`Nonempty (TM2ComputableInPolyTime id id f)` while `PvsNP.PolyTimeChecker R` is
`Nonempty (TM2ComputableInPolyTime encodePair encodeBool R)`.  Everything below stays on
the `PolyTimeComputable` side, where `polyTimeComputable_comp` lives; no encoding change
is performed or needed for the statements proved here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Turing Turing.TM2

/-- Stack contents: stack `false` is the input stack, stack `true` the output stack. -/
private def shiStk (a b : List Bool) : Bool → List Bool := fun k => bif k then b else a

/-- Push a fixed list of symbols onto the output stack, then continue with `q`. -/
private def shiPush (d : List Bool) (q : Stmt (fun _ : Bool => Bool) Bool Bool) :
    Stmt (fun _ : Bool => Bool) Bool Bool :=
  d.foldr (fun b r => Stmt.push true (fun _ => b) r) q

/-- The transducer.  Label `true` (the main label) emits the fixed suffix `c` onto the
output stack; label `false` drains the input stack, pushing one `true` per input symbol
when `keep` is set, and halts when the input stack is empty. -/
@[reducible]
private def shiTM (c : List Bool) (keep : Bool) : Turing.FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := fun _ => Bool
  Λ := Bool
  main := true
  σ := Bool
  initialState := false
  m := fun l =>
    bif l then shiPush c.reverse (Stmt.goto (fun _ => false))
    else Stmt.pop false (fun _ o => o.isSome)
      (Stmt.branch (fun v => v)
        (bif keep then Stmt.push true (fun _ => true) (Stmt.goto (fun _ => false))
          else Stmt.goto (fun _ => false))
        Stmt.halt)

private lemma shiCfg (c : List Bool) (keep : Bool) (L : Option Bool) (v : Bool)
    (S T : Bool → List Bool) (h : ∀ k, S k = T k) :
    (⟨L, v, S⟩ : (shiTM c keep).Cfg) = ⟨L, v, T⟩ := by
  have hst : S = T := funext h
  rw [hst]

private lemma shiMk (c : List Bool) (keep : Bool) (C : (shiTM c keep).Cfg)
    (L : Option Bool) (v : Bool) (S : Bool → List Bool)
    (e1 : C.l = L) (e2 : C.var = v) (e3 : C.stk = S) :
    C = ⟨L, v, S⟩ := by
  obtain ⟨l, vv, T⟩ := C
  have f1 : l = L := e1
  have f2 : vv = v := e2
  have f3 : T = S := e3
  subst f1
  subst f2
  subst f3
  rfl

private lemma shiK0 (c : List Bool) (keep : Bool) :
    (true : (shiTM c keep).K) ≠ (shiTM c keep).k₀ := by
  intro hh
  exact Bool.noConfusion hh

private lemma shiK1 (c : List Bool) (keep : Bool) :
    (false : (shiTM c keep).K) ≠ (shiTM c keep).k₁ := by
  intro hh
  exact Bool.noConfusion hh

private lemma shiPushRun (d : List Bool) (q : Stmt (fun _ : Bool => Bool) Bool Bool)
    (v : Bool) (a : List Bool) :
    ∀ b : List Bool, stepAux (shiPush d q) v (shiStk a b)
      = stepAux q v (shiStk a (d.reverse ++ b)) := by
  induction d with
  | nil => intro b; simp [shiPush]
  | cons e es ih =>
      intro b
      have h1 : stepAux (shiPush (e :: es) q) v (shiStk a b)
          = stepAux (shiPush es q) v (Function.update (shiStk a b) true (e :: b)) := rfl
      have h2 : Function.update (shiStk a b) true (e :: b) = shiStk a (e :: b) := by
        funext k
        cases k <;> rfl
      rw [h1, h2, ih]
      simp

private lemma shiStepEmit (c : List Bool) (keep : Bool) (v : Bool) (a b : List Bool) :
    (shiTM c keep).step ⟨some true, v, shiStk a b⟩
      = some (⟨some false, v, shiStk a (c ++ b)⟩ : (shiTM c keep).Cfg) := by
  have h2 : stepAux (shiPush c.reverse (Stmt.goto (fun _ => false))) v (shiStk a b)
      = stepAux (Stmt.goto (fun _ => false)) v (shiStk a (c.reverse.reverse ++ b)) :=
    shiPushRun c.reverse _ v a b
  rw [List.reverse_reverse] at h2
  exact congrArg Option.some h2

private lemma shiStepCons (c : List Bool) (keep b : Bool) (t acc : List Bool) (v : Bool) :
    (shiTM c keep).step ⟨some false, v, shiStk (b :: t) acc⟩
      = some (⟨some false, true,
          shiStk t (bif keep then true :: acc else acc)⟩ : (shiTM c keep).Cfg) := by
  cases keep
  · refine congrArg Option.some (shiCfg _ _ _ _ _ _ ?_)
    intro k
    cases k <;> rfl
  · refine congrArg Option.some (shiCfg _ _ _ _ _ _ ?_)
    intro k
    cases k <;> rfl

private lemma shiStepNil (c : List Bool) (keep : Bool) (acc : List Bool) (v : Bool) :
    (shiTM c keep).step ⟨some false, v, shiStk [] acc⟩
      = some (⟨none, false, shiStk [] acc⟩ : (shiTM c keep).Cfg) := by
  cases keep
  · refine congrArg Option.some (shiCfg _ _ _ _ _ _ ?_)
    intro k
    cases k <;> rfl
  · refine congrArg Option.some (shiCfg _ _ _ _ _ _ ?_)
    intro k
    cases k <;> rfl

private lemma shiRun (c : List Bool) (keep : Bool) :
    ∀ (l acc : List Bool) (v : Bool),
      (fun cf : Option ((shiTM c keep).Cfg) => Option.bind cf (shiTM c keep).step)^[l.length + 1]
          (some (⟨some false, v, shiStk l acc⟩ : (shiTM c keep).Cfg))
        = some (⟨none, false,
            shiStk [] ((bif keep then List.replicate l.length true else []) ++ acc)⟩ :
              (shiTM c keep).Cfg) := by
  intro l
  induction l with
  | nil =>
      intro acc v
      cases keep
      · exact shiStepNil c false acc v
      · exact shiStepNil c true acc v
  | cons b t ih =>
      intro acc v
      have hE : (fun cf : Option ((shiTM c keep).Cfg) => Option.bind cf (shiTM c keep).step)
          (some (⟨some false, v, shiStk (b :: t) acc⟩ : (shiTM c keep).Cfg))
          = some (⟨some false, true,
              shiStk t (bif keep then true :: acc else acc)⟩ : (shiTM c keep).Cfg) :=
        shiStepCons c keep b t acc v
      have hstep : ∀ y z : Option ((shiTM c keep).Cfg), y = z →
          (fun cf : Option ((shiTM c keep).Cfg) =>
            Option.bind cf (shiTM c keep).step)^[t.length + 1] y
          = (fun cf : Option ((shiTM c keep).Cfg) =>
            Option.bind cf (shiTM c keep).step)^[t.length + 1] z := by
        intro y z h
        rw [h]
      have hlist : (bif keep then List.replicate t.length true else [])
            ++ (bif keep then true :: acc else acc)
          = (bif keep then List.replicate (b :: t).length true else []) ++ acc := by
        cases keep
        · rfl
        · show List.replicate t.length true ++ (true :: acc)
              = List.replicate (t.length + 1) true ++ acc
          rw [List.replicate_add, List.append_assoc]
          rfl
      exact Eq.trans (hstep _ _ hE)
        (Eq.trans (ih (bif keep then true :: acc else acc) true)
          (congrArg (fun L => some (⟨none, false, shiStk [] L⟩ : (shiTM c keep).Cfg)) hlist))

private lemma shiInit (c : List Bool) (keep : Bool) (x : List Bool) :
    Turing.initList (shiTM c keep) x
      = (⟨some true, false, shiStk x []⟩ : (shiTM c keep).Cfg) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := ShiTM.initList_haltList_laws (shiTM c keep) x []
  have h5 : (Turing.initList (shiTM c keep) x).stk = shiStk x [] := by
    funext k
    cases k
    · exact h3
    · exact h4 true (shiK0 c keep)
  exact shiMk c keep _ _ _ _ h1 h2 h5

private lemma shiHalt (c : List Bool) (keep : Bool) (o : List Bool) :
    Turing.haltList (shiTM c keep) o
      = (⟨none, false, shiStk [] o⟩ : (shiTM c keep).Cfg) := by
  obtain ⟨-, -, -, -, h5, h6, h7, h8⟩ := ShiTM.initList_haltList_laws (shiTM c keep) [] o
  have h9 : (Turing.haltList (shiTM c keep) o).stk = shiStk [] o := by
    funext k
    cases k
    · exact h8 false (shiK1 c keep)
    · exact h7
  exact shiMk c keep _ _ _ _ h5 h6 h9

private lemma shiOutputs (c : List Bool) (keep : Bool) (x : List Bool) :
    Nonempty (Turing.TM2OutputsInTime (shiTM c keep) x
      (some ((bif keep then List.replicate x.length true else []) ++ c))
      (x.length + 2)) := by
  have hE : (fun cf : Option ((shiTM c keep).Cfg) => Option.bind cf (shiTM c keep).step)
      (some (⟨some true, false, shiStk x []⟩ : (shiTM c keep).Cfg))
      = some (⟨some false, false, shiStk x c⟩ : (shiTM c keep).Cfg) := by
    have h := shiStepEmit c keep false x []
    rw [List.append_nil] at h
    exact h
  have hstep : ∀ y z : Option ((shiTM c keep).Cfg), y = z →
      (fun cf : Option ((shiTM c keep).Cfg) =>
        Option.bind cf (shiTM c keep).step)^[x.length + 1] y
      = (fun cf : Option ((shiTM c keep).Cfg) =>
        Option.bind cf (shiTM c keep).step)^[x.length + 1] z := by
    intro y z h
    rw [h]
  have hrun := shiRun c keep x c false
  refine ⟨⟨⟨x.length + 2, ?_⟩, le_refl _⟩⟩
  show (fun cf : Option ((shiTM c keep).Cfg) =>
      Option.bind cf (shiTM c keep).step)^[x.length + 1 + 1]
      (some (Turing.initList (shiTM c keep) x))
    = some (Turing.haltList (shiTM c keep)
        ((bif keep then List.replicate x.length true else []) ++ c))
  rw [shiInit, shiHalt]
  exact Eq.trans (hstep _ _ hE) hrun

private lemma shiPTC (c : List Bool) (keep : Bool) :
    PvsNP.PolyTimeComputable
      (fun x : PvsNP.Str => (bif keep then List.replicate x.length true else []) ++ c) := by
  have key : ∀ a : PvsNP.Str,
      Nonempty (Turing.TM2OutputsInTime (shiTM c keep)
        (List.map (Equiv.refl Bool).invFun a)
        (some (List.map (Equiv.refl Bool).invFun
          ((bif keep then List.replicate a.length true else []) ++ c)))
        ((Polynomial.X + Polynomial.C 2 : Polynomial ℕ).eval a.length)) := by
    intro a
    have hm : ∀ y : List Bool, List.map (Equiv.refl Bool).invFun y = y :=
      fun y => List.map_id y
    have hp : ((Polynomial.X + Polynomial.C 2 : Polynomial ℕ)).eval a.length
        = a.length + 2 := by simp
    rw [hm, hm, hp]
    exact shiOutputs c keep a
  exact ⟨{ tm := shiTM c keep
           inputAlphabet := Equiv.refl Bool
           outputAlphabet := Equiv.refl Bool
           time := Polynomial.X + Polynomial.C 2
           outputsFun := fun a => (key a).some }⟩

private lemma shiUnaryPTC :
    PvsNP.PolyTimeComputable (fun x : PvsNP.Str => ShiBQP.unary x.length) := by
  simpa [ShiBQP.unary] using shiPTC [] true

private lemma shiTailPTC :
    PvsNP.PolyTimeComputable
      (fun x : PvsNP.Str => ShiBQP.unary x.length ++ [false, false, false]) := by
  simpa [ShiBQP.unary] using shiPTC [false, false, false] true

/-- **READ-1.**  Five unconditional conjuncts.

1. The bridge: for every family `F` with `ShiBQP.Uniform F` there is a polynomial-time
   computable `g : Str → Str` with `g x = ShiBQP.encFamilyAt F x.length` for EVERY input
   `x`, so a classical checker deciding an input of length `n` can read the circuit's
   description.  Built as `f ∘ (fun x => unary x.length)` via the platform theorem
   `PvsNP.polyTimeComputable_comp`.

2. The transducer `x ↦ 1^|x|` is itself polynomial-time computable (it did not exist in
   the development and is constructed here as an explicit `Turing.FinTM2`).

3. NON-VACUITY: a concrete family `F` -- `anc n = n`, empty circuit, output wire `0` --
   with `Uniform F` discharged explicitly, together with the resulting `g`, evaluated at
   two LITERAL inputs of DIFFERENT lengths, `[]` and `[true, false, true]`, and matched
   against `encFamilyAt F 0` and `encFamilyAt F 3`.  The two values differ, so the
   length dependence of `g` is genuinely exercised.

4/5. The unary transducer itself at the same two literal inputs. -/
theorem _root_.BQPReferenceValidation.candidate22 :
    (∀ F : ShiClass.Family, ShiBQP.Uniform F →
        ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
          ∀ x : PvsNP.Str, g x = ShiBQP.encFamilyAt F x.length)
      ∧ PvsNP.PolyTimeComputable (fun x : PvsNP.Str => ShiBQP.unary x.length)
      ∧ (∃ F : ShiClass.Family, ∃ g : PvsNP.Str → PvsNP.Str,
          ShiBQP.Uniform F ∧ PvsNP.PolyTimeComputable g ∧
          (∀ x : PvsNP.Str, g x = ShiBQP.encFamilyAt F x.length) ∧
          g [] = [false, false, false] ∧
          g [true, false, true] = [true, true, true, false, false, false] ∧
          ShiBQP.encFamilyAt F 0 = [false, false, false] ∧
          ShiBQP.encFamilyAt F 3 = [true, true, true, false, false, false])
      ∧ ShiBQP.unary ([] : PvsNP.Str).length = []
      ∧ ShiBQP.unary ([true, false, true] : PvsNP.Str).length = [true, true, true] := by
  refine ⟨?_, shiUnaryPTC, ?_, rfl, rfl⟩
  · intro F hF
    obtain ⟨f, hfp, hfe⟩ := hF
    refine ⟨f ∘ (fun x : PvsNP.Str => ShiBQP.unary x.length), ?_, ?_⟩
    · exact PvsNP.polyTimeComputable_comp _ _ shiUnaryPTC hfp
    · intro x
      exact hfe x.length
  · refine ⟨ShiClass.Family.mk (fun n => n) (fun _ => []) (fun n => ⟨0, by omega⟩),
      fun x : PvsNP.Str => ShiBQP.unary x.length ++ [false, false, false], ?_,
      shiTailPTC, ?_, rfl, rfl, rfl, rfl⟩
    · refine ⟨fun x : PvsNP.Str => ShiBQP.unary x.length ++ [false, false, false],
        shiTailPTC, ?_⟩
      intro n
      simp [ShiBQP.unary, ShiBQP.encFamilyAt, ShiBQP.encNat, ShiBQP.encCirc, ShiBQP.encStr]
    · intro x
      simp [ShiBQP.unary, ShiBQP.encFamilyAt, ShiBQP.encNat, ShiBQP.encCirc, ShiBQP.encStr]

end BQPReferenceValidation.Source22

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate22
    let target ← getConstInfo ``ShiBQP.uniform_family_encoding_is_polynomial_time_computable_from_the_input
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.uniform_family_encoding_is_polynomial_time_computable_from_the_input"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.uniform_family_encoding_is_polynomial_time_computable_from_the_input"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.uniform_family_encoding_is_polynomial_time_computable_from_the_input"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate22
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.uniform_family_encoding_is_polynomial_time_computable_from_the_input; axioms {axioms}"
