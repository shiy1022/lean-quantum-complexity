import Definitions.Def_PvsNP
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_PvsNP_polyTimeComputable_comp
import Theorems.Thm_PvsNP_polyTime_composition_and_alphabet_transport
import Theorems.Thm_ShiTM_comp_outputsInTime

namespace BQPReferenceValidation.Source2
/-
BRIDGE-C.  A usable polynomial-time COMPOSITION principle for
`Turing.TM2ComputableInPolyTime` at ARBITRARY, DIFFERENT alphabets, plus the two
alphabet-TRANSPORT principles that come for free, and the specialisations that let a
`PvsNP.PolyTimeChecker` (input alphabet `Bool ⊕ Bool`) and a `PvsNP.PolyTimeComputable` /
`PvsNP.PolyTimeDecider` (input alphabet `Bool`) be chained.

Mathlib's `Turing.TM2ComputableInPolyTime.comp`
(`Mathlib/Computability/TuringMachine/Computable.lean:284`, revision
`0df444a360eaa60ab8c11dca51a86af692955474`) is a `proof_wanted` STUB and is NOT used here.
The composite machine is `ShiTM2.comp` and the run is the PROVED platform theorem
`ShiTM.comp_outputsInTime`; the plain-string composition is the PROVED platform theorem
`PvsNP.polyTimeComputable_comp`.

Three things are worth stating plainly.

* Composition needs ONE extra hypothesis that Mathlib's `proof_wanted` does not carry: a
  polynomial `q` bounding the length of the INTERMEDIATE encoding, `|eβ (f a)| ≤ q(|eα a|)`.
  It is not removable for free here: a single `Turing.TM2.Stmt` is a finite tree of pushes, so
  one step can lengthen the output stack by more than one symbol, and bounding the blow-up by a
  constant needs a separate argument about the (finite) program.  Every consumer knows its own
  output-length bound, so carrying `q` costs nothing downstream and it makes the resulting time
  polynomial EXPLICIT: `c₁.time + (2 * q + 2) + c₂.time.comp q`.

* The two transport laws are free, because `TM2ComputableInPolyTime` mentions the encoding
  ONLY through `List.map inputAlphabet.invFun ∘ ea` and `List.map outputAlphabet.invFun ∘ eb`.
  Relabelling the alphabet along an `Equiv` and reindexing the domain/codomain therefore needs
  no machine at all: the SAME machine, with the alphabet equivalence composed with the
  relabelling, certifies the transported function with the SAME time polynomial.  Complementing
  a checker's output is the instance at the `Bool ≃ Bool` negation.

* The alphabet mismatch `Bool ⊕ Bool` vs `Bool` CANNOT be dissolved by transport, because
  transport needs a BIJECTION of alphabets and `Bool ⊕ Bool` has four elements while `Bool` has
  two.  It is dissolved by composition instead: `ShiTM2.comp` takes an arbitrary symbol
  translation `tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀`, so a machine READING the tagged alphabet and
  WRITING the plain one may be followed by any plain-string machine.  Part (7) below is that
  bridge, conditional on one such tagged-to-plain transducer; parts (4) and (5) are the
  plain-string half, and (5) is UNCONDITIONAL (no length hypothesis) because
  `PvsNP.PolyTimeDecider χ` is literally `PvsNP.PolyTimeComputable (fun w => [χ w])`.

HONEST LIMITATIONS.
1. No closure of `PolyTimeChecker` under Boolean AND/OR of two checkers is obtained.  That
   needs the input to be consumed twice, which sequential composition does not provide.
2. Part (7) is conditional: no tagged-to-plain transducer is constructed here.
3. The length hypothesis is not discharged; see above.
4. Nothing quantum appears anywhere in this file, and no containment such as `BQP ⊆ PP` is
   proved or approached beyond supplying this composition interface.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Turing

/-! ### Small arithmetic and `Equiv` helpers -/

private lemma evalMono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

/-- Boolean negation as an equivalence `Bool ≃ Bool`. -/
private def negEquiv : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro b; cases b <;> rfl

/-- Symbolwise negation on the tagged alphabet `Bool ⊕ Bool`. -/
private def flipEquiv : (Bool ⊕ Bool) ≃ (Bool ⊕ Bool) where
  toFun := Sum.map not not
  invFun := Sum.map not not
  left_inv := by
    intro s
    cases s with
    | inl b => cases b <;> rfl
    | inr b => cases b <;> rfl
  right_inv := by
    intro s
    cases s with
    | inl b => cases b <;> rfl
    | inr b => cases b <;> rfl

/-! ### 1.  The general composition, with an explicit time polynomial -/

private lemma compPolyCert {α β γ αΓ βΓ γΓ : Type}
    {eα : α → List αΓ} {eβ : β → List βΓ} {eγ : γ → List γΓ}
    {f : α → β} {g : β → γ} (q : Polynomial ℕ) (z : βΓ)
    (c₁ : Turing.TM2ComputableInPolyTime eα eβ f)
    (c₂ : Turing.TM2ComputableInPolyTime eβ eγ g)
    (hq : ∀ a : α, (eβ (f a)).length ≤ q.eval (eα a).length) :
    ∃ c : Turing.TM2ComputableInPolyTime eα eγ (g ∘ f),
      c.time = c₁.time + (Polynomial.C 2 * q + Polynomial.C 2) + c₂.time.comp q := by
  classical
  refine ⟨{ tm := ShiTM2.comp c₁.tm c₂.tm
                    (fun s => c₂.inputAlphabet.invFun (c₁.outputAlphabet s))
                    (c₂.inputAlphabet.invFun z)
            inputAlphabet := c₁.inputAlphabet
            outputAlphabet := c₂.outputAlphabet
            time := c₁.time + (Polynomial.C 2 * q + Polynomial.C 2) + c₂.time.comp q
            outputsFun := ?_ }, rfl⟩
  intro a
  have hfun : ((fun s => c₂.inputAlphabet.invFun (c₁.outputAlphabet s))
      ∘ c₁.outputAlphabet.invFun) = c₂.inputAlphabet.invFun := by
    funext b
    show c₂.inputAlphabet.invFun (c₁.outputAlphabet (c₁.outputAlphabet.invFun b))
      = c₂.inputAlphabet.invFun b
    exact congrArg c₂.inputAlphabet.invFun (c₁.outputAlphabet.right_inv b)
  have hmap : List.map (fun s => c₂.inputAlphabet.invFun (c₁.outputAlphabet s))
        (List.map c₁.outputAlphabet.invFun (eβ (f a)))
      = List.map c₂.inputAlphabet.invFun (eβ (f a)) := by
    rw [List.map_map, hfun]
  have h₁ : Turing.TM2OutputsInTime c₁.tm (List.map c₁.inputAlphabet.invFun (eα a))
      (Option.some (List.map c₁.outputAlphabet.invFun (eβ (f a))))
      (c₁.time.eval (eα a).length) := c₁.outputsFun a
  have h₂ : Turing.TM2OutputsInTime c₂.tm
      (List.map (fun s => c₂.inputAlphabet.invFun (c₁.outputAlphabet s))
        (List.map c₁.outputAlphabet.invFun (eβ (f a))))
      (Option.some (List.map c₂.outputAlphabet.invFun (eγ (g (f a)))))
      (c₂.time.eval (eβ (f a)).length) := by
    rw [hmap]
    exact c₂.outputsFun (f a)
  have hcomp := ShiTM.comp_outputsInTime (inst := ShiTM2.compKDecEq c₁.tm c₂.tm)
    c₁.tm c₂.tm (fun s => c₂.inputAlphabet.invFun (c₁.outputAlphabet s))
    (c₂.inputAlphabet.invFun z)
    (List.map c₁.inputAlphabet.invFun (eα a))
    (List.map c₁.outputAlphabet.invFun (eβ (f a)))
    (List.map c₂.outputAlphabet.invFun (eγ (g (f a))))
    (c₁.time.eval (eα a).length) (c₂.time.eval (eβ (f a)).length) h₁ h₂
  have hbound : c₁.time.eval (eα a).length
        + (2 * (List.map c₁.outputAlphabet.invFun (eβ (f a))).length + 2)
        + c₂.time.eval (eβ (f a)).length
      ≤ (c₁.time + (Polynomial.C 2 * q + Polynomial.C 2)
          + c₂.time.comp q).eval (eα a).length := by
    rw [List.length_map]
    have hb1 : (eβ (f a)).length ≤ q.eval (eα a).length := hq a
    have hb2 : c₂.time.eval (eβ (f a)).length ≤ c₂.time.eval (q.eval (eα a).length) :=
      evalMono c₂.time (hq a)
    have hev : (c₁.time + (Polynomial.C 2 * q + Polynomial.C 2)
          + c₂.time.comp q).eval (eα a).length
        = c₁.time.eval (eα a).length + (2 * q.eval (eα a).length + 2)
          + c₂.time.eval (q.eval (eα a).length) := by
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_comp]
    rw [hev]
    omega
  have e := hcomp.some
  exact ⟨e.toEvalsTo, le_trans e.steps_le_m hbound⟩

/-! ### 2.  Input-side transport along an alphabet bijection -/

private lemma transIn {α α' β αΓ αΓ' βΓ : Type} {ea : α → List αΓ} {ea' : α' → List αΓ'}
    {eb : β → List βΓ} (u : α' → α) (e : αΓ ≃ αΓ') {f : α → β}
    (he : ∀ a' : α', ea' a' = List.map e (ea (u a')))
    (c : Turing.TM2ComputableInPolyTime ea eb f) :
    Nonempty (Turing.TM2ComputableInPolyTime ea' eb (f ∘ u)) := by
  refine ⟨{ tm := c.tm
            inputAlphabet := c.inputAlphabet.trans e
            outputAlphabet := c.outputAlphabet
            time := c.time
            outputsFun := ?_ }⟩
  intro a'
  show Turing.TM2OutputsInTime c.tm
      (List.map (c.inputAlphabet.trans e).invFun (ea' a'))
      (Option.some (List.map c.outputAlphabet.invFun (eb (f (u a')))))
      (c.time.eval (ea' a').length)
  have hfun : ((c.inputAlphabet.trans e).invFun ∘ (e : αΓ → αΓ'))
      = c.inputAlphabet.invFun := by
    funext x
    show c.inputAlphabet.invFun (e.invFun (e x)) = c.inputAlphabet.invFun x
    exact congrArg c.inputAlphabet.invFun (e.left_inv x)
  have hin : List.map (c.inputAlphabet.trans e).invFun (ea' a')
      = List.map c.inputAlphabet.invFun (ea (u a')) := by
    rw [he a', List.map_map, hfun]
  have hlen : (ea' a').length = (ea (u a')).length := by
    rw [he a', List.length_map]
  rw [hin, hlen]
  exact c.outputsFun (u a')

/-! ### 3.  Output-side transport along an alphabet bijection -/

private lemma transOut {α β β' αΓ βΓ βΓ' : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {eb' : β' → List βΓ'} (v : β → β') (d : βΓ ≃ βΓ') {f : α → β}
    (hd : ∀ b : β, eb' (v b) = List.map d (eb b))
    (c : Turing.TM2ComputableInPolyTime ea eb f) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb' (v ∘ f)) := by
  refine ⟨{ tm := c.tm
            inputAlphabet := c.inputAlphabet
            outputAlphabet := c.outputAlphabet.trans d
            time := c.time
            outputsFun := ?_ }⟩
  intro a
  show Turing.TM2OutputsInTime c.tm (List.map c.inputAlphabet.invFun (ea a))
      (Option.some (List.map (c.outputAlphabet.trans d).invFun (eb' (v (f a)))))
      (c.time.eval (ea a).length)
  have hfun : ((c.outputAlphabet.trans d).invFun ∘ (d : βΓ → βΓ'))
      = c.outputAlphabet.invFun := by
    funext x
    show c.outputAlphabet.invFun (d.invFun (d x)) = c.outputAlphabet.invFun x
    exact congrArg c.outputAlphabet.invFun (d.left_inv x)
  have hout : List.map (c.outputAlphabet.trans d).invFun (eb' (v (f a)))
      = List.map c.outputAlphabet.invFun (eb (f a)) := by
    rw [hd (f a), List.map_map, hfun]
  rw [hout]
  exact c.outputsFun a

/-! ### 4.  A decider IS a string function whose value is a one-bit string -/

private lemma decIffComputable (χ : PvsNP.Str → Bool) :
    PvsNP.PolyTimeDecider χ ↔ PvsNP.PolyTimeComputable (fun w : PvsNP.Str => [χ w]) := by
  constructor
  · rintro ⟨c⟩
    exact ⟨{ tm := c.tm
             inputAlphabet := c.inputAlphabet
             outputAlphabet := c.outputAlphabet
             time := c.time
             outputsFun := c.outputsFun }⟩
  · rintro ⟨c⟩
    exact ⟨{ tm := c.tm
             inputAlphabet := c.inputAlphabet
             outputAlphabet := c.outputAlphabet
             time := c.time
             outputsFun := c.outputsFun }⟩

private lemma deciderComp (χ : PvsNP.Str → Bool) (g : PvsNP.Str → PvsNP.Str)
    (hχ : PvsNP.PolyTimeDecider χ) (hg : PvsNP.PolyTimeComputable g) :
    PvsNP.PolyTimeDecider (fun w : PvsNP.Str => χ (g w)) := by
  have h1 : PvsNP.PolyTimeComputable (fun w : PvsNP.Str => [χ w]) :=
    (decIffComputable χ).1 hχ
  have h2 : PvsNP.PolyTimeComputable ((fun w : PvsNP.Str => [χ w]) ∘ g) :=
    PvsNP.polyTimeComputable_comp g (fun w : PvsNP.Str => [χ w]) hg h1
  exact (decIffComputable (fun w : PvsNP.Str => χ (g w))).2 h2

/-! ### 5.  The tagged-alphabet specialisations -/

private lemma checkerPre (R : PvsNP.Str × PvsNP.Str → Bool)
    (T : PvsNP.Str × PvsNP.Str → PvsNP.Str × PvsNP.Str) (q : Polynomial ℕ)
    (c₁ : Turing.TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair T)
    (c₂ : Turing.TM2ComputableInPolyTime PvsNP.encodePair Computability.encodeBool R)
    (hq : ∀ p : PvsNP.Str × PvsNP.Str,
      (PvsNP.encodePair (T p)).length ≤ q.eval (PvsNP.encodePair p).length) :
    ∃ c : Turing.TM2ComputableInPolyTime PvsNP.encodePair Computability.encodeBool
        (fun p : PvsNP.Str × PvsNP.Str => R (T p)),
      c.time = c₁.time + (Polynomial.C 2 * q + Polynomial.C 2) + c₂.time.comp q := by
  obtain ⟨c, hc⟩ := compPolyCert q (Sum.inl false) c₁ c₂ hq
  exact ⟨c, hc⟩

private lemma untagBridge (u : PvsNP.Str × PvsNP.Str → PvsNP.Str) (χ : PvsNP.Str → Bool)
    (q : Polynomial ℕ)
    (hu : Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair
      (id : PvsNP.Str → PvsNP.Str) u))
    (hχ : PvsNP.PolyTimeDecider χ)
    (hq : ∀ p : PvsNP.Str × PvsNP.Str,
      (u p).length ≤ q.eval (PvsNP.encodePair p).length) :
    PvsNP.PolyTimeChecker (fun p : PvsNP.Str × PvsNP.Str => χ (u p)) := by
  obtain ⟨c₁⟩ := hu
  obtain ⟨c₂⟩ := hχ
  obtain ⟨c, -⟩ := compPolyCert q false c₁ c₂ hq
  exact ⟨c⟩

private lemma checkerNeg (R : PvsNP.Str × PvsNP.Str → Bool)
    (h : PvsNP.PolyTimeChecker R) :
    PvsNP.PolyTimeChecker (fun p : PvsNP.Str × PvsNP.Str => !(R p)) := by
  obtain ⟨c⟩ := h
  refine transOut (eb' := Computability.encodeBool) not negEquiv ?_ c
  intro b
  cases b <;> rfl

private lemma flipPair0 (p : PvsNP.Str × PvsNP.Str) :
    PvsNP.encodePair (p.1.map not, p.2.map not)
      = List.map flipEquiv (PvsNP.encodePair p) := by
  obtain ⟨x, y⟩ := p
  show (x.map not).map Sum.inl ++ (y.map not).map Sum.inr
    = List.map (Sum.map not not) (x.map Sum.inl ++ y.map Sum.inr)
  simp only [List.map_append, List.map_map]
  rfl

private lemma flipInv (l : List (Bool ⊕ Bool)) :
    List.map flipEquiv (List.map flipEquiv l) = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.map_cons, List.map_cons, ih]
      exact congrArg (fun s => s :: t) (flipEquiv.left_inv a)

private lemma flipPair (p : PvsNP.Str × PvsNP.Str) :
    PvsNP.encodePair p
      = List.map flipEquiv (PvsNP.encodePair (p.1.map not, p.2.map not)) := by
  rw [flipPair0 p, flipInv]

private lemma checkerFlipIn (R : PvsNP.Str × PvsNP.Str → Bool)
    (h : PvsNP.PolyTimeChecker R) :
    PvsNP.PolyTimeChecker
      (fun p : PvsNP.Str × PvsNP.Str => R (p.1.map not, p.2.map not)) := by
  obtain ⟨c⟩ := h
  exact transIn (ea' := PvsNP.encodePair)
    (fun p : PvsNP.Str × PvsNP.Str => (p.1.map not, p.2.map not)) flipEquiv flipPair c

/-! ### 6.  Non-vacuity: a genuine two-machine composite -/

private lemma idTime {α αΓ : Type} [Fintype αΓ] (ea : α → List αΓ) :
    (Turing.idComputableInPolyTime ea).time = 1 := rfl

private lemma idIdComp :
    ∃ c : Turing.TM2ComputableInPolyTime Computability.encodeBool Computability.encodeBool
        ((id : Bool → Bool) ∘ (id : Bool → Bool)),
      c.time.eval 1 = 6 ∧ c.time.eval 2 = 8 := by
  obtain ⟨c, hc⟩ := compPolyCert (α := Bool) (β := Bool) (γ := Bool)
    Polynomial.X false (Turing.idComputableInPolyTime Computability.encodeBool)
    (Turing.idComputableInPolyTime Computability.encodeBool)
    (fun a => by simp)
  refine ⟨c, ?_, ?_⟩
  · rw [hc]; simp [idTime, Polynomial.eval_comp]
  · rw [hc]; simp [idTime, Polynomial.eval_comp]

theorem _root_.BQPReferenceValidation.candidate2 :
    -- (1) GENERAL POLYNOMIAL-TIME COMPOSITION, arbitrary and DIFFERENT alphabets on all three
    -- sides, with the composite's time polynomial exhibited.  `q` bounds the length of the
    -- intermediate encoding; `z` supplies the dummy symbol `ShiTM2.comp` demands.
    (∀ (α β γ αΓ βΓ γΓ : Type) (eα : α → List αΓ) (eβ : β → List βΓ) (eγ : γ → List γΓ)
        (f : α → β) (g : β → γ) (q : Polynomial ℕ) (z : βΓ)
        (c₁ : Turing.TM2ComputableInPolyTime eα eβ f)
        (c₂ : Turing.TM2ComputableInPolyTime eβ eγ g),
        (∀ a : α, (eβ (f a)).length ≤ q.eval (eα a).length) →
        ∃ c : Turing.TM2ComputableInPolyTime eα eγ (g ∘ f),
          c.time = c₁.time + (Polynomial.C 2 * q + Polynomial.C 2) + c₂.time.comp q)
  ∧ -- (2) INPUT TRANSPORT.  Relabelling the input alphabet along a bijection and reindexing
    -- the domain is free: same machine, same time polynomial.
    (∀ (α α' β αΓ αΓ' βΓ : Type) (ea : α → List αΓ) (ea' : α' → List αΓ')
        (eb : β → List βΓ) (u : α' → α) (e : αΓ ≃ αΓ') (f : α → β),
        (∀ a' : α', ea' a' = List.map e (ea (u a'))) →
        Turing.TM2ComputableInPolyTime ea eb f →
        Nonempty (Turing.TM2ComputableInPolyTime ea' eb (f ∘ u)))
  ∧ -- (3) OUTPUT TRANSPORT, likewise free.
    (∀ (α β β' αΓ βΓ βΓ' : Type) (ea : α → List αΓ) (eb : β → List βΓ)
        (eb' : β' → List βΓ') (v : β → β') (d : βΓ ≃ βΓ') (f : α → β),
        (∀ b : β, eb' (v b) = List.map d (eb b)) →
        Turing.TM2ComputableInPolyTime ea eb f →
        Nonempty (Turing.TM2ComputableInPolyTime ea eb' (v ∘ f)))
  ∧ -- (4) A DECIDER IS A STRING FUNCTION: the two `Prop`s are equivalent.
    (∀ χ : PvsNP.Str → Bool,
        PvsNP.PolyTimeDecider χ ↔ PvsNP.PolyTimeComputable (fun w : PvsNP.Str => [χ w]))
  ∧ -- (5) UNCONDITIONAL plain-string chaining: no length hypothesis is needed, because this
    -- routes through the proved `PvsNP.polyTimeComputable_comp`.
    (∀ (χ : PvsNP.Str → Bool) (g : PvsNP.Str → PvsNP.Str),
        PvsNP.PolyTimeDecider χ → PvsNP.PolyTimeComputable g →
        PvsNP.PolyTimeDecider (fun w : PvsNP.Str => χ (g w)))
  ∧ -- (6) CHECKER PREPROCESSING: any poly-time transducer on the TAGGED alphabet may be
    -- prepended to any checker, with the composite's time polynomial exhibited.
    (∀ (R : PvsNP.Str × PvsNP.Str → Bool)
        (T : PvsNP.Str × PvsNP.Str → PvsNP.Str × PvsNP.Str) (q : Polynomial ℕ)
        (c₁ : Turing.TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair T)
        (c₂ : Turing.TM2ComputableInPolyTime PvsNP.encodePair Computability.encodeBool R),
        (∀ p : PvsNP.Str × PvsNP.Str,
          (PvsNP.encodePair (T p)).length ≤ q.eval (PvsNP.encodePair p).length) →
        ∃ c : Turing.TM2ComputableInPolyTime PvsNP.encodePair Computability.encodeBool
            (fun p : PvsNP.Str × PvsNP.Str => R (T p)),
          c.time = c₁.time + (Polynomial.C 2 * q + Polynomial.C 2) + c₂.time.comp q)
  ∧ -- (7) THE ALPHABET BRIDGE: one tagged-to-plain transducer turns EVERY plain-string
    -- polynomial-time decision procedure into a polynomial-time checking relation.
    (∀ (u : PvsNP.Str × PvsNP.Str → PvsNP.Str) (χ : PvsNP.Str → Bool) (q : Polynomial ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair
          (id : PvsNP.Str → PvsNP.Str) u) →
        PvsNP.PolyTimeDecider χ →
        (∀ p : PvsNP.Str × PvsNP.Str,
          (u p).length ≤ q.eval (PvsNP.encodePair p).length) →
        PvsNP.PolyTimeChecker (fun p : PvsNP.Str × PvsNP.Str => χ (u p)))
  ∧ -- (8) COMPLEMENT CLOSURE of `PolyTimeChecker`, the instance of (3) at Boolean negation.
    (∀ R : PvsNP.Str × PvsNP.Str → Bool,
        PvsNP.PolyTimeChecker R →
        PvsNP.PolyTimeChecker (fun p : PvsNP.Str × PvsNP.Str => !(R p)))
  ∧ -- (9) SYMBOLWISE INPUT NEGATION closure, the instance of (2) at `Sum.map not not`.
    (∀ R : PvsNP.Str × PvsNP.Str → Bool,
        PvsNP.PolyTimeChecker R →
        PvsNP.PolyTimeChecker
          (fun p : PvsNP.Str × PvsNP.Str => R (p.1.map not, p.2.map not)))
  ∧ -- (10) NON-VACUITY: (1) applied to two identity machines really does produce a composite,
    -- and its time polynomial evaluates as the formula predicts.
    (∃ c : Turing.TM2ComputableInPolyTime Computability.encodeBool Computability.encodeBool
        ((id : Bool → Bool) ∘ (id : Bool → Bool)),
      c.time.eval 1 = 6 ∧ c.time.eval 2 = 8)
  ∧ PvsNP.PolyTimeComputable (id : PvsNP.Str → PvsNP.Str)
  ∧ Nonempty (Turing.TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair
      (id : PvsNP.Str × PvsNP.Str → PvsNP.Str × PvsNP.Str)) := by
  refine ⟨?_, ?_, ?_, decIffComputable, deciderComp, checkerPre, untagBridge, checkerNeg,
    checkerFlipIn, idIdComp, ⟨Turing.idComputableInPolyTime (id : PvsNP.Str → PvsNP.Str)⟩,
    ⟨Turing.idComputableInPolyTime PvsNP.encodePair⟩⟩
  · intro α β γ αΓ βΓ γΓ eα eβ eγ f g q z c₁ c₂ hq
    exact compPolyCert q z c₁ c₂ hq
  · intro α α' β αΓ αΓ' βΓ ea ea' eb u e f he c
    exact transIn u e he c
  · intro α β β' αΓ βΓ βΓ' ea eb eb' v d f hd c
    exact transOut v d hd c

end BQPReferenceValidation.Source2

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate2
    let target ← getConstInfo ``PvsNP.polyTime_composition_and_alphabet_transport
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: PvsNP.polyTime_composition_and_alphabet_transport"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: PvsNP.polyTime_composition_and_alphabet_transport"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: PvsNP.polyTime_composition_and_alphabet_transport"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate2
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED PvsNP.polyTime_composition_and_alphabet_transport; axioms {axioms}"
