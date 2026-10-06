import QIP.Uniform.Mach


/-!
# Q34 — glue routines on Boolean stacks

All routines use the first state component `Option Bool` as a one-symbol scratch register and
leave it empty (`none`) when they halt.

* `moveAll a b`: pop all of `a` and push it onto `b` (reversed), in `2 |a| + 2` steps;
* `moveAll2 a b c`: the same, pushing every symbol onto both `b` and `c`;
* `discard a`: empty `a`, in `2 |a| + 2` steps;
* `parseV a b c`: move exactly one tree code from the top of `a` onto `b` (reversed), with the
  counter stack `c`, in `2 |code x| + 2` steps.
-/

namespace ShiQIP.Uniform

open Turing

/-! ### Binary trees and their codes -/

/-- Binary trees, the common representation of all data. -/
inductive V where
  | leaf
  | node (a b : V)
  deriving DecidableEq

/-- The preorder code of a tree: `node ↦ true`, `leaf ↦ false`. It is prefix free. -/
def V.code : V → List Bool
  | .leaf => [false]
  | .node a b => true :: (a.code ++ b.code)

section Glue

variable {K τ : Type} [DecidableEq K]

/-- Pop `a` into the scratch register. -/
def popTo (a : K) : BS K Unit (Option Bool × τ) := .pop a (fun v x => (x, v.2)) .halt

/-- Push the scratch register onto `b`, then pop `a` into it. -/
def moveBody (a b : K) : BS K Unit (Option Bool × τ) :=
  .push b (fun v => v.1.getD false) (.pop a (fun v x => (x, v.2)) .halt)

/-- Push the scratch register onto `b` and `c`, then pop `a` into it. -/
def moveBody2 (a b c : K) : BS K Unit (Option Bool × τ) :=
  .push b (fun v => v.1.getD false) (.push c (fun v => v.1.getD false) (.pop a (fun v x => (x, v.2)) .halt))

/-- Move all of `a` onto `b`, reversed. -/
def moveAll (a b : K) : Mach K (Option Bool × τ) :=
  seq (basic (popTo a)) (loop (fun v => v.1.isSome) (basic (moveBody a b)))

/-- Move all of `a` onto both `b` and `c`, reversed. -/
def moveAll2 (a b c : K) : Mach K (Option Bool × τ) :=
  seq (basic (popTo a)) (loop (fun v => v.1.isSome) (basic (moveBody2 a b c)))

/-- Empty `a`. -/
def discard (a : K) : Mach K (Option Bool × τ) :=
  seq (basic (popTo a)) (loop (fun v => v.1.isSome) (basic (popTo a)))

theorem runs_moveLoop (a b : K) (hab : a ≠ b) (u : τ) :
    ∀ (L : List Bool) (x : Bool) (S : K → List Bool), S a = L →
    Runs (loop (fun v : Option Bool × τ => v.1.isSome) (basic (moveBody a b))) (some x, u) S (none, u)
      (Function.update (Function.update S a []) b ((x :: L).reverse ++ S b)) (2 * L.length + 3) := by
  intro L
  induction L with
  | nil =>
    intro x S hS
    have h₁ := runs_basic (moveBody (τ := τ) a b) (some x, u) S rfl
    simp only [moveBody, TM2.stepAux, Function.update_of_ne hab, hS, Option.getD_some,
      List.head?_nil, List.tail_nil] at h₁
    refine (runs_loop_true rfl h₁ (runs_loop_false _ rfl)).of_eq rfl ?_ rfl
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  | cons y L ih =>
    intro x S hS
    have h₁ := runs_basic (moveBody (τ := τ) a b) (some x, u) S rfl
    simp only [moveBody, TM2.stepAux, Function.update_of_ne hab, hS, Option.getD_some,
      List.head?_cons, List.tail_cons] at h₁
    have h₂ := ih y (Function.update (Function.update S b (x :: S b)) a L) (Function.update_self ..)
    refine (runs_loop_true rfl h₁ h₂).of_eq rfl ?_ (by simp; ring)
    funext k
    simp only [Function.update_apply, List.reverse_cons, List.append_assoc]
    split_ifs <;> simp_all

theorem runs_moveAll (a b : K) (hab : a ≠ b) (o : Option Bool) (u : τ) (S : K → List Bool) :
    Runs (moveAll a b) (o, u) S (none, u)
      (Function.update (Function.update S a []) b ((S a).reverse ++ S b)) (2 * (S a).length + 2) := by
  rcases hS : S a with _ | ⟨x, L⟩
  · have h₁ := runs_basic (popTo (τ := τ) a) (o, u) S rfl
    simp only [popTo, TM2.stepAux, hS, List.head?_nil, List.tail_nil] at h₁
    refine (runs_seq h₁ (runs_loop_false _ rfl)).of_eq rfl ?_ rfl
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · have h₁ := runs_basic (popTo (τ := τ) a) (o, u) S rfl
    simp only [popTo, TM2.stepAux, hS, List.head?_cons, List.tail_cons] at h₁
    have h₂ := runs_moveLoop a b hab u L x (Function.update S a L) (Function.update_self ..)
    refine (runs_seq h₁ h₂).of_eq rfl ?_ (by simp; ring)
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

theorem runs_moveLoop2 (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (u : τ) :
    ∀ (L : List Bool) (x : Bool) (S : K → List Bool), S a = L →
    Runs (loop (fun v : Option Bool × τ => v.1.isSome) (basic (moveBody2 a b c))) (some x, u) S (none, u)
      (Function.update (Function.update (Function.update S a []) b ((x :: L).reverse ++ S b)) c
        ((x :: L).reverse ++ S c)) (2 * L.length + 3) := by
  intro L
  induction L with
  | nil =>
    intro x S hS
    have h₁ := runs_basic (moveBody2 (τ := τ) a b c) (some x, u) S rfl
    simp only [moveBody2, TM2.stepAux, Function.update_of_ne hab, Function.update_of_ne hac, hS,
      Option.getD_some, List.head?_nil, List.tail_nil] at h₁
    refine (runs_loop_true rfl h₁ (runs_loop_false _ rfl)).of_eq rfl ?_ rfl
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  | cons y L ih =>
    intro x S hS
    have h₁ := runs_basic (moveBody2 (τ := τ) a b c) (some x, u) S rfl
    simp only [moveBody2, TM2.stepAux, Function.update_of_ne hab, Function.update_of_ne hac, hS,
      Option.getD_some, List.head?_cons, List.tail_cons] at h₁
    have h₂ := ih y (Function.update (Function.update (Function.update S b (x :: S b)) c
      (x :: Function.update S b (x :: S b) c)) a L) (Function.update_self ..)
    refine (runs_loop_true rfl h₁ h₂).of_eq rfl ?_ (by simp; ring)
    funext k
    simp only [Function.update_apply, List.reverse_cons, List.append_assoc]
    split_ifs <;> simp_all

theorem runs_moveAll2 (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (o : Option Bool) (u : τ)
    (S : K → List Bool) :
    Runs (moveAll2 a b c) (o, u) S (none, u)
      (Function.update (Function.update (Function.update S a []) b ((S a).reverse ++ S b)) c
        ((S a).reverse ++ S c)) (2 * (S a).length + 2) := by
  rcases hS : S a with _ | ⟨x, L⟩
  · have h₁ := runs_basic (popTo (τ := τ) a) (o, u) S rfl
    simp only [popTo, TM2.stepAux, hS, List.head?_nil, List.tail_nil] at h₁
    refine (runs_seq h₁ (runs_loop_false _ rfl)).of_eq rfl ?_ rfl
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · have h₁ := runs_basic (popTo (τ := τ) a) (o, u) S rfl
    simp only [popTo, TM2.stepAux, hS, List.head?_cons, List.tail_cons] at h₁
    have h₂ := runs_moveLoop2 a b c hab hac hbc u L x (Function.update S a L) (Function.update_self ..)
    refine (runs_seq h₁ h₂).of_eq rfl ?_ (by simp; ring)
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

theorem runs_discardLoop (a : K) (u : τ) :
    ∀ (L : List Bool) (x : Bool) (S : K → List Bool), S a = L →
    Runs (loop (fun v : Option Bool × τ => v.1.isSome) (basic (popTo a))) (some x, u) S (none, u)
      (Function.update S a []) (2 * L.length + 3) := by
  intro L
  induction L with
  | nil =>
    intro x S hS
    have h₁ := runs_basic (popTo (τ := τ) a) (some x, u) S rfl
    simp only [popTo, TM2.stepAux, hS, List.head?_nil, List.tail_nil] at h₁
    exact (runs_loop_true rfl h₁ (runs_loop_false _ rfl)).of_eq rfl rfl rfl
  | cons y L ih =>
    intro x S hS
    have h₁ := runs_basic (popTo (τ := τ) a) (some x, u) S rfl
    simp only [popTo, TM2.stepAux, hS, List.head?_cons, List.tail_cons] at h₁
    have h₂ := ih y (Function.update S a L) (Function.update_self ..)
    refine (runs_loop_true rfl h₁ h₂).of_eq rfl ?_ (by simp; ring)
    simp

theorem runs_discard (a : K) (o : Option Bool) (u : τ) (S : K → List Bool) :
    Runs (discard a) (o, u) S (none, u) (Function.update S a []) (2 * (S a).length + 2) := by
  rcases hS : S a with _ | ⟨x, L⟩
  · have h₁ := runs_basic (popTo (τ := τ) a) (o, u) S rfl
    simp only [popTo, TM2.stepAux, hS, List.head?_nil, List.tail_nil] at h₁
    exact (runs_seq h₁ (runs_loop_false _ rfl)).of_eq rfl rfl rfl
  · have h₁ := runs_basic (popTo (τ := τ) a) (o, u) S rfl
    simp only [popTo, TM2.stepAux, hS, List.head?_cons, List.tail_cons] at h₁
    have h₂ := runs_discardLoop a u L x (Function.update S a L) (Function.update_self ..)
    refine (runs_seq h₁ h₂).of_eq rfl (by simp) (by simp; ring)

/-- One parse step: move a symbol from `a` to `b`; count pending subtrees on `c`. -/
def parseBody (a b c : K) : BS K Unit (Option Bool × τ) :=
  .pop a (fun v x => (x, v.2)) (.push b (fun v => v.1.getD false)
    (.branch (fun v => v.1.getD false)
      (.push c (fun _ => true) (.peek c (fun v x => (x, v.2)) .halt))
      (.pop c (fun v x => (x, v.2)) (.peek c (fun v x => (x, v.2)) .halt))))

/-- Move one tree code from the top of `a` onto `b` (reversed), using the counter stack `c`. -/
def parseV (a b c : K) : Mach K (Option Bool × τ) :=
  seq (basic (.push c (fun _ => true) (.load (fun v => (some true, v.2)) .halt)))
    (loop (fun v => v.1.isSome) (basic (parseBody a b c)))

theorem parseBody_l (a b c : K) (v : Option Bool × τ) (S : K → List Bool) :
    (TM2.stepAux (parseBody a b c) v S).l = none := by
  simp only [parseBody, TM2.stepAux]
  rcases (S a).head? with _ | ⟨_ | _⟩ <;> rfl

theorem runs_parseLoop (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (u : τ) (x : V) :
    ∀ (p : ℕ) (rest : List Bool) (S : K → List Bool) (v' : Option Bool × τ) (S'' : K → List Bool)
      (t' : ℕ), S a = x.code ++ rest → S c = List.replicate (p + 1) true →
    Runs (loop (fun v : Option Bool × τ => v.1.isSome) (basic (parseBody a b c)))
      ((List.replicate p true).head?, u)
      (Function.update (Function.update (Function.update S a rest) b (x.code.reverse ++ S b)) c
        (List.replicate p true)) v' S'' t' →
    Runs (loop (fun v : Option Bool × τ => v.1.isSome) (basic (parseBody a b c))) (some true, u) S v'
      S'' (t' + 2 * x.code.length) := by
  induction x with
  | leaf =>
    intro p rest S v' S'' t' ha hc h
    have h₁ := runs_basic (parseBody (τ := τ) a b c) (some true, u) S (parseBody_l ..)
    simp only [parseBody, TM2.stepAux, ha, hc, V.code, List.cons_append, List.nil_append,
      List.head?_cons, List.tail_cons, Option.getD_some, Function.update_of_ne hab.symm,
      Function.update_of_ne hac.symm, Function.update_of_ne hbc.symm, Function.update_self,
      cond_false, List.replicate_succ] at h₁
    simp only [V.code, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at h
    exact (runs_loop_true rfl h₁ h).of_eq rfl rfl (by simp [V.code])
  | node x₁ x₂ ih₁ ih₂ =>
    intro p rest S v' S'' t' ha hc h
    have h₁ := runs_basic (parseBody (τ := τ) a b c) (some true, u) S (parseBody_l ..)
    simp only [parseBody, TM2.stepAux, ha, hc, V.code, List.cons_append, List.append_assoc,
      List.head?_cons, List.tail_cons, Option.getD_some, Function.update_of_ne hab.symm,
      Function.update_of_ne hac.symm, Function.update_of_ne hbc.symm, Function.update_self,
      cond_true] at h₁
    have hne := And.intro hab (And.intro hac (And.intro hbc (And.intro hab.symm
      (And.intro hac.symm hbc.symm))))
    have h₃ := ih₂ p rest (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update S a (x₁.code ++ (x₂.code ++ rest))) b
        (true :: S b)) c (true :: List.replicate (p + 1) true)) a (x₂.code ++ rest)) b
          (x₁.code.reverse ++ (true :: S b))) c (List.replicate (p + 1) true)) v' S'' t'
      (by simp [hne]) (by simp) (by
        convert h using 2
        funext k
        simp only [Function.update_apply, V.code, List.reverse_cons, List.reverse_append,
          List.append_assoc]
        split_ifs <;> simp_all)
    have h₄ := ih₁ (p + 1) (x₂.code ++ rest) (Function.update (Function.update
      (Function.update S a (x₁.code ++ (x₂.code ++ rest))) b (true :: S b)) c
        (true :: List.replicate (p + 1) true)) v' S'' (t' + 2 * x₂.code.length)
      (by simp [hne]) (by simp [List.replicate_succ]) (by
        convert h₃ using 2
        · rfl
        · funext k
          simp only [Function.update_apply]
          split_ifs <;> simp_all)
    exact (runs_loop_true rfl h₁ h₄).of_eq rfl rfl (by simp only [V.code, List.length_cons, List.length_append]; ring)

theorem runs_parseV (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (o : Option Bool) (u : τ)
    (x : V) (rest : List Bool) (S : K → List Bool) (ha : S a = x.code ++ rest) (hc : S c = []) :
    Runs (parseV a b c) (o, u) S (none, u)
      (Function.update (Function.update S a rest) b (x.code.reverse ++ S b)) (2 * x.code.length + 2) := by
  have hne := And.intro hab (And.intro hac (And.intro hbc (And.intro hab.symm
    (And.intro hac.symm hbc.symm))))
  have h₁ := runs_basic (K := K) (.push c (fun _ => true) (.load (fun v : Option Bool × τ =>
    (some true, v.2)) .halt)) (o, u) S rfl
  simp only [TM2.stepAux, hc] at h₁
  have h₂ := runs_parseLoop a b c hab hac hbc u x 0 rest (Function.update S c [true]) (none, u) _ 1
    (by simp [hne, ha]) (by simp) (runs_loop_false _ rfl)
  refine (runs_seq h₁ h₂).of_eq rfl ?_ (by ring)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end Glue

end ShiQIP.Uniform
