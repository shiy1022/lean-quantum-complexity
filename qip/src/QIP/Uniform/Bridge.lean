import QIP.Uniform.PT


/-!
# Q34 — from `PT` to Mathlib's polynomial-time computability

* `BM.toFinTM2`: a bundled machine as a `FinTM2` (alphabet `Bool` on every stack).
* `inPolyTime_of_computes`: a bundled machine computing `ea a ↦ eb (f a)` within a polynomial
  gives `TM2ComputableInPolyTime ea eb f`.
* `rawIn`/`rawOut`: machines converting between a raw Boolean string and the tree code of the
  same string.
* `polyTimeComputable_of_PT`: a `PT` function `Str → Str` is `PvsNP.PolyTimeComputable`.
-/

namespace ShiQIP.Uniform

open Turing

/-- A bundled machine as a Mathlib `FinTM2`. -/
abbrev BM.toFinTM2 (B : BM) : FinTM2 :=
  @FinTM2.mk B.K B.dK B.fK B.i B.o (fun _ => Bool) B.M.Λ B.M.main B.M.fin B.σ B.init B.fσ
    inferInstance B.M.m

theorem BM.initList_eq (B : BM) (x : List Bool) :
    initList B.toFinTM2 x = ⟨some B.M.main, B.init, one B.i x⟩ := by
  have : (initList B.toFinTM2 x).stk = one B.i x := by
    funext k
    by_cases hk : k = B.i
    · subst hk
      exact (ShiQIP.TMComp.initList_stk_self B.toFinTM2 x).trans (by simp [one])
    · rw [ShiQIP.TMComp.initList_stk_ne B.toFinTM2 x k hk]
      unfold one
      exact (Function.update_of_ne hk _ (fun _ => [])).symm
  rw [show initList B.toFinTM2 x = ⟨(initList B.toFinTM2 x).l, (initList B.toFinTM2 x).var,
    (initList B.toFinTM2 x).stk⟩ from rfl, this]
  rfl

theorem BM.haltList_eq (B : BM) (y : List Bool) :
    haltList B.toFinTM2 y = ⟨none, B.init, one B.o y⟩ := by
  have : (haltList B.toFinTM2 y).stk = one B.o y := by
    funext k
    by_cases hk : k = B.o
    · subst hk
      exact (ShiQIP.TMComp.haltList_stk_self B.toFinTM2 y).trans (by simp [one])
    · rw [ShiQIP.TMComp.haltList_stk_ne B.toFinTM2 y k hk]
      unfold one
      exact (Function.update_of_ne hk _ (fun _ => [])).symm
  rw [show haltList B.toFinTM2 y = ⟨(haltList B.toFinTM2 y).l, (haltList B.toFinTM2 y).var,
    (haltList B.toFinTM2 y).stk⟩ from rfl, this]
  rfl

/-- A bundled machine computing `ea a ↦ eb (f a)` in polynomial time is a Mathlib polynomial-time
TM2 computation. -/
theorem inPolyTime_of_computes {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (B : BM) (p : Polynomial ℕ) (h : ∀ a, ∃ t ≤ p.eval (ea a).length, B.Computes (ea a) (eb (f a)) t) :
    Nonempty (TM2ComputableInPolyTime ea eb f) := by
  refine ⟨⟨⟨B.toFinTM2, Equiv.refl _, Equiv.refl _⟩, p, fun a => ?_⟩⟩
  have ht := (h a).choose_spec.1
  have hB := (h a).choose_spec.2
  refine ⟨⟨(h a).choose, ?_⟩, ?_⟩
  · show (flip bind B.toFinTM2.step)^[(h a).choose]
        (some (initList B.toFinTM2 (List.map id (ea a)))) =
      Option.map (haltList B.toFinTM2) (some (List.map id (eb (f a))))
    rw [List.map_id, List.map_id, Option.map_some, BM.initList_eq, BM.haltList_eq]
    exact hB
  · exact ht

/-- `PT` functions are Mathlib polynomial-time computable in their tree codes. -/
theorem PT.inPolyTime {α β : Type} [Rep α] [Rep β] {f : α → β} (hf : PT f) :
    Nonempty (TM2ComputableInPolyTime (enc : α → List Bool) (enc : β → List Bool) f) := by
  obtain ⟨B, p, hp⟩ := hf
  exact inPolyTime_of_computes B p fun a => (hp a).2

/-! ### Raw strings and tree codes -/

/-- The code of one item of a Boolean list. -/
def itemT (b : Bool) : List Bool := true :: enc b

theorem enc_list_bool (l : List Bool) : enc l = l.flatMap itemT ++ [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [enc_cons, ih]; simp [itemT]

/-- Pop register `a` into the scratch register. -/
def popA : BS Reg Unit (Option Bool × Unit) := .pop .a (fun v x => (x, v.2)) .halt

/-- Push the item code of the current bit (reversed) onto `b`, then pop `a`. -/
def bodyIn : BS Reg Unit (Option Bool × Unit) :=
  .branch (fun v => v.1.getD false) (pushL .b [true, true, false, false] popA)
    (pushL .b [true, false] popA)

theorem runs_loopIn :
    ∀ (L : List Bool) (x : Bool) (S : Reg → List Bool), S .a = L →
    Runs (loop (fun v : Option Bool × Unit => v.1.isSome) (basic bodyIn)) (some x, ()) S (none, ())
      (Function.update (Function.update S .a []) .b (((x :: L).flatMap itemT).reverse ++ S .b))
      (2 * L.length + 3) := by
  intro L
  induction L with
  | nil =>
    intro x S hS
    have h₁ := runs_basic bodyIn (some x, ()) S (by cases x <;> rfl)
    cases x <;>
    · simp only [bodyIn, popA, TM2.stepAux, stepAux_pushL, Option.getD_some, cond_true, cond_false,
        Function.update_apply, reduceCtorEq, if_false, hS, List.head?_nil, List.tail_nil] at h₁
      refine (runs_loop_true rfl h₁ (runs_loop_false _ rfl)).of_eq rfl ?_ rfl
      funext k
      cases k <;> simp [itemT, enc_true, enc_false]
  | cons y L ih =>
    intro x S hS
    have h₁ := runs_basic bodyIn (some x, ()) S (by cases x <;> rfl)
    cases x <;>
    · simp only [bodyIn, popA, TM2.stepAux, stepAux_pushL, Option.getD_some, cond_true, cond_false,
        Function.update_apply, reduceCtorEq, if_false, hS, List.head?_cons, List.tail_cons] at h₁
      refine (runs_loop_true rfl h₁ (ih y _ ?_)).of_eq rfl ?_ (by simp; ring)
      · simp
      · funext k
        cases k <;> simp [itemT, enc_true, enc_false]

/-- Raw string to tree code. -/
def rawInM : Mach Reg (Option Bool × Unit) :=
  seq (basic (.push .c (fun _ => false) popA))
    (seq (loop (fun v => v.1.isSome) (basic bodyIn)) (moveAll .b .c))

theorem rawInM_runs (x : List Bool) :
    ∃ t ≤ 12 * x.length + 10, Runs rawInM (none, ()) (reg4 x [] [] []) (none, ())
      (reg4 [] [] (enc x) []) t := by
  rw [enc_list_bool]
  rcases x with _ | ⟨b, L⟩
  · have h₁ := runs_basic (.push Reg.c (fun _ => false) popA) (none, ()) (reg4 [] [] [] []) rfl
    simp only [popA, TM2.stepAux] at h₁
    have h₂ := runs_moveAll (τ := Unit) Reg.b .c (by decide) none () (reg4 [] [] [false] [])
    refine ⟨_, ?_, runs_seq h₁ (runs_seq (runs_loop_false _ ?_) (h₂.of_eq rfl ?_ rfl) |>.of_eq₀ ?_)⟩
    · simp [reg4]
    · simp
    · funext k; cases k <;> simp [reg4]
    · funext k; cases k <;> simp [reg4]
  · have h₁ := runs_basic (.push Reg.c (fun _ => false) popA) (none, ()) (reg4 (b :: L) [] [] []) rfl
    simp only [popA, TM2.stepAux, reg4, Function.update_apply, reduceCtorEq, if_false,
      List.head?_cons, List.tail_cons] at h₁
    have h₃ := runs_moveAll (τ := Unit) Reg.b .c (by decide) none ()
      (reg4 [] ((b :: L).flatMap itemT).reverse [false] [])
    refine ⟨_, ?_, runs_seq h₁ (runs_seq ((runs_loopIn L b _ ?_).of_eq rfl ?_ rfl)
      (h₃.of_eq rfl ?_ rfl)) |>.of_eq₀ ?_⟩
    · simp only [reg4, List.length_reverse]
      have : ((b :: L).flatMap itemT).length ≤ 4 * (L.length + 1) := by
        rw [List.length_flatMap]
        have : ∀ y ∈ (b :: L), (itemT y).length ≤ 4 := by
          intro y _; cases y <;> simp [itemT, enc_true, enc_false]
        calc ((b :: L).map fun y => (itemT y).length).sum ≤ ((b :: L).map fun _ => 4).sum :=
              List.sum_le_sum (by simpa using this)
          _ = 4 * (L.length + 1) := by simp [List.sum_replicate]; ring
      simp only [List.length_cons]
      omega
    · simp
    · funext k; cases k <;> simp [reg4]
    · funext k; cases k <;> simp [reg4]
    · funext k; cases k <;> simp [reg4]

/-- Read one item code from `a`, push the bit onto `b`, pop `a`. -/
def bodyOut : BS Reg Unit (Option Bool × Unit) :=
  .pop .a (fun v x => (x, v.2)) (.branch (fun v => v.1.getD false)
    (.pop .a (fun v x => (x, v.2)) (.pop .a (fun v x => (x, v.2)) (.push .b (fun _ => true) popA)))
    (.push .b (fun _ => false) popA))

theorem runs_loopOut :
    ∀ (l : List Bool) (b : Bool) (S : Reg → List Bool), S .a = enc b ++ enc l →
    Runs (loop (fun v : Option Bool × Unit => v.1.getD false) (basic bodyOut)) (some true, ()) S
      (some false, ()) (Function.update (Function.update S .a []) .b ((b :: l).reverse ++ S .b))
      (2 * l.length + 3) := by
  intro l
  induction l with
  | nil =>
    intro b S hS
    have h₁ := runs_basic bodyOut (some true, ()) S (by cases b <;> simp [bodyOut, popA, TM2.stepAux, hS, enc_true, enc_false, enc_nil])
    cases b <;>
    · simp only [bodyOut, popA, TM2.stepAux, hS, enc_true, enc_false, enc_nil, List.cons_append,
        List.nil_append, List.head?_cons, List.tail_cons, Option.getD_some, cond_true, cond_false,
        Function.update_apply, reduceCtorEq, if_false, if_true] at h₁
      refine (runs_loop_true rfl h₁ (runs_loop_false _ rfl)).of_eq rfl ?_ rfl
      funext k
      cases k <;> simp
  | cons c l ih =>
    intro b S hS
    have h₁ := runs_basic bodyOut (some true, ()) S (by cases b <;> simp [bodyOut, popA, TM2.stepAux, hS, enc_true, enc_false, enc_cons])
    cases b <;>
    · simp only [bodyOut, popA, TM2.stepAux, hS, enc_true, enc_false, enc_cons, List.cons_append,
        List.nil_append, List.head?_cons, List.tail_cons, Option.getD_some, cond_true, cond_false,
        Function.update_apply, reduceCtorEq, if_false, if_true] at h₁
      refine (runs_loop_true rfl h₁ (ih c _ ?_)).of_eq rfl ?_ (by simp; ring)
      · simp
      · funext k
        cases k <;> simp

/-- Rep code to raw string. -/
def rawOutM : Mach Reg (Option Bool × Unit) :=
  seq (basic popA) (seq (loop (fun v => v.1.getD false) (basic bodyOut)) (moveAll .b .c))

theorem rawOutM_runs (x : List Bool) :
    ∃ t ≤ 4 * x.length + 10, Runs rawOutM (none, ()) (reg4 (enc x) [] [] []) (none, ())
      (reg4 [] [] x []) t := by
  rcases x with _ | ⟨b, l⟩
  · have h₁ := runs_basic popA (none, ()) (reg4 (enc ([] : List Bool)) [] [] []) rfl
    simp only [popA, TM2.stepAux, enc_nil, reg4, List.head?_cons, List.tail_cons] at h₁
    have h₂ := runs_moveAll (τ := Unit) Reg.b .c (by decide) (some false) () (reg4 [] [] [] [])
    refine ⟨_, ?_, runs_seq h₁ (runs_seq (runs_loop_false _ rfl) ((h₂.of_eq rfl ?_ rfl).of_eq₀ ?_))
      |>.of_eq₀ ?_⟩
    · simp [reg4]
    · funext k; cases k <;> simp [reg4]
    · funext k; cases k <;> simp [reg4]
    · funext k; cases k <;> simp [reg4, enc_nil]
  · have h₁ := runs_basic popA (none, ()) (reg4 (enc (b :: l)) [] [] []) rfl
    simp only [popA, TM2.stepAux, enc_cons, reg4, List.head?_cons, List.tail_cons] at h₁
    have h₃ := runs_moveAll (τ := Unit) Reg.b .c (by decide) (some false) ()
      (reg4 [] (b :: l).reverse [] [])
    refine ⟨_, ?_, runs_seq h₁ (runs_seq ((runs_loopOut l b _ ?_).of_eq rfl
      (show _ = reg4 [] (b :: l).reverse [] [] from ?_) rfl) (h₃.of_eq rfl ?_ rfl)) |>.of_eq₀ ?_⟩
    · simp only [reg4, List.length_reverse, List.length_cons]
      omega
    · simp
    · funext k; cases k <;> simp [reg4]
    · funext k; cases k <;> simp [reg4]
    · funext k; cases k <;> simp [reg4, enc_cons]

/-- **From `PT` to `PolyTimeComputable`.** -/
theorem polyTimeComputable_of_PT {F : List Bool → List Bool} (hF : PT F) :
    PvsNP.PolyTimeComputable F := by
  have h₁ : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) enc id) :=
    inPolyTime_of_computes (regB rawInM) (12 * Polynomial.X + 10) fun x => by
      obtain ⟨t, ht, h⟩ := rawInM_runs x
      exact ⟨t, by simpa using ht, regB_computes h⟩
  have h₃ : Nonempty (TM2ComputableInPolyTime enc (id : List Bool → List Bool) id) :=
    inPolyTime_of_computes (regB rawOutM) (4 * Polynomial.X + 10) fun x => by
      obtain ⟨t, ht, h⟩ := rawOutM_runs x
      refine ⟨t, ?_, regB_computes h⟩
      have := length_lt_enc_list x
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega
  have := ShiQIP.TMComp.comp_inPolyTime (ShiQIP.TMComp.comp_inPolyTime h₁ hF.inPolyTime) h₃
  exact this

end ShiQIP.Uniform
