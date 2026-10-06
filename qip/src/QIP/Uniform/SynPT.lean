import QIP.Uniform.Codec
import QIP.Execution
import QIP.Resources


/-!
# Q34 — polynomial-time functions on verifier syntax

Fields and derived quantities of descriptions, the holding predicate `Desc.held` (through a fold
equal to the recursive `msgHeld`), `Gate.okBool`, the checker `Desc.check` and the schedule
test `Desc.HasSchedule`.
-/

namespace ShiQIP.Uniform

open ShiQIP

instance : Inhabited Dir := ⟨.toVerifier⟩
instance : Inhabited Message := ⟨⟨.toVerifier, 0⟩⟩
instance : Inhabited Gate := ⟨.h 0⟩
instance : Inhabited Desc := ⟨⟨0, 0, [], []⟩⟩

/-! ### Fields -/

@[fun_prop] theorem PT.fp_numMsgs {α : Type} [Rep α] {f : α → Desc} (hf : PT f) :
    PT fun x => (f x).numMsgs := by unfold Desc.numMsgs; fun_prop

@[fun_prop] theorem PT.fp_totalWires {α : Type} [Rep α] {f : α → Desc} (hf : PT f) :
    PT fun x => (f x).totalWires := by unfold Desc.totalWires; fun_prop

@[fun_prop] theorem PT.fp_msgOffset {α : Type} [Rep α] {f : α → Desc} {g : α → ℕ} (hf : PT f)
    (hg : PT g) : PT fun x => (f x).msgOffset (g x) := by unfold Desc.msgOffset; fun_prop

theorem msgWidth_eq' (d : Desc) (j : ℕ) : d.msgWidth j = (d.msgs.map Message.width).getD j 0 := by
  simp [Desc.msgWidth, List.getD_eq_getElem?_getD, List.getElem?_map]

@[fun_prop] theorem PT.fp_msgWidth' {α : Type} [Rep α] {f : α → Desc} {g : α → ℕ} (hf : PT f)
    (hg : PT g) : PT fun x => (f x).msgWidth (g x) :=
  (show PT fun x => ((f x).msgs.map Message.width).getD (g x) 0 by fun_prop).of_eq
    fun x => (msgWidth_eq' _ _).symm

@[fun_prop] theorem PT.fp_gateCount {α : Type} [Rep α] {f : α → Desc} (hf : PT f) :
    PT fun x => (f x).gateCount := by unfold Desc.gateCount; fun_prop

/-! ### Decidable propositions -/

@[fun_prop] theorem PT.fp_decide_and {α : Type} [Rep α] {p q : α → Prop} [DecidablePred p]
    [DecidablePred q] (hp : PT fun x => decide (p x)) (hq : PT fun x => decide (q x)) :
    PT fun x => decide (p x ∧ q x) :=
  (PT.fp_and hp hq).of_eq fun _ => (Bool.decide_and _ _).symm

@[fun_prop] theorem PT.fp_decide_or {α : Type} [Rep α] {p q : α → Prop} [DecidablePred p]
    [DecidablePred q] (hp : PT fun x => decide (p x)) (hq : PT fun x => decide (q x)) :
    PT fun x => decide (p x ∨ q x) :=
  (PT.fp_or hp hq).of_eq fun _ => (Bool.decide_or _ _).symm

@[fun_prop] theorem PT.fp_decide_not {α : Type} [Rep α] {p : α → Prop} [DecidablePred p]
    (hp : PT fun x => decide (p x)) : PT fun x => decide ¬p x :=
  (PT.fp_not hp).of_eq fun _ => decide_not.symm

@[fun_prop] theorem PT.fp_decide_bool {α : Type} [Rep α] {f : α → Bool} (hf : PT f) :
    PT fun x => decide (f x = true) := hf.of_eq fun x => by cases f x <;> rfl

@[fun_prop] theorem PT.fp_bne_nat {α : Type} [Rep α] {f g : α → ℕ} (hf : PT f) (hg : PT g) :
    PT fun x => f x != g x :=
  (PT.fp_not (PT.fp_eq hf hg)).of_eq fun x => by
    by_cases h : f x = g x <;> simp [h, bne]

@[fun_prop] theorem PT.fp_bne_bool {α : Type} [Rep α] {f g : α → Bool} (hf : PT f) (hg : PT g) :
    PT fun x => f x != g x :=
  (PT.fp_ite hf (PT.fp_not hg) hg).of_eq fun x => by cases f x <;> cases g x <;> rfl

@[fun_prop] theorem PT.fp_beq_bool {α : Type} [Rep α] {f g : α → Bool} (hf : PT f) (hg : PT g) :
    PT fun x => f x == g x :=
  (PT.fp_ite hf hg (PT.fp_not hg)).of_eq fun x => by cases f x <;> cases g x <;> rfl

/-! ### Holding -/

/-- The direction condition of `msgHeld`. -/
def dirOK (j k : ℕ) (m : Message) : Bool := if m.dir.toB then decide (k < j) else decide (j ≤ k)

theorem dirOK_eq (j k : ℕ) (m : Message) :
    (match m.dir with
      | .toVerifier => decide (k < j)
      | .toProver => decide (j ≤ k)) = dirOK j k m := by
  rcases m with ⟨_ | _, w⟩ <;> rfl

/-- One step of the holding scan; the context is `(j, w)`. -/
def heldStep (q : ((ℕ × ℕ) × (Bool × (ℕ × ℕ))) × Message) : (ℕ × ℕ) × (Bool × (ℕ × ℕ)) :=
  (q.1.1, (q.1.2.1 || (decide (q.1.2.2.2 ≤ q.1.1.2 ∧ q.1.1.2 < q.1.2.2.2 + q.2.width) &&
    dirOK q.1.1.1 q.1.2.2.1 q.2), q.1.2.2.1 + 1, q.1.2.2.2 + q.2.width))

theorem foldS_heldStep (j w : ℕ) : ∀ (ms : List Message) (b : Bool) (k off : ℕ),
    foldS heldStep ((j, w), (b, k, off)) ms =
      ((j, w), (b || msgHeld j w ms k off, k + ms.length, off + (ms.map Message.width).sum))
  | [], b, k, off => by simp [foldS, msgHeld]
  | m :: ms, b, k, off => by
    simp only [foldS, List.foldl_cons] at *
    rw [show heldStep (((j, w), (b, k, off)), m) = ((j, w), (b || (decide (off ≤ w ∧ w < off + m.width)
      && dirOK j k m), k + 1, off + m.width)) from rfl]
    have := foldS_heldStep j w ms (b || (decide (off ≤ w ∧ w < off + m.width) && dirOK j k m))
      (k + 1) (off + m.width)
    simp only [foldS] at this
    rw [this]
    rcases m with ⟨_ | _, wd⟩ <;>
      simp only [msgHeld, dirOK, Dir.toB, List.length_cons, List.map_cons, List.sum_cons,
        Bool.or_assoc, if_true, if_false, Bool.false_eq_true] <;> congr 3 <;> ring

theorem PT.dirOKU : PT fun q : (ℕ × ℕ) × Message => dirOK q.1.1 q.1.2 q.2 := by
  unfold dirOK; fun_prop

@[fun_prop] theorem PT.fp_dirOK {α : Type} [Rep α] {j k : α → ℕ} {m : α → Message} (hj : PT j)
    (hk : PT k) (hm : PT m) : PT fun x => dirOK (j x) (k x) (m x) :=
  PT.comp (show PT fun x => ((j x, k x), m x) by fun_prop) PT.dirOKU

theorem PT.heldStepU : PT heldStep := by unfold heldStep; fun_prop

theorem PT.msgHeldU : PT fun p : (ℕ × ℕ) × (List Message × ℕ) => msgHeld p.1.1 p.1.2 p.2.1 0 p.2.2 := by
  have h := PT.foldl_gen (s := fun p : (ℕ × ℕ) × (List Message × ℕ) => (p.1, (false, (0 : ℕ), p.2.2)))
    (xs := fun p => p.2.1) PT.heldStepU (by fun_prop) (by fun_prop)
    ⟨4 * Polynomial.X + 4, fun ⟨⟨j, w⟩, ms, off⟩ k => by
      rw [foldS_heldStep]
      have h₁ := length_lt_enc_list ms
      have h₂ : ((ms.take k).map Message.width).sum ≤ (enc ms).length := by
        have key : ∀ l : List Message, (l.map Message.width).sum ≤ (enc l).length := by
          intro l
          induction l with
          | nil => simp
          | cons m l ih =>
            rw [enc_cons_length]; simp only [List.map_cons, List.sum_cons]
            have : m.width ≤ (enc m).length := by
              show m.width ≤ (enc (m.dir, m.width)).length
              rw [enc_pair_length, enc_nat_length]; omega
            omega
        exact (key _).trans (enc_take_le ms k)
      have h₃ := enc_bool_length (false || msgHeld j w (ms.take k) 0 off)
      simp only [enc_pair_length, enc_nat_length, List.length_take] at h₃ ⊢
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      have : min k ms.length ≤ ms.length := min_le_right _ _
      omega⟩
  exact (PT.fp_fst (PT.fp_snd h)).of_eq fun ⟨⟨j, w⟩, ms, off⟩ => by
    show (foldS heldStep ((j, w), (false, 0, off)) ms).2.1 = _
    rw [foldS_heldStep]; simp

@[fun_prop] theorem PT.fp_msgHeld {α : Type} [Rep α] {j w off : α → ℕ} {ms : α → List Message}
    (hj : PT j) (hw : PT w) (hms : PT ms) (hoff : PT off) :
    PT fun x => msgHeld (j x) (w x) (ms x) 0 (off x) :=
  PT.comp (show PT fun x => ((j x, w x), (ms x, off x)) by fun_prop) PT.msgHeldU

@[fun_prop] theorem PT.fp_held {α : Type} [Rep α] {d : α → Desc} {j w : α → ℕ} (hd : PT d)
    (hj : PT j) (hw : PT w) : PT fun x => (d x).held (j x) (w x) := by
  unfold Desc.held; fun_prop

/-! ### Gate checks -/

theorem okBool_eq (ok : ℕ → Bool) (g : Gate) : g.okBool ok =
    if g.cd.1 = 4 then (ok g.cd.2.1 && ok g.cd.2.2 && g.cd.2.1 != g.cd.2.2) else ok g.cd.2.1 := by
  cases g <;> rfl

@[fun_prop] theorem PT.fp_okBool {α : Type} [Rep α] {ok : α → ℕ → Bool} {g : α → Gate}
    (hok : PT fun p : α × ℕ => ok p.1 p.2) (hg : PT g) : PT fun x => (g x).okBool (ok x) := by
  have : PT fun x => if (g x).cd.1 = 4 then (ok x (g x).cd.2.1 && ok x (g x).cd.2.2 &&
      (g x).cd.2.1 != (g x).cd.2.2) else ok x (g x).cd.2.1 := by
    have h₁ : PT fun x => ok x (g x).cd.2.1 := PT.comp (show PT fun x => (x, (g x).cd.2.1) by fun_prop) hok
    have h₂ : PT fun x => ok x (g x).cd.2.2 := PT.comp (show PT fun x => (x, (g x).cd.2.2) by fun_prop) hok
    fun_prop
  exact this.of_eq fun x => (okBool_eq _ _).symm

/-! ### The checker -/

theorem alternates_eq : ∀ ms : List Message,
    Desc.alternates ms = (ms.zip ms.tail).all fun p => p.1.dir.toB != p.2.dir.toB
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    rw [Desc.alternates, alternates_eq (b :: rest)]
    rcases a with ⟨_ | _, _⟩ <;> rcases b with ⟨_ | _, _⟩ <;> simp [Dir.toB]

theorem blocksOkFrom_eq (d : Desc) : ∀ (bs : List (List Gate)) (j : ℕ),
    d.blocksOkFrom bs j = ((bs.zip (List.range' j bs.length)).all fun p =>
      p.1.all (Gate.okBool (d.held p.2)))
  | [], _ => rfl
  | b :: bs, j => by
    rw [Desc.blocksOkFrom, blocksOkFrom_eq d bs (j + 1)]
    simp [List.range'_succ]

@[fun_prop] theorem PT.fp_check {α : Type} [Rep α] {f : α → Desc} (hf : PT f) :
    PT fun x => (f x).check := by
  have : PT fun x => decide ((f x).out < (f x).priv) &&
      ((f x).msgs.zip (f x).msgs.tail).all (fun p => p.1.dir.toB != p.2.dir.toB) &&
      decide ((f x).blocks.length = (f x).msgs.length + 1) &&
      (((f x).blocks.zip (List.range' 0 (f x).blocks.length)).all fun p =>
        p.1.all (Gate.okBool ((f x).held p.2))) := by
    have hr : PT fun x => List.range' 0 (f x).blocks.length :=
      (show PT fun x => List.range (f x).blocks.length by fun_prop).of_eq fun x => List.range_eq_range'
    fun_prop
  exact this.of_eq fun x => by rw [Desc.check, alternates_eq, blocksOkFrom_eq]

/-! ### Schedules -/

theorem stdSchedule_eq (k : ℕ) : stdSchedule k = (List.range k).map fun i =>
    Dir.ofB (decide ((k - 1 - i) % 2 = 0)) := by
  unfold stdSchedule
  congr 1; funext i
  by_cases h : (k - 1 - i) % 2 = 0 <;> simp [h, Dir.ofB]

@[fun_prop] theorem PT.fp_stdSchedule {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) :
    PT fun x => stdSchedule (f x) :=
  (show PT fun x => (List.range (f x)).map fun i => Dir.ofB (decide ((f x - 1 - i) % 2 = 0)) by
    fun_prop).of_eq fun x => (stdSchedule_eq _).symm

theorem dirList_eq_iff (l₁ l₂ : List Dir) : decide (l₁ = l₂) =
    (decide (l₁.length = l₂.length) && (l₁.zip l₂).all fun p => p.1.toB == p.2.toB) := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp
  | cons a l ih =>
    cases l₂ with
    | nil => simp
    | cons b l₂ =>
      have := ih l₂
      rcases a with _ | _ <;> rcases b with _ | _ <;> simp_all [Dir.toB]

@[fun_prop] theorem PT.fp_hasSchedule {α : Type} [Rep α] {f : α → Desc} {k : α → ℕ} (hf : PT f)
    (hk : PT k) : PT fun x => decide ((f x).HasSchedule (k x)) := by
  have : PT fun x => decide (((f x).msgs.map Message.dir).length = (stdSchedule (k x)).length) &&
      (((f x).msgs.map Message.dir).zip (stdSchedule (k x))).all fun p => p.1.toB == p.2.toB := by
    fun_prop
  exact this.of_eq fun x => by unfold Desc.HasSchedule; rw [← dirList_eq_iff]; congr

end ShiQIP.Uniform
