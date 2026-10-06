import QIP.Uniform.SynRep


/-!
# Q34 — the encoder and a total decoder are polynomial time

* `PT.encode`: the Boolean encoding of descriptions is `PT`.
* `pNat`, `pList`, `pMsg`, `pGate`, `pDesc`: total parsers (each returns the parsed value and the
  unread suffix), built from folds. `dec s = (pDesc s).1` satisfies `dec (encode d) = d`, and
  `PT.dec`.
-/

namespace ShiQIP.Uniform

open ShiQIP

/-! ### The encoder -/

@[fun_prop] theorem PT.fp_encNat {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) :
    PT fun x => encNat (f x) := by
  unfold encNat; fun_prop

theorem encDir_eq (d : Dir) : encDir d = [d.toB] := by cases d <;> rfl

@[fun_prop] theorem PT.fp_encDir {α : Type} [Rep α] {f : α → Dir} (hf : PT f) :
    PT fun x => encDir (f x) :=
  (show PT fun x => [(f x).toB] by fun_prop).of_eq fun x => (encDir_eq _).symm

@[fun_prop] theorem PT.fp_encMsg {α : Type} [Rep α] {f : α → Message} (hf : PT f) :
    PT fun x => encMsg (f x) := by
  unfold encMsg; fun_prop

theorem encGate_eq (g : Gate) : encGate g =
    encNat g.cd.1 ++ encNat g.cd.2.1 ++ (if g.cd.1 = 4 then encNat g.cd.2.2 else []) := by
  cases g <;> simp [encGate, Gate.cd]

@[fun_prop] theorem PT.fp_encGate {α : Type} [Rep α] {f : α → Gate} (hf : PT f) :
    PT fun x => encGate (f x) :=
  (show PT fun x => encNat (f x).cd.1 ++ encNat (f x).cd.2.1 ++
    (if (f x).cd.1 = 4 then encNat (f x).cd.2.2 else []) by fun_prop).of_eq
    fun x => (encGate_eq _).symm

theorem PT.encListU {α : Type} [Rep α] {e : α → Str} (he : PT e) :
    PT fun l : List α => encList e l := by
  unfold encList; fun_prop

@[fun_prop] theorem PT.fp_encBlock {α : Type} [Rep α] {f : α → List Gate} (hf : PT f) :
    PT fun x => encBlock (f x) := by
  unfold encBlock encList; fun_prop

/-- **The encoder is polynomial time.** -/
theorem PT.encodeU : PT ShiQIP.encode := by
  unfold ShiQIP.encode encList; fun_prop

/-! ### Total parsers -/

/-- One step of the unary parser: count leading `true`s, then copy the rest. -/
def natStep (q : (Bool × (ℕ × Str)) × Bool) : Bool × (ℕ × Str) :=
  if q.1.1 then (true, q.1.2.1, q.1.2.2 ++ [q.2])
  else if q.2 then (false, q.1.2.1 + 1, q.1.2.2) else (true, q.1.2.1, q.1.2.2)

/-- The unary parser: the number of leading `true`s and the suffix after the first `false`. -/
def pNat (s : Str) : ℕ × Str :=
  ((foldS natStep (false, 0, []) s).2.1, (foldS natStep (false, 0, []) s).2.2)

attribute [irreducible] pNat

theorem foldS_natStep_done (n : ℕ) (acc r : Str) :
    foldS natStep (true, n, acc) r = (true, n, acc ++ r) := by
  induction r generalizing acc with
  | nil => simp [foldS]
  | cons b r ih => simp only [foldS, List.foldl_cons] at ih ⊢; rw [natStep, if_pos rfl, ih]; simp

theorem foldS_natStep (n k : ℕ) (r : Str) :
    foldS natStep (false, n, []) (List.replicate k true ++ false :: r) = (true, n + k, r) := by
  induction k generalizing n with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, foldS, List.foldl_cons]
    rw [show natStep ((false, n, []), false) = (true, n, []) from rfl]
    exact (foldS_natStep_done n [] r).trans (by simp)
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, foldS, List.foldl_cons] at ih ⊢
    rw [show natStep ((false, n, []), true) = (false, n + 1, []) from rfl, ih]
    simp; ring

theorem pNat_encNat (k : ℕ) (r : Str) : pNat (encNat k ++ r) = (k, r) := by
  simp only [pNat, encNat, List.append_assoc, List.singleton_append, foldS_natStep]
  simp

theorem PT.natStepU : PT natStep := by unfold natStep; fun_prop

theorem PT.pNatU : PT pNat := by
  have h := PT.foldl_unif (α := Bool) (step := natStep) PT.natStepU 3 fun s x => by
    obtain ⟨d, n, acc⟩ := s
    have h₁ := length_enc_pos x
    have h₂ := enc_append_length acc [x]
    unfold natStep
    split_ifs <;> simp only [enc_pair_length, enc_nat_length, enc_cons_length, enc_nil,
      List.length_cons, List.length_nil, enc_true, enc_false] at h₂ ⊢ <;> cases d <;>
      simp_all [enc_true, enc_false] <;> omega
  unfold pNat
  fun_prop

attribute [fun_prop] PT.pNatU

@[fun_prop] theorem PT.fp_pNat {α : Type} [Rep α] {f : α → Str} (hf : PT f) :
    PT fun x => pNat (f x) := PT.comp hf PT.pNatU

/-! ### Parser bounds -/

theorem enc_prod_length {α β : Type} [Rep α] [Rep β] (x : α × β) :
    (enc x).length = (enc x.1).length + (enc x.2).length + 1 := enc_pair_length x.1 x.2

/-- A parser whose value is polynomially bounded and whose rest is a suffix of its input. -/
def ParserB {α : Type} [Rep α] (p : Str → α × Str) (P : Polynomial ℕ) : Prop :=
  ∀ s, (enc (p s).1).length ≤ P.eval (enc s).length ∧ (p s).2 <:+ s

theorem enc_suffix_le {α : Type} [Rep α] {t s : List α} (h : t <:+ s) :
    (enc t).length ≤ (enc s).length := by
  obtain ⟨pre, rfl⟩ := h
  have := enc_append_length pre t
  have := length_enc_pos pre
  omega

theorem length_le_enc_str (s : Str) : s.length ≤ (enc s).length := by
  have := length_lt_enc_list s; omega

theorem foldS_natStep_spec : ∀ (s : Str) (n : ℕ) (acc : Str), ∃ t, t <:+ s ∧
    (foldS natStep (false, n, acc) s).2.2 = acc ++ t ∧
      (foldS natStep (false, n, acc) s).2.1 ≤ n + s.length
  | [], n, acc => ⟨[], List.suffix_refl _, by simp [foldS], by simp [foldS]⟩
  | true :: s, n, acc => by
    obtain ⟨t, ht, e, hn⟩ := foldS_natStep_spec s (n + 1) acc
    refine ⟨t, ht.trans (List.suffix_cons true s), ?_, ?_⟩
    · simpa [foldS, natStep] using e
    · simp only [foldS, List.foldl_cons, List.length_cons] at hn ⊢
      rw [show natStep ((false, n, acc), true) = (false, n + 1, acc) from rfl]; omega
  | false :: s, n, acc => by
    have e := foldS_natStep_done n acc s
    refine ⟨s, List.suffix_cons false s, ?_, ?_⟩
    · simp only [foldS, List.foldl_cons] at e ⊢
      rw [show natStep ((false, n, acc), false) = (true, n, acc) from rfl, e]
    · simp only [foldS, List.foldl_cons] at e ⊢
      rw [show natStep ((false, n, acc), false) = (true, n, acc) from rfl, e]; simp

theorem pNat_bound : ParserB pNat (2 * Polynomial.X + 1) := by
  intro s
  obtain ⟨t, ht, e, hn⟩ := foldS_natStep_spec s 0 []
  have := length_le_enc_str s
  refine ⟨?_, ?_⟩
  · simp only [pNat, enc_nat_length, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    omega
  · simpa [pNat, e] using ht

/-! ### Lists of items -/

variable {α : Type} [Rep α]

/-- One item of a list parser. -/
def listStep (p : Str → α × Str) (q : (List α × Str) × Unit) : List α × Str :=
  (q.1.1 ++ [(p q.1.2).1], (p q.1.2).2)

/-- A length, then that many items. -/
def pList (p : Str → α × Str) (s : Str) : List α × Str :=
  foldS (listStep p) ([], (pNat s).2) (List.replicate (pNat s).1 ())

omit [Rep α] in
theorem foldS_listStep {f : α → Str} (p : Str → α × Str) (hp : ∀ a r, p (f a ++ r) = (a, r))
    (r : Str) : ∀ (l acc : List α),
    foldS (listStep p) (acc, (l.map f).flatten ++ r) (List.replicate l.length ()) = (acc ++ l, r)
  | [], acc => by simp [foldS]
  | a :: l, acc => by
    simp only [List.length_cons, List.replicate_succ, foldS, List.foldl_cons, List.map_cons,
      List.flatten_cons, List.append_assoc]
    rw [show listStep p ((acc, f a ++ ((l.map f).flatten ++ r)), ()) =
      (acc ++ [a], (l.map f).flatten ++ r) by simp [listStep, hp]]
    have := foldS_listStep p hp r l (acc ++ [a])
    simp only [foldS] at this
    rw [this]; simp

omit [Rep α] in
theorem pList_encList {f : α → Str} (p : Str → α × Str) (hp : ∀ a r, p (f a ++ r) = (a, r))
    (l : List α) (r : Str) : pList p (encList f l ++ r) = (l, r) := by
  simp only [pList, encList, List.append_assoc, pNat_encNat]
  simpa using foldS_listStep p hp r l []

theorem foldS_listStep_bound (p : Str → α × Str) (P : Polynomial ℕ) (hp : ParserB p P) :
    ∀ (m : ℕ) (acc : List α) (r : Str),
    (enc (foldS (listStep p) (acc, r) (List.replicate m ())).1).length ≤
        (enc acc).length + m * (P.eval (enc r).length + 1) ∧
      (foldS (listStep p) (acc, r) (List.replicate m ())).2 <:+ r
  | 0, acc, r => by simp [foldS]
  | m + 1, acc, r => by
    simp only [List.replicate_succ, foldS, List.foldl_cons]
    obtain ⟨h₁, h₂⟩ := hp r
    obtain ⟨h₃, h₄⟩ := foldS_listStep_bound p P hp m (acc ++ [(p r).1]) (p r).2
    simp only [foldS] at h₃ h₄
    refine ⟨?_, h₄.trans h₂⟩
    have h₅ := enc_append_length acc [(p r).1]
    have h₆ := ShiQIP.TMComp.eval_mono P (enc_suffix_le h₂)
    simp only [enc_cons_length, enc_nil, List.length_cons, List.length_nil] at h₅
    have h₇ := Nat.mul_le_mul_left m (Nat.add_le_add_right h₆ 1)
    rw [show listStep p ((acc, r), ()) = (acc ++ [(p r).1], (p r).2) from rfl]
    nlinarith

theorem pList_bound (p : Str → α × Str) (P : Polynomial ℕ) (hp : ParserB p P) :
    ParserB (pList p) (Polynomial.X * (P + 1) + 2 * Polynomial.X + 2) := by
  intro s
  obtain ⟨h₁, h₂⟩ := pNat_bound s
  obtain ⟨h₃, h₄⟩ := foldS_listStep_bound p P hp (pNat s).1 [] (pNat s).2
  refine ⟨?_, h₄.trans h₂⟩
  have h₅ := ShiQIP.TMComp.eval_mono P (enc_suffix_le h₂)
  have h₆ : (pNat s).1 ≤ (enc s).length := by
    have := h₁; simp only [enc_nat_length, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one] at this; omega
  have h₇ := Nat.mul_le_mul h₆ (Nat.add_le_add_right h₅ 1)
  simp only [pList, enc_nil, List.length_cons, List.length_nil] at h₃ ⊢
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  nlinarith

theorem PT.listStepU {p : Str → α × Str} (hp : PT p) : PT (listStep p) := by
  unfold listStep; fun_prop

theorem PT.pListU {p : Str → α × Str} {P : Polynomial ℕ} (hpt : PT p) (hp : ParserB p P) :
    PT (pList p) := by
  refine PT.foldl_gen (s := fun s => (([] : List α), (pNat s).2))
    (xs := fun s => List.replicate (pNat s).1 ()) (PT.listStepU hpt) (by fun_prop) (by fun_prop)
    ⟨Polynomial.X * (P + 1) + 3 * Polynomial.X + 3, fun s k => ?_⟩
  rw [List.take_replicate]
  obtain ⟨h₁, h₂⟩ := pNat_bound s
  obtain ⟨h₃, h₄⟩ := foldS_listStep_bound p P hp (min k (pNat s).1) [] (pNat s).2
  have h₅ := ShiQIP.TMComp.eval_mono P (enc_suffix_le h₂)
  have h₆ : (pNat s).1 ≤ (enc s).length := by
    have := h₁; simp only [enc_nat_length, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one] at this; omega
  have h₇ := Nat.mul_le_mul (le_trans (min_le_right k _) h₆) (Nat.add_le_add_right h₅ 1)
  have h₈ := enc_suffix_le (h₄.trans h₂)
  rw [enc_prod_length]
  simp only [enc_nil, List.length_cons, List.length_nil] at h₃
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  nlinarith

/-! ### Messages, gates, descriptions -/

/-- Parse a message. -/
def pMsg (s : Str) : Message × Str :=
  (⟨Dir.ofB (s.headD false), (pNat s.tail).1⟩, (pNat s.tail).2)

/-- Parse a gate. -/
def pGate (s : Str) : Gate × Str :=
  if (pNat s).1 = 4 then
    (Gate.cnot (pNat (pNat s).2).1 (pNat (pNat (pNat s).2).2).1, (pNat (pNat (pNat s).2).2).2)
  else (Gate.ofCd ((pNat s).1, (pNat (pNat s).2).1, 0), (pNat (pNat s).2).2)

/-- Parse a description. -/
def pDesc (s : Str) : Desc × Str :=
  (⟨(pNat s).1, (pNat (pNat s).2).1, (pList pMsg (pNat (pNat s).2).2).1,
    (pList (pList pGate) (pList pMsg (pNat (pNat s).2).2).2).1⟩,
    (pList (pList pGate) (pList pMsg (pNat (pNat s).2).2).2).2)

/-- **The total decoder.** -/
def dec (s : Str) : Desc := (pDesc s).1

theorem pMsg_encMsg (m : Message) (r : Str) : pMsg (encMsg m ++ r) = (m, r) := by
  rcases m with ⟨d, w⟩
  simp only [pMsg, encMsg, encDir_eq, List.cons_append, List.nil_append,
    List.headD_cons, List.tail_cons, pNat_encNat, Dir.ofB_toB]

theorem pGate_encGate (g : Gate) (r : Str) : pGate (encGate g ++ r) = (g, r) := by
  cases g <;> simp [pGate, encGate, List.append_assoc, pNat_encNat, Gate.ofCd]

theorem dec_encode (d : Desc) : dec (encode d) = d := by
  rcases d with ⟨a, b, ms, bs⟩
  have h₁ : pList pMsg (encList encMsg ms ++ encList encBlock bs) = (ms, encList encBlock bs) :=
    pList_encList pMsg pMsg_encMsg ms _
  have h₂ : pList (pList pGate) (encList encBlock bs ++ []) = (bs, []) :=
    pList_encList (pList pGate) (fun b r => pList_encList pGate pGate_encGate b r) bs []
  rw [List.append_nil] at h₂
  simp only [dec, pDesc, encode, List.append_assoc, pNat_encNat, h₁, h₂]

theorem PT.pMsgU : PT pMsg := by unfold pMsg; fun_prop

theorem PT.pGateU : PT pGate := by unfold pGate; fun_prop

theorem pMsg_bound : ParserB pMsg (2 * Polynomial.X + 5) := by
  intro s
  obtain ⟨h₁, h₂⟩ := pNat_bound s.tail
  have h₃ := enc_tail_le s
  have h₄ := enc_bool_length (s.headD false)
  refine ⟨?_, h₂.trans (List.tail_suffix s)⟩
  show (enc (Dir.ofB (s.headD false), (pNat s.tail).1)).length ≤ _
  rw [enc_pair_length]
  have : (enc (Dir.ofB (s.headD false))).length ≤ 3 := by
    show (enc (Dir.ofB (s.headD false)).toB).length ≤ 3; exact enc_bool_length _
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one] at h₁ ⊢
  omega

theorem enc_gate_length (g : Gate) : (enc g).length = (enc g.cd).length := rfl

theorem enc_ofCd_le (c : ℕ × (ℕ × ℕ)) :
    (enc (Gate.ofCd c)).length ≤ (enc c.2.1).length + (enc c.2.2).length + 11 := by
  rcases c with ⟨t, i, j⟩
  unfold Gate.ofCd
  split_ifs <;> simp [enc_gate_length, Gate.cd, enc_pair_length, enc_nat_length] <;> omega

theorem pGate_bound : ParserB pGate (6 * Polynomial.X + 20) := by
  intro s
  obtain ⟨h₁, h₂⟩ := pNat_bound s
  obtain ⟨h₃, h₄⟩ := pNat_bound (pNat s).2
  obtain ⟨h₅, h₆⟩ := pNat_bound (pNat (pNat s).2).2
  have e₁ := enc_suffix_le h₂
  have e₂ := enc_suffix_le (h₄.trans h₂)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one] at h₁ h₃ h₅ ⊢
  unfold pGate
  split_ifs
  · refine ⟨?_, h₆.trans (h₄.trans h₂)⟩
    simp only [enc_gate_length, Gate.cd, enc_pair_length, enc_nat_length] at h₃ h₅ ⊢
    omega
  · refine ⟨?_, h₄.trans h₂⟩
    have := enc_ofCd_le ((pNat s).1, (pNat (pNat s).2).1, 0)
    simp only [enc_nat_length] at this h₃
    dsimp only
    omega

attribute [irreducible] pMsg pGate

@[fun_prop] theorem PT.fp_pMsg {α : Type} [Rep α] {f : α → Str} (hf : PT f) :
    PT fun x => pMsg (f x) := PT.comp hf PT.pMsgU

@[fun_prop] theorem PT.fp_pListMsg {α : Type} [Rep α] {f : α → Str} (hf : PT f) :
    PT fun x => pList pMsg (f x) := PT.comp hf (PT.pListU PT.pMsgU pMsg_bound)

theorem PT.pBlockU : PT (pList pGate) := PT.pListU PT.pGateU pGate_bound

@[fun_prop] theorem PT.fp_pListBlock {α : Type} [Rep α] {f : α → Str} (hf : PT f) :
    PT fun x => pList (pList pGate) (f x) :=
  PT.comp hf (PT.pListU PT.pBlockU (pList_bound pGate _ pGate_bound))

/-- **The decoder is polynomial time.** -/
theorem PT.decU : PT dec := by unfold dec pDesc; fun_prop

end ShiQIP.Uniform
