import QIP.Uniform.GatePT
import QIP.Pipeline


/-!
# Q35/Q36 — the description transformers before compression are polynomial time

Pairing (`pairDesc`), the flag game and `rejectDesc`, schedule normalization (`normDesc`), the
Bell test (`bellDesc`, `perfDesc`), and padding (`padDesc`, `padTo`, with the padded count
computed by a bounded doubling loop).
-/

namespace ShiQIP.Uniform

open ShiQIP ShiQIP.Arith

/-! ### Pairing -/

@[fun_prop] theorem PT.fp_pairMsgs {α : Type} [Rep α] {a b : α → List Message} (ha : PT a)
    (hb : PT b) : PT fun x => pairMsgs (a x) (b x) := by unfold pairMsgs; fun_prop

@[fun_prop] theorem PT.fp_segs {α : Type} [Rep α] {d : α → Desc} (hd : PT d) :
    PT fun x => segs (d x) := by unfold segs; fun_prop

@[fun_prop] theorem PT.fp_pos₁ {α : Type} [Rep α] {d₁ d₂ : α → Desc} {v : α → ℕ} (h₁ : PT d₁)
    (h₂ : PT d₂) (hv : PT v) : PT fun x => pos₁ (d₁ x) (d₂ x) (v x) := by unfold pos₁; fun_prop

@[fun_prop] theorem PT.fp_pos₂ {α : Type} [Rep α] {d₁ d₂ : α → Desc} {v : α → ℕ} (h₁ : PT d₁)
    (h₂ : PT d₂) (hv : PT v) : PT fun x => pos₂ (d₁ x) (d₂ x) (v x) := by unfold pos₂; fun_prop

@[fun_prop] theorem PT.fp_pairBlock {α : Type} [Rep α] {d₁ d₂ : α → Desc} {j : α → ℕ} (h₁ : PT d₁)
    (h₂ : PT d₂) (hj : PT j) : PT fun x => pairBlock (d₁ x) (d₂ x) (j x) := by
  unfold pairBlock; fun_prop

@[fun_prop] theorem PT.fp_pairDesc {α : Type} [Rep α] {d₁ d₂ : α → Desc} (h₁ : PT d₁)
    (h₂ : PT d₂) : PT fun x => pairDesc (d₁ x) (d₂ x) := by unfold pairDesc; fun_prop

/-! ### The flag game -/

@[fun_prop] theorem PT.fp_flagWidths {α : Type} [Rep α] {m : α → ℕ} (hm : PT m) :
    PT fun x => flagWidths (m x) := by unfold flagWidths; fun_prop

@[fun_prop] theorem PT.fp_flagMsgs {α : Type} [Rep α] {ms : α → List Message} (hms : PT ms) :
    PT fun x => flagMsgs (ms x) := by unfold flagMsgs; fun_prop

@[fun_prop] theorem PT.fp_flagDesc {α : Type} [Rep α] {d : α → Desc} (hd : PT d) :
    PT fun x => flagDesc (d x) := by unfold flagDesc; fun_prop

@[fun_prop] theorem PT.fp_rejectDesc {α : Type} [Rep α] {d : α → Desc} (hd : PT d) :
    PT fun x => rejectDesc (d x) := by unfold rejectDesc; fun_prop

/-! ### Normalization -/

theorem decide_lastToVerifier (d : Desc) : decide (LastToVerifier d) =
    ((d.msgs.map Message.dir).getD (d.numMsgs - 1) .toVerifier).toB := by
  unfold LastToVerifier
  have key : ∀ x : Dir, decide (x = .toVerifier) = x.toB := by intro x; cases x <;> rfl
  convert key _

@[fun_prop] theorem PT.fp_lastToVerifier {α : Type} [Rep α] {d : α → Desc} (hd : PT d) :
    PT fun x => decide (LastToVerifier (d x)) :=
  (show PT fun x => (((d x).msgs.map Message.dir).getD ((d x).numMsgs - 1) .toVerifier).toB by
    fun_prop).of_eq fun x => (decide_lastToVerifier _).symm

@[fun_prop] theorem PT.fp_appendV {α : Type} [Rep α] {d : α → Desc} (hd : PT d) :
    PT fun x => appendV (d x) := by unfold appendV; fun_prop

@[fun_prop] theorem PT.fp_normDesc {α : Type} [Rep α] {d : α → Desc} (hd : PT d) :
    PT fun x => normDesc (d x) := by unfold normDesc; fun_prop

/-! ### The Bell test -/

@[fun_prop] theorem PT.fp_bellShift {α : Type} [Rep α] {d : α → Desc} {v : α → ℕ} (hd : PT d)
    (hv : PT v) : PT fun x => bellShift (d x) (v x) := by unfold bellShift; fun_prop

@[fun_prop] theorem PT.fp_swapAll {α : Type} [Rep α] {d : α → Desc} (hd : PT d) :
    PT fun x => swapAll (d x) := by unfold swapAll bellMsgOff; fun_prop

@[fun_prop] theorem PT.fp_bellFinal {α : Type} [Rep α] {d : α → Desc} (hd : PT d) :
    PT fun x => bellFinal (d x) := by unfold bellFinal bellO bellB bellOut; fun_prop

@[fun_prop] theorem PT.fp_bellBlock {α : Type} [Rep α] {d : α → Desc} {j : α → ℕ} (hd : PT d)
    (hj : PT j) : PT fun x => bellBlock (d x) (j x) := by unfold bellBlock bellB; fun_prop

@[fun_prop] theorem PT.fp_bellDesc {α : Type} [Rep α] {d : α → Desc} (hd : PT d) :
    PT fun x => bellDesc (d x) := by unfold bellDesc; fun_prop

@[fun_prop] theorem PT.fp_perfDesc {α : Type} [Rep α] {d : α → Desc} (hd : PT d) :
    PT fun x => perfDesc (d x) := by unfold perfDesc; fun_prop

/-! ### The padded count, by bounded doubling -/

theorem foldS_append {α β : Type} (step : β × α → β) (s : β) (l₁ l₂ : List α) :
    foldS step s (l₁ ++ l₂) = foldS step (foldS step s l₁) l₂ := by
  simp [foldS, List.foldl_append]

/-- One doubling step, with the target `m` kept in the state. -/
def padStep (q : (ℕ × (ℕ × ℕ)) × Unit) : ℕ × (ℕ × ℕ) :=
  (q.1.1, if q.1.2.2 < q.1.1 then (q.1.2.1 + 1, 2 * q.1.2.2 - 1) else q.1.2)

/-- `m` doubling steps from `(0, padM 0)`. -/
def padRun (m : ℕ) : ℕ × (ℕ × ℕ) := foldS padStep (m, (0, 3)) (List.replicate m ())

theorem padM_succ' (k : ℕ) : padM (k + 1) = 2 * padM k - 1 := by
  unfold padM; rw [pow_succ]; omega

theorem padExp_le (m : ℕ) : padExp m ≤ m :=
  Nat.find_min' (exists_padExp m) (by have := Nat.lt_two_pow_self (n := m + 1); unfold padM; omega)

theorem padRun_pre (m : ℕ) : ∀ k ≤ padExp m,
    foldS padStep (m, (0, 3)) (List.replicate k ()) = (m, (k, padM k)) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [List.replicate_succ', foldS_append, ih (by omega)]
    have hlt : padM k < m := by
      have := Nat.find_min (exists_padExp m) (show k < padExp m by omega)
      omega
    simp only [foldS, List.foldl_cons, List.foldl_nil, padStep, if_pos hlt, padM_succ']

theorem padRun_post (m j : ℕ) :
    foldS padStep (m, (padExp m, padM (padExp m))) (List.replicate j ()) =
      (m, (padExp m, padM (padExp m))) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ', foldS_append, ih]
    have : ¬ padM (padExp m) < m := by have := le_padCount m; unfold padCount at this; omega
    simp only [foldS, List.foldl_cons, List.foldl_nil, padStep, if_neg this]

theorem padRun_eq (m : ℕ) : (padRun m).2 = (padExp m, padCount m) := by
  have h := padExp_le m
  unfold padRun
  conv_lhs => rw [show List.replicate m () = List.replicate (padExp m) () ++
    List.replicate (m - padExp m) () by rw [← List.replicate_add]; congr 1; omega]
  rw [foldS_append, padRun_pre m _ le_rfl, padRun_post]
  rfl

theorem padM_padExp_le (m : ℕ) : padM (padExp m) ≤ 2 * m + 3 := by
  rcases h : padExp m with _ | e
  · simp [padM]
  · have := Nat.find_min (exists_padExp m) (show e < padExp m by omega)
    rw [padM_succ']
    unfold padM at this ⊢
    omega

theorem PT.padRunU : PT padRun := by
  have h := PT.foldl_gen (s := fun m : ℕ => (m, ((0 : ℕ), (3 : ℕ))))
    (xs := fun m => List.replicate m ()) (step := padStep) (by unfold padStep; fun_prop)
    (by fun_prop) PT.units ⟨20 * Polynomial.X + 20, fun m k => by
      rw [List.take_replicate]
      have hb := padM_padExp_le m
      have he := padExp_le m
      have key : ∀ j, (enc (foldS padStep (m, (0, 3)) (List.replicate j ()))).length ≤
          8 * m + 15 := by
        intro j
        rcases le_or_gt j (padExp m) with hj | hj
        · rw [padRun_pre m j hj]
          have : padM j ≤ padM (padExp m) := by
            unfold padM; have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show j + 1 ≤ padExp m + 1 by omega); omega
          simp only [enc_pair_length, enc_nat_length]; omega
        · rw [show List.replicate j () = List.replicate (padExp m) () ++
            List.replicate (j - padExp m) () by rw [← List.replicate_add]; congr 1; omega,
            foldS_append, padRun_pre m _ le_rfl, padRun_post]
          simp only [enc_pair_length, enc_nat_length]; omega
      have := key (min k m)
      simp only [enc_nat_length, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      omega⟩
  exact h

@[fun_prop] theorem PT.fp_padExp {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) :
    PT fun x => padExp (f x) :=
  (show PT fun x => (padRun (f x)).2.1 from PT.fp_fst (PT.fp_snd (PT.comp hf PT.padRunU))).of_eq
    fun x => by rw [padRun_eq]

@[fun_prop] theorem PT.fp_padCount {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) :
    PT fun x => padCount (f x) :=
  (show PT fun x => (padRun (f x)).2.2 from PT.fp_snd (PT.fp_snd (PT.comp hf PT.padRunU))).of_eq
    fun x => by rw [padRun_eq]

/-! ### Padding -/

@[fun_prop] theorem PT.fp_dummyMsgs {α : Type} [Rep α] {m s : α → ℕ} (hm : PT m) (hs : PT s) :
    PT fun x => dummyMsgs (m x) (s x) := by unfold dummyMsgs; fun_prop

@[fun_prop] theorem PT.fp_padDesc {α : Type} [Rep α] {d : α → Desc} {s : α → ℕ} (hd : PT d)
    (hs : PT s) : PT fun x => padDesc (d x) (s x) := by unfold padDesc; fun_prop

@[fun_prop] theorem PT.fp_padTo {α : Type} [Rep α] {d : α → Desc} (hd : PT d) :
    PT fun x => padTo (d x) := by unfold padTo; fun_prop

end ShiQIP.Uniform
