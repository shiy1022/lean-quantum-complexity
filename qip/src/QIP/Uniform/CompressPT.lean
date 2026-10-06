import QIP.Uniform.HalvePT


/-!
# Q37 — uniform iterated compression

* Code lengths: `hsize d ≤ |enc d| + 1` and `|enc d| ≤ 3 · serialSize d + 3`.
* `gHalve`: one halving step, guarded by `check`, `1 ≤ n`, `n` even and `n ≤ numMsgs`; on a
  description failing the guard it is the identity.
* `pw M`: the halving parameters `[2 ^ r, …, 2]` for `M = padM r`, by bounded doubling.
* `compG d = foldS gHalve d (pw d.numMsgs)`; `compG_eq`: on a valid description with schedule
  `padM r`, `compG d = compressR r d`; `PT.compG`.
-/

namespace ShiQIP.Uniform

open ShiQIP ShiQIP.Arith

/-! ### Code lengths of descriptions -/

theorem enc_list_length {α : Type} [Rep α] (l : List α) :
    (enc l).length = l.length + 1 + (l.map fun x => (enc x).length).sum := by
  induction l with
  | nil => simp [enc_nil]
  | cons a l ih => rw [enc_cons_length, ih]; simp; ring

theorem enc_desc_length (d : Desc) : (enc d).length = (2 * d.priv + 1) + (2 * d.out + 1) +
    (enc d.msgs).length + (enc d.blocks).length + 3 := by
  show (enc (d.priv, d.out, d.msgs, d.blocks)).length = _
  simp only [enc_pair_length, enc_nat_length]; ring

theorem enc_msg_length (m : Message) : 2 * m.width + 3 ≤ (enc m).length ∧
    (enc m).length ≤ 2 * m.width + 5 := by
  show 2 * m.width + 3 ≤ (enc (m.dir, m.width)).length ∧ (enc (m.dir, m.width)).length ≤ _
  rw [enc_pair_length, enc_nat_length]
  have h₁ : (enc m.dir).length ≤ 3 := enc_bool_length _
  have h₂ : 1 ≤ (enc m.dir).length := length_enc_pos _
  omega

theorem enc_gate_bounds (g : Gate) : g.encLen ≤ (enc g).length ∧
    (enc g).length ≤ 2 * g.encLen + 1 := by
  cases g <;> simp [enc_gate_length, Gate.cd, enc_pair_length, enc_nat_length, Gate.encLen] <;>
    omega

theorem sum_map_le_sum_map {α : Type} (l : List α) (f g : α → ℕ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := List.sum_le_sum (by simpa using h)

theorem sum_two_encLen (b : List Gate) :
    (b.map fun g => 2 * g.encLen + 1).sum = 2 * (b.map Gate.encLen).sum + b.length := by
  induction b with
  | nil => simp
  | cons g b ih => simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

theorem sum_width_add_length (ms : List Message) :
    (ms.map Message.width).sum + ms.length ≤ (ms.map fun m => m.width + 2).sum := by
  induction ms with
  | nil => simp
  | cons m ms ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

/-- The serial size is at most the tree-code length. -/
theorem serialSize_le_enc (d : Desc) : d.serialSize ≤ (enc d).length := by
  rw [enc_desc_length, enc_list_length, enc_list_length]
  unfold Desc.serialSize
  have h₁ : (d.msgs.map fun m => m.width + 2).sum ≤ (d.msgs.map fun m => (enc m).length).sum :=
    sum_map_le_sum_map _ _ _ fun m _ => by have := (enc_msg_length m).1; omega
  have h₂ : (d.blocks.map fun b => b.length + 1 + (b.map Gate.encLen).sum).sum ≤
      (d.blocks.map fun b => (enc b).length).sum :=
    sum_map_le_sum_map _ _ _ fun b _ => by
      rw [enc_list_length]
      have := sum_map_le_sum_map b Gate.encLen (fun g => (enc g).length) fun g _ =>
        (enc_gate_bounds g).1
      omega
  omega

/-- The tree-code length is at most three times the serial size, plus three. -/
theorem enc_le_serialSize (d : Desc) : (enc d).length ≤ 3 * d.serialSize + 3 := by
  rw [enc_desc_length, enc_list_length, enc_list_length]
  unfold Desc.serialSize
  have h₁ : (d.msgs.map fun m => (enc m).length).sum ≤ 3 * (d.msgs.map fun m => m.width + 2).sum := by
    rw [← List.sum_map_mul_left]
    exact sum_map_le_sum_map _ _ _ fun m _ => by have := (enc_msg_length m).2; omega
  have h₂ : (d.blocks.map fun b => (enc b).length).sum ≤
      3 * (d.blocks.map fun b => b.length + 1 + (b.map Gate.encLen).sum).sum := by
    rw [← List.sum_map_mul_left]
    refine sum_map_le_sum_map _ _ _ fun b _ => ?_
    rw [enc_list_length]
    have := sum_map_le_sum_map b (fun g => (enc g).length) (fun g => 2 * g.encLen + 1) fun g _ =>
      (enc_gate_bounds g).2
    have e := sum_two_encLen b
    omega
  omega

/-- The size measure is at most the tree-code length plus one. -/
theorem hsize_le_enc (d : Desc) : hsize d ≤ (enc d).length + 1 := by
  have := serialSize_le_enc d
  unfold hsize Desc.gateCount Desc.totalWires Desc.numMsgs
  unfold Desc.serialSize at this
  have h₁ : (d.blocks.map List.length).sum ≤
      (d.blocks.map fun b => b.length + 1 + (b.map Gate.encLen).sum).sum :=
    sum_map_le_sum_map _ _ _ fun b _ => by omega
  have h₂ := sum_width_add_length d.msgs
  omega

/-- The tree-code length of a valid description is polynomial in its size measure. -/
theorem enc_le_hsize {d : Desc} (h : d.Valid) :
    (enc d).length ≤ 3 * ((hsize d + 3) * (2 * hsize d + 8)) + 3 := by
  have h₁ := enc_le_serialSize d
  have h₂ := Desc.serialSize_le h
  have h₃ : d.gateCount + d.numMsgs + 3 ≤ hsize d + 3 := by unfold hsize; omega
  have h₄ : 2 * d.totalWires + 8 ≤ 2 * hsize d + 8 := by unfold hsize; omega
  have := Nat.mul_le_mul h₃ h₄
  omega

/-! ### Guarded halving and the parameter list -/

/-- The guard of one halving step. -/
def hGuard (d : Desc) (n : ℕ) : Bool :=
  d.check && (decide (1 ≤ n) && (decide (n % 2 = 0) && decide (n ≤ d.numMsgs)))

/-- One guarded halving step. -/
def gHalve (q : Desc × ℕ) : Desc := if hGuard q.1 q.2 then halveDesc q.1 q.2 else q.1

theorem PT.gHalveU : PT gHalve := by unfold gHalve hGuard; fun_prop

/-- One doubling step of the parameter list, with the bound `M` kept in the state. -/
def pwStep (q : (ℕ × (ℕ × List ℕ)) × Unit) : ℕ × (ℕ × List ℕ) :=
  (q.1.1, if 2 * q.1.2.1 + 1 ≤ q.1.1 then (2 * q.1.2.1, q.1.2.1 :: q.1.2.2) else q.1.2)

/-- The halving parameters below `M`. -/
def pw (M : ℕ) : List ℕ := (foldS pwStep (M, (2, [])) (List.replicate M ())).2.2

/-- `[2 ^ r, …, 2]`. -/
def powList : ℕ → List ℕ
  | 0 => []
  | r + 1 => 2 ^ (r + 1) :: powList r

theorem pw_pre (r : ℕ) : ∀ k ≤ r, foldS pwStep (padM r, (2, [])) (List.replicate k ()) =
    (padM r, (2 ^ (k + 1), powList k)) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [List.replicate_succ', foldS_append, ih (by omega)]
    have : 2 * 2 ^ (k + 1) + 1 ≤ padM r := by
      unfold padM
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show k + 2 ≤ r + 1 by omega)
      rw [pow_succ] at this ⊢; omega
    simp only [foldS, List.foldl_cons, List.foldl_nil, pwStep, if_pos this, powList]
    rw [pow_succ 2 (k + 1)]; ring_nf

theorem pw_post (r j : ℕ) : foldS pwStep (padM r, (2 ^ (r + 1), powList r)) (List.replicate j ()) =
    (padM r, (2 ^ (r + 1), powList r)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ', foldS_append, ih]
    have : ¬ 2 * 2 ^ (r + 1) + 1 ≤ padM r := by
      unfold padM; have : 0 < 2 ^ (r + 1) := by positivity
      omega
    simp only [foldS, List.foldl_cons, List.foldl_nil, pwStep, if_neg this]

theorem pw_padM (r : ℕ) : pw (padM r) = powList r := by
  have hr : r ≤ padM r := by
    unfold padM; have := Nat.lt_two_pow_self (n := r + 1); omega
  unfold pw
  conv_lhs => rw [show List.replicate (padM r) () = List.replicate r () ++
    List.replicate (padM r - r) () by rw [← List.replicate_add]; congr 1; omega]
  rw [foldS_append, pw_pre r r le_rfl, pw_post]

/-! ### The compression loop -/

/-- **Uniform compression**: guarded halvings with the parameters of the message count. -/
def compG (d : Desc) : Desc := foldS gHalve d (pw d.numMsgs)

theorem foldS_gHalve_powList : ∀ (r : ℕ) (d : Desc), d.Valid → d.HasSchedule (padM r) →
    foldS gHalve d (powList r) = compressR r d
  | 0, d, _, _ => rfl
  | r + 1, d, hd, hs => by
    have hm := Desc.numMsgs_of_hasSchedule hs
    have hpos : 1 ≤ 2 ^ (r + 1) := Nat.one_le_two_pow
    have hev : 2 ^ (r + 1) % 2 = 0 := by rw [pow_succ]; omega
    have hle : 2 ^ (r + 1) ≤ d.numMsgs := by
      rw [hm]; unfold padM; rw [pow_succ 2 (r + 1)]; omega
    have hg : hGuard d (2 ^ (r + 1)) = true := by
      unfold hGuard
      have : d.check = true := hd
      simp [this, hpos, hev, hle]
    have hs' : (halveDesc d (2 ^ (r + 1))).HasSchedule (padM r) := by
      have := hasSchedule_halveDesc (d := d) (n := 2 ^ (r + 1)) hev
      unfold padM; exact this
    simp only [powList, foldS, List.foldl_cons]
    rw [show gHalve (d, 2 ^ (r + 1)) = halveDesc d (2 ^ (r + 1)) by simp [gHalve, hg]]
    exact foldS_gHalve_powList r _ (halveDesc_valid hd hpos hev) hs'

/-- On a valid description with schedule `padM r`, `compG` is `r` halvings. -/
theorem compG_eq (r : ℕ) {d : Desc} (hd : d.Valid) (hs : d.HasSchedule (padM r)) :
    compG d = compressR r d := by
  unfold compG
  rw [Desc.numMsgs_of_hasSchedule hs, pw_padM]
  exact foldS_gHalve_powList r d hd hs

/-! ### Bounds -/

theorem pw_inv (M : ℕ) : ∀ k, let st := foldS pwStep (M, (2, [])) (List.replicate k ());
    st.1 = M ∧ st.2.1 = 2 ^ (st.2.2.length + 1) ∧ st.2.1 ≤ M + 2 ∧ (∀ x ∈ st.2.2, x ≤ M) ∧
      st.2.2.length ≤ k := by
  intro k
  induction k with
  | zero => simp [foldS]
  | succ k ih =>
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := ih
    rw [List.replicate_succ', foldS_append]
    set st := foldS pwStep (M, (2, [])) (List.replicate k ())
    obtain ⟨m, p, acc⟩ := st
    simp only at h₁ h₂ h₃ h₄ h₅
    subst h₁
    simp only [foldS, List.foldl_cons, List.foldl_nil, pwStep]
    split_ifs with h
    · dsimp only
      refine ⟨trivial, by rw [h₂, List.length_cons, pow_succ]; ring, by omega, ?_, by
        rw [List.length_cons]; omega⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · exact h₄ x hx
    · dsimp only
      exact ⟨trivial, h₂, h₃, h₄, by omega⟩

theorem pw_length (M : ℕ) : 2 ^ (pw M).length ≤ M + 1 := by
  obtain ⟨_, h₂, h₃, _, _⟩ := pw_inv M M
  unfold pw
  rw [h₂, pow_succ] at h₃
  omega

theorem PT.pwU : PT pw := by
  have h := PT.foldl_gen (s := fun M : ℕ => (M, ((2 : ℕ), ([] : List ℕ))))
    (xs := fun M => List.replicate M ()) (step := pwStep) (by unfold pwStep; fun_prop)
    (by fun_prop) PT.units ⟨Polynomial.X * Polynomial.X + 4 * Polynomial.X + 12, fun M k => by
      rw [List.take_replicate]
      obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := pw_inv M (min k M)
      set st := foldS pwStep (M, (2, [])) (List.replicate (min k M) ())
      obtain ⟨m, p, acc⟩ := st
      simp only at h₁ h₂ h₃ h₄ h₅ ⊢
      subst h₁
      have h₆ := enc_list_le acc (2 * m + 1) fun x hx => by rw [enc_nat_length]; have := h₄ x hx; omega
      have h₇ : acc.length * (2 * m + 1 + 1) ≤ m * (2 * m + 2) :=
        Nat.mul_le_mul (le_trans h₅ (min_le_right _ _)) le_rfl
      simp only [enc_pair_length, enc_nat_length, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat]
      nlinarith⟩
  exact (PT.fp_snd (PT.fp_snd h)).of_eq fun M => rfl

@[fun_prop] theorem PT.fp_pw {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) : PT fun x => pw (f x) :=
  PT.comp (f := f) (g := pw) hf PT.pwU

theorem gHalve_bound (d₀ : Desc) (ns : List ℕ) : ∀ k,
    (foldS gHalve d₀ (ns.take k) = d₀ ∨ (foldS gHalve d₀ (ns.take k)).Valid) ∧
      hsize (foldS gHalve d₀ (ns.take k)) ≤ 2010 ^ (min k ns.length) * hsize d₀ := by
  intro k
  induction k with
  | zero => simp [foldS]
  | succ k ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    rcases hx : ns[k]? with _ | n
    · have hk : ns.length ≤ k := by simpa using hx
      rw [List.take_of_length_le (by omega), min_eq_right (by omega)]
      rw [List.take_of_length_le hk] at ih₁ ih₂
      rw [min_eq_right hk] at ih₂
      exact ⟨ih₁, ih₂⟩
    · have hk : k < ns.length := by
        by_contra h; simp [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hx
      rw [foldS_take_succ gHalve d₀ ns k n hx, min_eq_left (by omega)]
      rw [min_eq_left (by omega)] at ih₂
      set st := foldS gHalve d₀ (ns.take k)
      unfold gHalve
      split_ifs with hg
      · simp only [hGuard, Bool.and_eq_true, decide_eq_true_eq] at hg
        obtain ⟨hc, h1, hev, hle⟩ := hg
        refine ⟨Or.inr (halveDesc_valid hc h1 hev), ?_⟩
        have := hsize_halveDesc_le st h1 hle
        rw [pow_succ]
        nlinarith
      · refine ⟨ih₁, ?_⟩
        have : 2010 ^ k ≤ 2010 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        nlinarith

theorem numMsgs_le_enc (d : Desc) : d.numMsgs ≤ (enc d).length := by
  have := length_lt_enc_list d.msgs
  rw [enc_desc_length]; unfold Desc.numMsgs; omega

/-- **Uniform compression is polynomial time.** -/
theorem PT.compGU : PT compG := by
  refine PT.foldl_gen (s := fun d : Desc => d) (xs := fun d => pw d.numMsgs) PT.gHalveU PT.id
    (by fun_prop) ⟨Polynomial.X + 3 * (((Polynomial.X + 1) ^ 12 + 3) *
      (2 * (Polynomial.X + 1) ^ 12 + 8)) + 3, fun d k => ?_⟩
  obtain ⟨h₁, h₂⟩ := gHalve_bound d (pw d.numMsgs) k
  set N := (enc d).length
  have hM := numMsgs_le_enc d
  have hL := pw_length d.numMsgs
  have hH := hsize_le_enc d
  have h2010 : 2010 ^ (min k (pw d.numMsgs).length) ≤ (N + 1) ^ 11 := by
    calc 2010 ^ (min k (pw d.numMsgs).length) ≤ 2010 ^ (pw d.numMsgs).length :=
          Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)
      _ ≤ (2 ^ 11) ^ (pw d.numMsgs).length := Nat.pow_le_pow_left (by norm_num) _
      _ = (2 ^ (pw d.numMsgs).length) ^ 11 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (N + 1) ^ 11 := Nat.pow_le_pow_left (by omega) _
  have hS : hsize (foldS gHalve d ((pw d.numMsgs).take k)) ≤ (N + 1) ^ 12 := by
    calc _ ≤ 2010 ^ (min k (pw d.numMsgs).length) * hsize d := h₂
      _ ≤ (N + 1) ^ 11 * (N + 1) := Nat.mul_le_mul h2010 hH
      _ = (N + 1) ^ 12 := by ring
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_one]
  rcases h₁ with e | hv
  · rw [e]; omega
  · have := enc_le_hsize hv
    have hm := Nat.mul_le_mul (Nat.add_le_add_right hS 3)
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hS) 8)
    omega

@[fun_prop] theorem PT.fp_compG {α : Type} [Rep α] {f : α → Desc} (hf : PT f) :
    PT fun x => compG (f x) := PT.comp hf PT.compGU

end ShiQIP.Uniform
