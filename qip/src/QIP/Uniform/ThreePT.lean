import QIP.Uniform.CompressPT


/-!
# Q38/Q39 — uniform repetition and the uniform three-message printer

* `repG (d, K)`: `K - 1` guarded pairings of `d` with the running copy; on a valid `d` it is
  `parRepeat d K` (`repG_eq`); `PT.repGU`.
* `threeG d`: normalization, perfect completeness, padding, uniform compression, uniform
  repetition; on a valid `d` it is `threeDesc d` (`threeG_eq`); `PT.threeGU`.
* `printer s = encode (threeG (dec s))`: **`printer (encode d) = encode (threeDesc d)`** for valid
  `d`, and `printer` is `PvsNP.PolyTimeComputable` (`printer_polyTime`).
-/

namespace ShiQIP.Uniform

open ShiQIP ShiQIP.Arith

/-! ### Uniform repetition -/

/-- One guarded pairing step: the state is `(d, copies so far)`. -/
def rStep (q : (Desc × Desc) × Unit) : Desc × Desc :=
  (q.1.1, if q.1.1.check then pairDesc q.1.1 q.1.2 else q.1.2)

/-- `K` copies of `d` (if `d` is valid). -/
def repG (p : Desc × ℕ) : Desc := (foldS rStep (p.1, p.1) (List.replicate (p.2 - 1) ())).2

theorem foldS_rStep_valid {d : Desc} (hd : d.Valid) (j : ℕ) : ∀ k,
    foldS rStep (d, repeatAux d j) (List.replicate k ()) = (d, repeatAux d (j + k)) := by
  intro k
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    simp only [foldS, List.foldl_cons] at ih ⊢
    rw [show rStep ((d, repeatAux d j), ()) = (d, repeatAux d (j + 1)) by
      simp [rStep, show d.check = true from hd, repeatAux], ih (j + 1)]
    congr 2; ring

theorem foldS_rStep_invalid {d : Desc} (hd : d.check = false) (e : Desc) : ∀ k,
    foldS rStep (d, e) (List.replicate k ()) = (d, e) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    simp only [foldS, List.foldl_cons] at ih ⊢
    rw [show rStep ((d, e), ()) = (d, e) by simp [rStep, hd], ih]

theorem repG_eq {d : Desc} (hd : d.Valid) (K : ℕ) : repG (d, K) = parRepeat d K := by
  unfold repG parRepeat
  have := foldS_rStep_valid hd 0 (K - 1)
  rw [show repeatAux d 0 = d from rfl] at this
  simp only at this ⊢
  rw [this, zero_add]

theorem hsize_repeatAux_le {d : Desc} (hd : d.Valid) (k : ℕ) :
    hsize (repeatAux d k) ≤ (k + 1) * (hsize d + 34) := by
  have h1 := gateCount_repeatAux hd k
  have h2 := totalWires_repeatAux d k
  have h3 := numMsgs_repeatAux d k
  unfold hsize
  rw [h1, h2, h3]
  nlinarith

theorem PT.repGU : PT repG := by
  have h := PT.foldl_gen (s := fun p : Desc × ℕ => (p.1, p.1))
    (xs := fun p => List.replicate (p.2 - 1) ()) (step := rStep) (by unfold rStep; fun_prop)
    (by fun_prop) (by fun_prop)
    ⟨2 * Polynomial.X + 3 * ((((Polynomial.X + 1) * (Polynomial.X + 36)) + 3) *
      (2 * ((Polynomial.X + 1) * (Polynomial.X + 36)) + 8)) + 4, fun ⟨d, K⟩ k => by
      rw [List.take_replicate]
      simp only
      have hdN : (enc d).length + 1 ≤ (enc (d, K)).length := by rw [enc_pair_length]; omega
      have hKN : K ≤ (enc (d, K)).length := by rw [enc_pair_length, enc_nat_length]; omega
      set N := (enc (d, K)).length
      rw [enc_prod_length]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
        Polynomial.eval_one]
      by_cases hc : d.check = true
      · have hd : d.Valid := hc
        have e := foldS_rStep_valid hd 0 (min k (K - 1))
        rw [show repeatAux d 0 = d from rfl, zero_add] at e
        rw [e]
        have hv := enc_le_hsize (repeatAux_valid hd (min k (K - 1)))
        have hs := hsize_repeatAux_le hd (min k (K - 1))
        have hH := hsize_le_enc d
        have hk : min k (K - 1) + 1 ≤ N + 1 := by omega
        have h₁ : hsize (repeatAux d (min k (K - 1))) ≤ (N + 1) * (N + 36) := by
          calc _ ≤ (min k (K - 1) + 1) * (hsize d + 34) := hs
            _ ≤ (N + 1) * (N + 36) := Nat.mul_le_mul hk (by omega)
        have hm := Nat.mul_le_mul (Nat.add_le_add_right h₁ 3)
          (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h₁) 8)
        dsimp only
        omega
      · rw [foldS_rStep_invalid (by simpa using hc)]
        dsimp only
        omega⟩
  exact (PT.fp_snd h).of_eq fun p => rfl

@[fun_prop] theorem PT.fp_repG {α : Type} [Rep α] {f : α → Desc} {g : α → ℕ} (hf : PT f)
    (hg : PT g) : PT fun x => repG (f x, g x) :=
  PT.comp (f := fun x => (f x, g x)) (g := repG) (PT.pair hf hg) PT.repGU

/-! ### The uniform pipeline -/

/-- **The uniform three-message transformation.** -/
noncomputable def threeG (d : Desc) : Desc :=
  repG (compG (padTo (perfDesc (normDesc d))), repK (padCount (perfDesc (normDesc d)).numMsgs))

@[fun_prop] theorem PT.fp_sq {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) :
    PT fun x => f x ^ 2 := (PT.fp_mul hf hf).of_eq fun _ => (sq _).symm

@[fun_prop] theorem PT.fp_repK {α : Type} [Rep α] {f : α → ℕ} (hf : PT f) :
    PT fun x => repK (f x) := by unfold repK; fun_prop

theorem PT.threeGU : PT threeG := by unfold threeG; fun_prop

theorem padStage_spec {d : Desc} (hd : d.Valid) :
    (padTo (perfDesc (normDesc d))).Valid ∧
      (padTo (perfDesc (normDesc d))).HasSchedule (padM (pipeExp d)) := by
  obtain ⟨hv1, hs1, hk1, -, -, -, -⟩ := normDesc_spec hd
  have hv2 := perfDesc_valid hv1 hs1 hk1
  have hs2 := hasSchedule_perfDesc hs1 hk1
  have hm2 : (perfDesc (normDesc d)).numMsgs = (normDesc d).numMsgs + 2 :=
    Desc.numMsgs_of_hasSchedule hs2
  refine ⟨padTo_valid hv2 hs2, ?_⟩
  have := hasSchedule_padTo hs2
  rwa [show padCount ((normDesc d).numMsgs + 2) = padM (pipeExp d) by rw [pipeExp, hm2]; rfl] at this

/-- On valid descriptions the uniform transformation is the pipeline of `QIP.Pipeline`. -/
theorem threeG_eq {d : Desc} (hd : d.Valid) : threeG d = threeDesc d := by
  obtain ⟨hv, hs⟩ := padStage_spec hd
  have hc : compG (padTo (perfDesc (normDesc d))) = compDesc d := compG_eq _ hv hs
  unfold threeG threeDesc
  rw [hc, show padCount (perfDesc (normDesc d)).numMsgs = padM (pipeExp d) from rfl]
  exact repG_eq (compDesc_spec hd).1 _

/-! ### The printer -/

/-- **The printer**: decode, transform, encode. -/
noncomputable def printer (s : Str) : Str := encode (threeG (dec s))

theorem printer_encode {d : Desc} (hd : d.Valid) : printer (encode d) = encode (threeDesc d) := by
  rw [printer, dec_encode, threeG_eq hd]

theorem PT.printerU : PT printer := by
  have h₁ := PT.decU
  have h₂ := PT.threeGU
  have h₃ := PT.encodeU
  unfold printer
  fun_prop

/-- **The printer is polynomial-time computable.** -/
theorem printer_polyTime : PvsNP.PolyTimeComputable printer := polyTimeComputable_of_PT PT.printerU

end ShiQIP.Uniform
