import QIP.Halve.Honest


/-!
# Q31 — perfect completeness of halving

If `value d = 1`, the halved description has value `1` (`value_halve_eq_one`). The honest halved
prover sends the state of an optimal clean unitary prover of `d` after block `n + 1` as the cut
state, then runs that prover forward (coin copy `0`) or backward (coin copy `1`) on the message
slots.
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped Kronecker

variable {d : Desc} {n : ℕ}

/-! ## An optimal clean unitary prover of `d` -/

section Optimal

variable (T : IsoStrategy (Reg d) (Reg d) d.numMsgs)

/-- In the clean run, a message to the prover reads `0` after its turn. -/
theorem clean_after_turn (hd : d.Valid) {i : ℕ} (hp : toProverAt d i) (x : Qubits d.totalWires)
    (μ : DilMem d (cleanT T)) {w : Fin d.totalWires} (hw : inReg d i w) (hx : x w = true) :
    tv i (dilU (cleanT T) i) (dRun d (DilMem d (cleanT T)) (dilU (cleanT T)) (dilateU (cleanT T)).init i) (x, μ) = 0 := by
  have hi := lt_of_toProverAt hp
  rw [← dRun_undo]
  refine kronH_vanish hd (not_held_of_dead (Nat.lt_succ_self i) hp hw) _ (fun x' μ' hx' => ?_) x μ hx
  rw [← pureRun_dilateU_dRun, pureRun_dilateU (cleanT T) (i + 1) (by omega)]
  simp only [embVec]
  refine Finset.sum_eq_zero fun ν _ => ?_
  obtain ⟨m, s⟩ := ν
  have hng : ¬ good (i + 1) x' s := fun hg => by
    rw [hg.1 w ⟨i, Nat.lt_succ_self i, hp, hw⟩] at hx'
    exact Bool.false_ne_true hx'
  rw [pureRun_clean T hd (i + 1) (by omega), if_neg hng, zero_mul, mul_zero]

end Optimal


/-! ## The honest halved prover -/

section HonestProver

variable {D : Type} [Fintype D] [DecidableEq D]

/-- The cut state request, column form. -/
noncomputable def colOf {X : Type} (v : X → ℂ) : Matrix X Unit ℂ := Matrix.of fun x _ => v x

theorem colOf_iso {X : Type} [Fintype X] (v : X → ℂ) (hv : ∑ x, ‖v x‖ ^ 2 = 1) : (colOf v)ᴴ * colOf v = 1 := by
  ext ⟨⟩ ⟨⟩
  simp only [colOf, mul_apply, conjTranspose_apply, of_apply, one_apply_eq]
  have : ∀ x, star (v x) * v x = ((‖v x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [this, ← Complex.ofReal_sum, hv, Complex.ofReal_one]

/-- **A unitary sending the fixed vector `e` to the unit vector `t`.** -/
theorem exists_unitary_send {X : Type} [Fintype X] [DecidableEq X] (e t : X → ℂ)
    (he : ∑ x, ‖e x‖ ^ 2 = 1) (ht : ∑ x, ‖t x‖ ^ 2 = 1) :
    ∃ U ∈ Matrix.unitaryGroup X ℂ, U *ᵥ e = t := by
  obtain ⟨U, hU, h⟩ := exists_unitary_ext (colOf e) (colOf t) (colOf_iso e he) (colOf_iso t ht)
  refine ⟨U, hU, funext fun x => ?_⟩
  have := congrFun (congrFun h x) ()
  simpa [colOf, mul_apply, mulVec, dotProduct] using this

end HonestProver

/-- **Perfect completeness of halving**, from a clean unitary prover of `d` accepting with
certainty. -/
theorem value_halve_eq_one_of {D : Type} [Fintype D] [DecidableEq D] (hd : d.Valid) (hn : 1 ≤ n)
    (hne : n % 2 = 0) (hsch : d.HasSchedule (2 * n + 1))
    (U : ∀ t, Matrix (Reg d t × D) (Reg d t × D) ℂ) (hU : ∀ t, U t ∈ Matrix.unitaryGroup _ ℂ) (ιd : D → ℂ)
    (hιd : ∑ μ, ‖ιd μ‖ ^ 2 = 1)
    (hclean : ∀ i, toProverAt d i → ∀ (x : Qubits d.totalWires) μ (w : Fin d.totalWires), inReg d i w →
      x w = true → tv i (U i) (dRun d D U ιd i) (x, μ) = 0)
    (hnorm : ∑ x, ∑ μ, ‖dRun d D U ιd (n + 1) (x, μ)‖ ^ 2 = 1)
    (hfwd : (∑ x, ∑ μ, if outBit d x then ‖dRun d D U ιd (2 * n + 1) (x, μ)‖ ^ 2 else 0) = 1) :
    value (halveDesc d n) = 1 := by
  have hm : d.numMsgs = 2 * n + 1 := Desc.numMsgs_of_hasSchedule hsch
  -- the honest halved prover
  set ι : Bool × D → ℂ := fun p => if p.1 then 0 else ιd p.2 with hι
  have hιn : ∑ p, ‖ι p‖ ^ 2 = 1 := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool]; simpa [hι] using hιd
  set e₀ : Reg (halveDesc d n) 0 × (Bool × D) → ℂ := fun p => if p.1 = (fun _ => false) then ι p.2 else 0
  set t₀ : Reg (halveDesc d n) 0 × (Bool × D) → ℂ :=
    fun p => if p.2.1 then 0 else dRun d D U ιd (n + 1) ((regOfE d n).symm p.1, p.2.2)
  have he₀ : ∑ p, ‖e₀ p‖ ^ 2 = 1 := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (fun _ => false)]
    · simpa [e₀] using hιn
    · intro r _ hr; simp [e₀, hr]
    · simp
  have ht₀ : ∑ p, ‖t₀ p‖ ^ 2 = 1 := by
    rw [Fintype.sum_prod_type, ← hnorm, ← Equiv.sum_comp (regOfE d n)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp [t₀]
  obtain ⟨A₀, hA₀, hA₀e⟩ := exists_unitary_send e₀ t₀ he₀ ht₀
  set A : ∀ k, Matrix (Reg (halveDesc d n) k × (Bool × D)) (Reg (halveDesc d n) k × (Bool × D)) ℂ :=
    fun k => if h : 1 ≤ k ∧ k ≤ n then honA d n D U k h.1 h.2 else
      if hk : k = 0 then cast (by subst hk; rfl) A₀ else 1 with hAdef
  have hA0 : A 0 = A₀ := by
    simp only [hAdef]
    rw [dif_neg (by omega), dif_pos trivial, cast_eq]
  have hA : ∀ k (hk1 : 1 ≤ k) (hkn : k ≤ n), A k = honA d n D U k hk1 hkn :=
    fun k hk1 hkn => by simp only [hAdef]; rw [dif_pos ⟨hk1, hkn⟩]
  have hAu : ∀ k, A k ∈ Matrix.unitaryGroup _ ℂ := by
    intro k
    by_cases h : 1 ≤ k ∧ k ≤ n
    · rw [hA k h.1 h.2, honA]
      refine Submonoid.mul_mem _ (ctl_mem (embU_mem _ _ _ (hU _)) (embU_mem _ _ _ ?_)) (pmat_mem _)
      rw [← star_eq_conjTranspose]; exact Unitary.star_mem (hU _)
    · by_cases hk : k = 0
      · subst hk; rw [hA0]; exact hA₀
      · simp only [hAdef]; rw [dif_neg h, dif_neg hk]; exact one_mem _
  have hξ : cutVec d n (A 0) ι = liftV d n false (dRun d D U ιd (n + 1)) := by
    funext ⟨x, ⟨c, μ⟩, β⟩
    have hc : ∀ p, cvec d n A₀ ι p = t₀ p := fun p => by
      rw [← hA₀e]
      simp only [cvec, mulVec, dotProduct, Fintype.sum_prod_type, e₀]
      rw [Finset.sum_eq_single (fun _ => false)]
      · simp
      · intro r _ hr; simp [hr]
      · simp
    have hr : (regOfE d n).symm (regOf d n x) = x := (regOfE d n).symm_apply_apply x
    simp only [cutVec, liftV, hA0, hc, t₀, hr]
    cases c <;> simp
  -- the run of the halved description
  obtain ⟨UF, hUFu, hUF⟩ := exists_UF (d := d) (n := n) A hAu
  obtain ⟨UB, hUBu, hUB, hUB0⟩ := exists_UB (d := d) (n := n) A hAu
  have hhalf := accept_hRun A ι UF UB hd hn hne hm hUF hUB hUB0
  rw [fwdP_honest hd hn hne hsch hm U ιd A hA ι hξ UF hUF,
    bwdP_honest hd hn hne hsch U hU ιd hιd hclean A hA ι hξ UB hUB hUB0] at hhalf
  rw [hfwd] at hhalf
  -- the honest halved prover as an isometric strategy
  let Th : IsoStrategy (Reg (halveDesc d n)) (Reg (halveDesc d n)) (halveDesc d n).numMsgs :=
    { M := fun _ => Bool × D
      init := ι
      init_density := (isDensity_pure_iff _).mpr hιn
      V := A
      V_iso := fun k _ => Matrix.mem_unitaryGroup_iff'.mp (hAu k) }
  have hrun : ∀ k, pureRun Th k = hRun d n (Bool × D) A ι k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pureRun, hRun, ← ih]; rfl
  have hTh : accept Th.toOp = 1 := by
    rw [accept_pureRun, accept_expect]
    have e : ∀ j, j = n + 1 → (∑ y, ∑ μ : Bool × D, if outBit (halveDesc d n) y then
        ‖pureRun Th j (y, μ)‖ ^ 2 else 0) = (1 / 2 : ℝ) * (1 + 1) := by
      rintro j rfl; rw [hrun, hhalf]
    rw [e _ (numMsgs_halveDesc d n)]
    norm_num
  exact le_antisymm (value_mem_Icc _).2 (hTh ▸ accept_le_value _ Th.toOp)


/-- **Perfect completeness of halving.** -/
theorem value_halve_eq_one (hd : d.Valid) (hn : 1 ≤ n) (hne : n % 2 = 0) (hsch : d.HasSchedule (2 * n + 1))
    (hv : value d = 1) : value (halveDesc d n) = 1 := by
  have hm : d.numMsgs = 2 * n + 1 := Desc.numMsgs_of_hasSchedule hsch
  obtain ⟨P, hP⟩ := value_attained d
  obtain ⟨T₁, hT₁⟩ := exists_isoProver P
  have hacc : accept (dilateU (cleanT T₁)).toOp = 1 := by
    rw [accept_dilateU, accept_clean T₁ hd, hT₁, hP, hv]
  refine value_halve_eq_one_of hd hn hne hsch (dilU (cleanT T₁)) (fun t => dilU_mem _) (dilateU (cleanT T₁)).init
    ((isDensity_pure_iff _).mp (dilateU (cleanT T₁)).init_density)
    (fun i hp x μ w hw hx => clean_after_turn T₁ hd hp x μ hw hx) ?_ ?_
  · rw [← pureRun_dilateU_dRun]; exact sum_norm_pureRun (dilateU (cleanT T₁)) (j := n + 1) (by omega)
  · rw [← hacc, accept_pureRun, accept_expect]
    have e : ∀ j, j = 2 * n + 1 → (∑ y, ∑ μ : DilMem d (cleanT T₁), if outBit d y then
        ‖pureRun (dilateU (cleanT T₁)) j (y, μ)‖ ^ 2 else 0) =
        ∑ x, ∑ μ, if outBit d x then ‖dRun d (DilMem d (cleanT T₁)) (dilU (cleanT T₁)) (dilateU (cleanT T₁)).init
          (2 * n + 1) (x, μ)‖ ^ 2 else 0 := by
      rintro j rfl; rw [pureRun_dilateU_dRun]
    exact (e _ hm).symm

end ShiQIP
