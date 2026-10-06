import QIP.PadMessages


/-!
# Schedule normalization

A valid description alternates its messages, but may end with a message to the prover or have
no messages. `appendV d` appends one zero-width message to the verifier and an empty block. If
`d` has `m ≥ 1` messages and the last goes to the verifier, `d` already has the standard
`m`-message schedule (`hasSchedule_of_last`).
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped Kronecker

/-- Append a zero-width message to the verifier and an empty final block. -/
def appendV (d : Desc) : Desc where
  priv := d.priv
  out := d.out
  msgs := d.msgs ++ [⟨.toVerifier, 0⟩]
  blocks := d.blocks ++ [[]]

variable {d : Desc}

theorem numMsgs_appendV : (appendV d).numMsgs = d.numMsgs + 1 := by
  simp [appendV, Desc.numMsgs]

theorem totalWires_appendV : (appendV d).totalWires = d.totalWires := by
  simp [appendV, Desc.totalWires]

theorem alternates_cons_cons (a b : Message) (ms : List Message) :
    Desc.alternates (a :: b :: ms) = ((a.dir != b.dir) && Desc.alternates (b :: ms)) := rfl

/-- Alternation, read from the directions. -/
theorem alternates_iff_dirs : ∀ ms : List Message, Desc.alternates ms = true ↔
    ∀ i, i + 1 < ms.length → (ms.map Message.dir).getD i .toVerifier ≠ (ms.map Message.dir).getD (i + 1) .toVerifier
  | [] => by simp [Desc.alternates]
  | [_] => by simp [Desc.alternates]
  | a :: b :: ms => by
    rw [alternates_cons_cons, Bool.and_eq_true, alternates_iff_dirs (b :: ms)]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | zero => simpa using h1
      | succ i => simpa using h2 i (by simp at hi ⊢; omega)
    · intro h
      refine ⟨by simpa using h 0 (by simp), fun i hi => ?_⟩
      simpa using h (i + 1) (by simp at hi ⊢; omega)


/-! ## Wires and registers -/

theorem msgHeld_append_zero (j w : ℕ) : ∀ (ms : List Message) (k off : ℕ),
    msgHeld j w (ms ++ [⟨.toVerifier, 0⟩]) k off = msgHeld j w ms k off
  | [], k, off => by simp [msgHeld]
  | m :: ms, k, off => by simp only [List.cons_append, msgHeld, msgHeld_append_zero j w ms]

theorem held_appendV (j w : ℕ) : (appendV d).held j w = d.held j w := by
  unfold Desc.held
  rw [show (appendV d).msgs = d.msgs ++ [⟨.toVerifier, 0⟩] from rfl, msgHeld_append_zero]
  rfl

variable (d) in
/-- The wires of `appendV d` are those of `d`. -/
def eWA : Fin (appendV d).totalWires ≃ Fin d.totalWires := finCongr totalWires_appendV

variable (d) in
/-- Basis labels of `appendV d` are those of `d`. -/
def eQA : Qubits (appendV d).totalWires ≃ Qubits d.totalWires :=
  Equiv.arrowCongr (eWA d) (Equiv.refl Bool)

theorem eWA_val (w : Fin (appendV d).totalWires) : (eWA d w : ℕ) = w := rfl

theorem msgOffset_appendV {j : ℕ} (hj : j ≤ d.numMsgs) : (appendV d).msgOffset j = d.msgOffset j := by
  simp only [Desc.msgOffset, appendV]
  rw [List.take_append_of_le_length hj]

theorem msgWidth_appendV {j : ℕ} (hj : j < d.numMsgs) : (appendV d).msgWidth j = d.msgWidth j := by
  simp only [Desc.msgWidth, appendV, List.getElem?_append_left hj]

theorem msgWidth_appendV_last : (appendV d).msgWidth d.numMsgs = 0 := by
  simp [Desc.msgWidth, appendV, Desc.numMsgs]

theorem inReg_appendV {j : ℕ} (hj : j < d.numMsgs) (w : Fin (appendV d).totalWires) :
    inReg (appendV d) j w ↔ inReg d j (eWA d w) := by
  unfold inReg
  rw [msgOffset_appendV hj.le, msgWidth_appendV hj, eWA_val]

theorem not_inReg_appendV_last (w : Fin (appendV d).totalWires) : ¬ inReg (appendV d) d.numMsgs w := by
  unfold inReg; rw [msgWidth_appendV_last]; omega

variable (d) in
/-- Register `j < m` of `appendV d` is register `j` of `d`. -/
def τA {j : ℕ} (hj : j < d.numMsgs) : Reg (appendV d) j ≃ Reg d j :=
  Equiv.arrowCongr ((eWA d).subtypeEquiv fun w => inReg_appendV hj w) (Equiv.refl Bool)

theorem blocks_appendV_getD {j : ℕ} (hd : d.Valid) (hj : j ≤ d.numMsgs) :
    (appendV d).blocks.getD j [] = d.blocks.getD j [] := by
  have hl := hd.blocks_length
  have hj' : j ≤ d.msgs.length := hj
  simp only [appendV, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]

theorem blocks_appendV_last (hd : d.Valid) : (appendV d).blocks.getD (d.numMsgs + 1) [] = [] := by
  have hl := hd.blocks_length
  simp only [appendV, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [Desc.numMsgs] at hl ⊢; omega)]
  simp [Desc.numMsgs] at hl ⊢

theorem blockMat_appendV (hd : d.Valid) {j : ℕ} (hj : j ≤ d.numMsgs) :
    blockMat (appendV d) j = (blockMat d j).submatrix (eQA d) (eQA d) := by
  rw [blockMat, blocks_appendV_getD hd hj, layerMat_cast totalWires_appendV]
  rfl

theorem blockMat_appendV_last (hd : d.Valid) : blockMat (appendV d) (d.numMsgs + 1) = 1 := by
  rw [blockMat, blocks_appendV_last hd]
  rfl


/-! ## Dropping the final turn -/

section Rest

variable (hd : d.Valid) (T : IsoStrategy (Reg (appendV d)) (Reg (appendV d)) (appendV d).numMsgs)

/-- **The restricted prover**: the first `m` turns of a prover of `appendV d`. -/
@[reducible] noncomputable def restT : IsoStrategy (Reg d) (Reg d) d.numMsgs where
  M j := T.M j
  init := T.init
  init_density := T.init_density
  V j := if h : j < d.numMsgs then
      (T.V j).submatrix (Prod.map (τA d h).symm id) (Prod.map (τA d h).symm id) else 0
  V_iso j hj := by
    rw [dif_pos hj]
    exact iso_submatrix_equiv (T.V j) (T.V_iso j (by rw [numMsgs_appendV]; omega))
      ((τA d hj).symm.prodCongr (Equiv.refl _)) ((τA d hj).symm.prodCongr (Equiv.refl _))

theorem eQA_apply (y : Qubits (appendV d).totalWires) (v : Fin d.totalWires) :
    eQA d y v = y ((eWA d).symm v) := rfl

theorem split_τA {j : ℕ} (hj : j < d.numMsgs) (y : Qubits (appendV d).totalWires) :
    (τA d hj).symm (wireSplitE d j (eQA d y)).2 = (wireSplitE (appendV d) j y).2 := by
  rw [Equiv.symm_apply_eq]
  rfl

theorem regSet_τA {j : ℕ} (hj : j < d.numMsgs) (y : Qubits (appendV d).totalWires) (x : Reg (appendV d) j) :
    eQA d (PrefixData.regSet (appendV d) j y x) = PrefixData.regSet d j (eQA d y) (τA d hj x) := by
  funext v
  rw [eQA_apply, PrefixData.regSet_apply, PrefixData.regSet_apply]
  have hv : inReg (appendV d) j ((eWA d).symm v) ↔ inReg d j v := by
    rw [inReg_appendV hj, Equiv.apply_symm_apply]
  by_cases h : inReg d j v
  · rw [dif_pos (hv.mpr h), dif_pos h]
    rfl
  · rw [dif_neg (fun h' => h (hv.mp h')), dif_neg h, eQA_apply]

theorem turnVec_rest {j : ℕ} (hj : j < d.numMsgs) (v : Qubits (appendV d).totalWires × T.M j → ℂ)
    (v' : Qubits d.totalWires × (restT T).M j → ℂ) (hv : ∀ y ν, v (y, ν) = v' (eQA d y, ν))
    (y : Qubits (appendV d).totalWires) (ν' : T.M (j + 1)) :
    turnVec T j v (y, ν') = turnVec (restT T) j v' (eQA d y, ν') := by
  rw [PrefixData.turnVec_apply, PrefixData.turnVec_apply]
  refine Fintype.sum_equiv (τA d hj) _ _ fun x => Finset.sum_congr rfl fun ν _ => ?_
  change _ = (if h : j < d.numMsgs then (T.V j).submatrix (Prod.map (τA d h).symm id)
    (Prod.map (τA d h).symm id) else 0) ((wireSplitE d j (eQA d y)).2, ν') (τA d hj x, ν) * _
  rw [dif_pos hj]
  simp only [submatrix_apply, Prod.map_apply, id_eq]
  rw [split_τA, Equiv.symm_apply_apply, hv, regSet_τA]

theorem zeroVec_eQA (z : Qubits d.totalWires) :
    zeroVec (appendV d).totalWires ((eQA d).symm z) = zeroVec d.totalWires z := by
  simp only [zeroVec]
  congr 1
  apply propext
  constructor
  · intro h; funext v
    have := congrFun h ((eWA d).symm v)
    change z (eWA d ((eWA d).symm v)) = _ at this
    rw [Equiv.apply_symm_apply] at this
    exact this
  · intro h; funext w
    rw [h]; rfl

theorem kron_submatrix_mulVecA {M : Type} [Fintype M] [DecidableEq M]
    (B : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ)
    (f : Qubits (appendV d).totalWires × M → ℂ) (g : Qubits d.totalWires × M → ℂ)
    (hfg : ∀ y μ, f (y, μ) = g (eQA d y, μ)) (y : Qubits (appendV d).totalWires) (μ : M) :
    ((B.submatrix (eQA d) (eQA d) ⊗ₖ (1 : Matrix M M ℂ)) *ᵥ f) (y, μ) =
      ((B ⊗ₖ (1 : Matrix M M ℂ)) *ᵥ g) (eQA d y, μ) := by
  rw [kronOne_mulVec_apply, kronOne_mulVec_apply, submatrix_mulVec_equiv]
  have : (fun y' => f (y', μ)) ∘ (eQA d).symm = fun y' => g (y', μ) :=
    funext fun z => by simp only [Function.comp_apply, hfg, Equiv.apply_symm_apply]
  rw [Function.comp_apply, this]

include hd in
/-- **Up to block `m`, the run is the restricted run.** -/
theorem pureRun_rest : ∀ j ≤ d.numMsgs, ∀ y ν,
    pureRun T j (y, ν) = pureRun (restT T) j (eQA d y, ν)
  | 0, _, y, ν => by
    rw [pureRun, pureRun, blockMat_appendV hd (Nat.zero_le _)]
    refine kron_submatrix_mulVecA _ _ _ (fun y μ => ?_) y ν
    change zeroVec _ y * _ = zeroVec _ (eQA d y) * _
    rw [← zeroVec_eQA (eQA d y), Equiv.symm_apply_apply]
  | j + 1, hj, y, ν => by
    rw [pureRun, pureRun, blockMat_appendV hd hj]
    exact kron_submatrix_mulVecA _ _ _ (fun y μ => turnVec_rest T (by omega) _ _
      (fun y ν => pureRun_rest j (by omega) y ν) y μ) y ν

end Rest


section RestAccept

variable (hd : d.Valid) (T : IsoStrategy (Reg (appendV d)) (Reg (appendV d)) (appendV d).numMsgs)

theorem sum_norm_iso {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (W : Matrix A B ℂ) (hW : Wᴴ * W = 1) (u : B → ℂ) :
    ∑ a, ‖(W *ᵥ u) a‖ ^ 2 = ∑ b, ‖u b‖ ^ 2 := by
  have key : star (W *ᵥ u) ⬝ᵥ (W *ᵥ u) = star u ⬝ᵥ u := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hW, one_mulVec]
  have e : ∀ {X : Type} [Fintype X] (v : X → ℂ), star v ⬝ᵥ v = ((∑ x, ‖v x‖ ^ 2 : ℝ) : ℂ) := by
    intro X _ v
    rw [dotProduct, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, e] at key
  exact_mod_cast key

/-- The empty register of the appended message. -/
def zRegA : Reg (appendV d) d.numMsgs := fun _ => false

theorem regA_eq_zero (g : Reg (appendV d) d.numMsgs) : g = zRegA :=
  funext fun w => absurd w.2 (not_inReg_appendV_last w.1)

/-- The final, idle turn as a map on memories. -/
noncomputable def lastW : Matrix (T.M (d.numMsgs + 1)) (T.M d.numMsgs) ℂ :=
  Matrix.of fun ν' ν => T.V d.numMsgs (zRegA, ν') (zRegA, ν)

theorem lastW_iso : (lastW T)ᴴ * lastW T = 1 := by
  have hV := T.V_iso d.numMsgs (by rw [numMsgs_appendV]; omega)
  have : Subsingleton (Reg (appendV d) d.numMsgs) :=
    ⟨fun a b => (regA_eq_zero a).trans (regA_eq_zero b).symm⟩
  ext ν ν₂
  have := congrArg (fun M => M (zRegA, ν) (zRegA, ν₂)) hV
  simp only [mul_apply, conjTranspose_apply, Fintype.sum_prod_type, one_apply, Prod.mk.injEq,
    true_and] at this
  rw [Fintype.sum_subsingleton _ zRegA] at this
  simpa [mul_apply, lastW, one_apply] using this

theorem turnVec_last (v : Qubits (appendV d).totalWires × T.M d.numMsgs → ℂ)
    (y : Qubits (appendV d).totalWires) (ν' : T.M (d.numMsgs + 1)) :
    turnVec T d.numMsgs v (y, ν') = (lastW T *ᵥ fun ν => v (y, ν)) ν' := by
  have : Subsingleton (Reg (appendV d) d.numMsgs) :=
    ⟨fun a b => (regA_eq_zero a).trans (regA_eq_zero b).symm⟩
  rw [PrefixData.turnVec_apply, Fintype.sum_subsingleton _ zRegA,
    regA_eq_zero (wireSplitE _ d.numMsgs y).2,
    show PrefixData.regSet (appendV d) d.numMsgs y zRegA = y from funext fun w => by
      rw [PrefixData.regSet_apply, dif_neg (not_inReg_appendV_last w)]]
  rfl

theorem outBit_eQA (y : Qubits (appendV d).totalWires) : outBit (appendV d) y ↔ outBit d (eQA d y) := by
  constructor
  · rintro ⟨h, e⟩
    exact ⟨by rw [← totalWires_appendV (d := d)]; exact h, e⟩
  · rintro ⟨h, e⟩
    exact ⟨by rw [totalWires_appendV]; exact h, e⟩

include hd in
/-- **Dropping the idle final turn keeps the acceptance probability.** -/
theorem accept_restT : accept T.toOp = accept (restT T).toOp := by
  have hacc : ∀ k, k = (appendV d).numMsgs → accept T.toOp = (star (pureRun T k) ⬝ᵥ
      (acceptEffect (appendV d) (T.M k) *ᵥ pureRun T k)).re := by
    intro k hk; subst hk; exact accept_pureRun T
  rw [hacc _ numMsgs_appendV.symm, accept_pureRun, accept_expect, accept_expect]
  have hlast : ∀ y ν', pureRun T (d.numMsgs + 1) (y, ν') = (lastW T *ᵥ fun ν => pureRun T d.numMsgs (y, ν)) ν' := by
    intro y ν'
    rw [pureRun, blockMat_appendV_last hd, one_kronecker_one, one_mulVec, turnVec_last]
  refine Fintype.sum_equiv (eQA d) _ _ fun y => ?_
  by_cases h : outBit (appendV d) y
  · simp only [if_pos h, if_pos ((outBit_eQA y).mp h)]
    rw [show (∑ ν', ‖pureRun T (d.numMsgs + 1) (y, ν')‖ ^ 2) =
      ∑ ν', ‖(lastW T *ᵥ fun ν => pureRun T d.numMsgs (y, ν)) ν'‖ ^ 2 from
        Finset.sum_congr rfl fun ν' _ => by rw [hlast], sum_norm_iso _ (lastW_iso T)]
    exact Finset.sum_congr rfl fun ν _ => by rw [pureRun_rest hd T _ le_rfl]
  · simp only [if_neg h, if_neg (fun h' => h ((outBit_eQA y).mpr h'))]
    simp

end RestAccept


/-! ## Adding an idle final turn -/

section Ext

variable (T₀ : IsoStrategy (Reg d) (Reg d) d.numMsgs)

/-- The turns of the extended prover. -/
noncomputable def extV (i : ℕ) :
    Matrix (Reg (appendV d) i × T₀.M (min (i + 1) d.numMsgs)) (Reg (appendV d) i × T₀.M (min i d.numMsgs)) ℂ :=
  if h : i < d.numMsgs then
    (T₀.V i).submatrix (Prod.map (τA d h) (mCast T₀ (by omega))) (Prod.map (τA d h) (mCast T₀ (by omega)))
  else
    (1 : Matrix (Reg (appendV d) i × T₀.M (min i d.numMsgs)) (Reg (appendV d) i × T₀.M (min i d.numMsgs)) ℂ).submatrix
      (Prod.map id (mCast T₀ (by omega))) id

theorem extV_iso {i : ℕ} (_hi : i < (appendV d).numMsgs) : (extV T₀ i)ᴴ * extV T₀ i = 1 := by
  unfold extV
  split_ifs with h
  · exact iso_submatrix_equiv _ (T₀.V_iso i h)
      ((τA d h).prodCongr (mCast T₀ (by omega))) ((τA d h).prodCongr (mCast T₀ (by omega)))
  · exact iso_submatrix_equiv _ (by rw [conjTranspose_one, Matrix.one_mul])
      ((Equiv.refl _).prodCongr (mCast T₀ (by omega))) (Equiv.refl _)

/-- **The extended prover**: `T₀`, then an idle final turn. -/
@[reducible] noncomputable def extT : IsoStrategy (Reg (appendV d)) (Reg (appendV d)) (appendV d).numMsgs where
  M i := T₀.M (min i d.numMsgs)
  init := T₀.init ∘ mCast T₀ (Nat.zero_min _)
  init_density := isDensity_pureState_comp _ T₀.init_density _
  V i := extV T₀ i
  V_iso _ hi := extV_iso T₀ hi

theorem accept_extT (hd : d.Valid) : accept (extT T₀).toOp = accept T₀.toOp := by
  rw [accept_restT hd]
  refine accept_relabel T₀ (restT (extT T₀)) (fun k hk => mCast T₀ (Nat.min_eq_left hk))
    (fun a => rfl) (fun k hk g a g' b => ?_)
  change (if h : k < d.numMsgs then (extV T₀ k).submatrix (Prod.map (τA d h).symm id)
    (Prod.map (τA d h).symm id) else 0) (g, a) (g', b) = _
  rw [dif_pos hk]
  simp only [submatrix_apply, Prod.map_apply, id_eq, extV, dif_pos hk, Equiv.apply_symm_apply]

end Ext

/-- **Appending an empty message to the verifier keeps the value.** -/
theorem value_appendV (hd : d.Valid) : value (appendV d) = value d := by
  apply le_antisymm
  · obtain ⟨P, hP⟩ := value_attained (appendV d)
    obtain ⟨T, hT⟩ := exists_isoProver P
    rw [← hP, ← hT, accept_restT hd]
    exact accept_le_value d _
  · obtain ⟨P, hP⟩ := value_attained d
    obtain ⟨T₀, hT₀⟩ := exists_isoProver P
    rw [← hP, ← hT₀, ← accept_extT T₀ hd]
    exact accept_le_value _ _


/-! ## Validity and schedule -/

theorem dir_getD_cases (x : Dir) : x = .toVerifier ∨ x = .toProver := by cases x <;> simp

/-- An alternating list of messages whose last message goes to the verifier is the standard
schedule. -/
theorem dirs_eq_std (ms : List Message) (halt : Desc.alternates ms = true)
    (hlast : ms ≠ [] → (ms.map Message.dir).getD (ms.length - 1) .toVerifier = .toVerifier) :
    ms.map Message.dir = stdSchedule ms.length := by
  have hstd : ∀ t, t < ms.length → (ms.map Message.dir).getD (ms.length - 1 - t) .toVerifier =
      if t % 2 = 0 then .toVerifier else .toProver := by
    intro t
    induction t with
    | zero => intro h; rw [if_pos rfl, Nat.sub_zero]; exact hlast (by intro e; simp [e] at h)
    | succ t ih =>
      intro ht
      have hne := (alternates_iff_dirs ms).mp halt (ms.length - 1 - (t + 1)) (by omega)
      rw [show ms.length - 1 - (t + 1) + 1 = ms.length - 1 - t by omega, ih (by omega)] at hne
      rcases dir_getD_cases ((ms.map Message.dir).getD (ms.length - 1 - (t + 1)) .toVerifier) with h | h <;>
        rw [h] at hne ⊢ <;> split_ifs at hne ⊢ with h1 h2 h2 <;> first | rfl | (exfalso; omega) | exact absurd rfl hne
  apply List.ext_getElem
  · simp [stdSchedule]
  · intro i h1 h2
    have := hstd (ms.length - 1 - i) (by simp at h1; omega)
    rw [show ms.length - 1 - (ms.length - 1 - i) = i by simp at h1; omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
    rw [this]
    simp only [stdSchedule, List.getElem_map, List.getElem_range]

/-- **A valid description whose last message goes to the verifier has the standard schedule.** -/
theorem hasSchedule_of_last (hd : d.Valid) (hlast : LastToVerifier d) : d.HasSchedule d.numMsgs :=
  dirs_eq_std d.msgs hd.alternates (fun _ => hlast)

theorem appendV_valid (hd : d.Valid) (hl : ¬ (1 ≤ d.numMsgs ∧ LastToVerifier d)) : (appendV d).Valid := by
  unfold Desc.Valid Desc.check
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hd.out_lt, ?_⟩, ?_⟩, ?_⟩
  · rw [show (appendV d).msgs = d.msgs ++ [⟨.toVerifier, 0⟩] from rfl, alternates_iff_dirs]
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    have halt := (alternates_iff_dirs d.msgs).mp hd.alternates
    rw [List.map_append, List.getD_append _ _ _ _ (by simp; omega)]
    by_cases hi' : i + 1 < d.msgs.length
    · rw [List.getD_append _ _ _ _ (by simp; omega)]
      exact halt i hi'
    · have hm : i + 1 = d.msgs.length := by omega
      rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_map, hm, Nat.sub_self, List.map_cons, List.map_nil, List.getD_cons_zero]
      intro e
      apply hl
      refine ⟨by unfold Desc.numMsgs; omega, ?_⟩
      unfold LastToVerifier Desc.numMsgs
      rw [show d.msgs.length - 1 = i by omega]
      exact e
  · have := hd.blocks_length
    change (d.blocks ++ [[]]).length = (d.msgs ++ [(⟨.toVerifier, 0⟩ : Message)]).length + 1
    simp only [List.length_append, List.length_singleton]
    unfold Desc.numMsgs at this
    omega
  · refine blocksOkFrom_of _ 0 fun i g hg => ?_
    rw [zero_add, show (appendV d).held i = d.held i from funext (held_appendV i)]
    by_cases hi : i ≤ d.numMsgs
    · rw [blocks_appendV_getD hd hi] at hg
      have := blocksOkFrom_getD d.blocks 0 i hd.blocksOk g hg
      rwa [zero_add] at this
    · have hl' := hd.blocks_length
      have hg' : g ∈ (d.blocks ++ [[]]).getD i [] := hg
      have hlen : d.blocks.length ≤ i := by unfold Desc.numMsgs at hl' hi; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hlen] at hg'
      rcases h : i - d.blocks.length with _ | k
      · simp [h] at hg'
      · simp [h] at hg'

theorem hasSchedule_appendV (hd : d.Valid) (hl : ¬ (1 ≤ d.numMsgs ∧ LastToVerifier d)) :
    (appendV d).HasSchedule (d.numMsgs + 1) := by
  have h := hasSchedule_of_last (appendV_valid hd hl) (by
    unfold LastToVerifier
    rw [numMsgs_appendV, Nat.add_sub_cancel]
    simp [appendV, List.getD_eq_getElem?_getD, Desc.numMsgs])
  rwa [numMsgs_appendV] at h

/-! ## Normalization -/

instance : DecidablePred LastToVerifier := fun d => by unfold LastToVerifier; infer_instance

/-- **Schedule normalization**: `d` itself if it ends with a message to the verifier, otherwise
`appendV d`. -/
noncomputable def normDesc (d : Desc) : Desc :=
  if 1 ≤ d.numMsgs ∧ LastToVerifier d then d else appendV d

theorem normDesc_spec (hd : d.Valid) :
    (normDesc d).Valid ∧ (normDesc d).HasSchedule (normDesc d).numMsgs ∧ 1 ≤ (normDesc d).numMsgs ∧
      value (normDesc d) = value d ∧ (normDesc d).numMsgs ≤ d.numMsgs + 1 ∧
      (normDesc d).totalWires = d.totalWires ∧ (normDesc d).gateCount = d.gateCount := by
  unfold normDesc
  split_ifs with h
  · exact ⟨hd, hasSchedule_of_last hd h.2, h.1, rfl, by omega, rfl, rfl⟩
  · refine ⟨appendV_valid hd h, by rw [numMsgs_appendV]; exact hasSchedule_appendV hd h,
      by rw [numMsgs_appendV]; omega, value_appendV hd, by rw [numMsgs_appendV], totalWires_appendV, ?_⟩
    simp [appendV, Desc.gateCount]

end ShiQIP
