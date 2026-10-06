import QIP.Halve.Accept
import QIP.UnitaryProver


/-!
# Q31 — the run of the halved description

Against the unitary prover `dilateU T`, the state after block `k'` (`1 ≤ k ≤ n`) is
`(Φ 0 F_k + Φ 1 B_k) / √2`, where `F_k` follows the second half of `d` from the cut state and
`B_k` undoes the first half (`pureRun_halve`). The turns of `d` used here are local to the
prover's side (`exists_turn_sw`, `exists_turn_flip`), so they define generalized turn families
`UF`, `UB`, and the acceptance probability is `(fwdP UF c ξ + bwdP UB c ξ) / 2`
(`accept_halve`).
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped Kronecker

variable {d : Desc} {n : ℕ} {N₀ : Type} [Fintype N₀] [DecidableEq N₀]

/-! ## Local turns -/

omit [Fintype N₀] [DecidableEq N₀] in
theorem σSw_involutive {p q r : ℕ} (hqr : q + r ≤ d.totalWires) (hp : hPriv d ≤ p)
    (hpr : p + r ≤ (halveDesc d n).totalWires) :
    Function.Involutive (σSw (N₀ := N₀) d n p q r) := by
  intro z
  obtain ⟨x, μ, β⟩ := z
  simp only [σSw]
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · funext w
    simp only
    split_ifs with h1 h2 <;> first
      | rfl
      | (exfalso; omega)
      | (congr 1; apply Fin.ext; simp only; omega)
  · funext u
    simp only
    split_ifs with h1 h2 <;> first
      | rfl
      | (exfalso; omega)
      | (congr 1; apply Subtype.ext; apply Fin.ext; simp only; omega)

theorem gsplit_fst_eq {k : ℕ} {N : Type} {z z' : Qubits d.totalWires × N}
    (h : ∀ w, kept d k w → z'.1 w = z.1 w) : (gsplit d k N z').1 = (gsplit d k N z).1 := by
  funext w; exact h w.1 w.2

/-- **A swap with register `j` is a turn at turn `j`.** -/
theorem exists_turn_sw {k j : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : wd d j ≤ hw d n k) :
    ∃ U ∈ Matrix.unitaryGroup (PS d j × (N₀ × MB d n)) ℂ, ∀ v, turnOp U *ᵥ v = swOp d n N₀ k j v := by
  have h1 := msgOffset_add_width_le d j
  have h2 := hPay_ge (d := d) (n := n) k
  have h3 := hPay_add_le hk1 hkn hj
  have hW : d.totalWires + 3 ≤ hPriv d := by unfold hPriv; omega
  have hqr : d.msgOffset j + wd d j ≤ d.totalWires := h1
  refine exists_turn_perm j _ (σSw_involutive hqr h2 h3) (fun z => ?_) (fun z z' hzz => ?_)
  · refine gsplit_fst_eq fun w hw => ?_
    simp only [σSw]
    rw [dif_neg]
    intro h
    exact not_kept_of_inReg ⟨h.1, h.2.1⟩ hw
  · have hx : ∀ w, ¬ kept d j w → z.1 w = z'.1 w := fun w hw =>
      congrFun (congrArg Prod.fst hzz) ⟨w, hw⟩
    have hν : z.2 = z'.2 := by have := congrArg Prod.snd hzz; exact this
    obtain ⟨x, μ, β⟩ := z
    obtain ⟨x', μ', β'⟩ := z'
    simp only at hx hν
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hν
    simp only [gsplit_apply, σSw, Prod.mk.injEq, true_and]
    refine ⟨funext fun w => ?_, funext fun u => ?_⟩
    · split_ifs with h
      · rfl
      · exact hx w.1 w.2
    · split_ifs with h
      · have hr : wd d j = d.msgWidth j := rfl
        exact hx _ (not_kept_of_inReg ⟨by simp only; omega, by simp only; omega⟩)
      · rfl

variable (d n N₀) in
/-- Flip the coin copy. -/
def flipOp : DOp d n N₀ := fun v => v ∘ flipZ d n N₀

theorem exists_turn_flip (k : ℕ) :
    ∃ U ∈ Matrix.unitaryGroup (PS d k × (N₀ × MB d n)) ℂ, ∀ v, turnOp U *ᵥ v = flipOp d n N₀ v := by
  refine exists_turn_perm k _ (fun z => flipZ_flipZ z) (fun z => rfl) (fun z z' hzz => ?_)
  have hx : (fun w : {w // ¬ kept d k w} => z.1 w.1) = fun w => z'.1 w.1 := congrArg (fun p => p.1) hzz
  have hν : z.2 = z'.2 := by have := congrArg Prod.snd hzz; exact this
  simp only [gsplit_apply, flipZ, hν]
  rw [hx]

/-! ## The prover's turns -/

variable (d n N₀) in
/-- A prover turn in the `d`-picture. -/
noncomputable def proverOp (k : ℕ) (A : Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ) :
    DOp d n N₀ := fun v => ((1 : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) ⊗ₖ PA d n k A) *ᵥ v

theorem exists_turn_prover {k t : ℕ} {A : Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ}
    (hA : A ∈ Matrix.unitaryGroup _ ℂ) :
    ∃ U ∈ Matrix.unitaryGroup (PS d t × (N₀ × MB d n)) ℂ, ∀ v, turnOp U *ᵥ v = proverOp d n N₀ k A v :=
  exists_turn_mem t (PA_mem hA)

theorem exists_turn_ifOp {t : ℕ} (c : Prop) [Decidable c] {op : DOp d n N₀}
    (h : ∃ U ∈ Matrix.unitaryGroup (PS d t × (N₀ × MB d n)) ℂ, ∀ v, turnOp U *ᵥ v = op v) :
    ∃ U ∈ Matrix.unitaryGroup (PS d t × (N₀ × MB d n)) ℂ, ∀ v, turnOp U *ᵥ v = ifOp c op v := by
  by_cases hc : c
  · simpa [ifOp, hc] using h
  · simpa [ifOp, hc] using exists_turn_id (d := d) (N := N₀ × MB d n) t


/-! ## The turns of `d` used by the two branches -/

variable (d n N₀) in
/-- Forward turn `n + k` of `d`: the prover's turn `k'` with the swap of message `k'`. -/
noncomputable def tfOp (A : ∀ k, Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ) (k : ℕ) :
    DOp d n N₀ := fun v =>
  ifOp (k % 2 = 0) (swOp d n N₀ k (n + k)) (proverOp d n N₀ k (A k) (ifOp (k % 2 = 1) (swOp d n N₀ k (n + k)) v))

variable (d n N₀) in
/-- Backward turn `n + 1 - k` of `d`, inverted. -/
noncomputable def tbOp (A : ∀ k, Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ) (k : ℕ) :
    DOp d n N₀ := fun v =>
  ifOp (k % 2 = 0) (swOp d n N₀ k (n + 1 - k)) (proverOp d n N₀ k (A k)
    (ifOp (k % 2 = 1) (swOp d n N₀ k (n + 1 - k)) (ifOp (k = 1) (flipOp d n N₀) v)))

/-! ## Products of operators -/

theorem sufOp_succ' {N : Type} [Fintype N] [DecidableEq N] (U : Turns d N) (a : ℕ) :
    ∀ j, sufOp U a (j + 1) = sufOp U (a + 1) j * blockOp d N (a + 1) * turnOp (U a)
  | 0 => by simp [sufOp]
  | j + 1 => by
    rw [sufOp, sufOp_succ' U a j, sufOp]
    rw [show a + (j + 1) + 1 = a + 1 + j + 1 by omega, show a + (j + 1) = a + 1 + j by omega]
    simp only [Matrix.mul_assoc]

theorem bOpH_flip (j : ℕ) (v : Qubits d.totalWires × (N₀ × MB d n) → ℂ) :
    flipOp d n N₀ (bOpH d n N₀ j v) = bOpH d n N₀ j (flipOp d n N₀ v) := by
  funext ⟨x, μ, β⟩
  simp only [flipOp, bOpH, blockOp, conjTranspose_kronecker, conjTranspose_one, Function.comp_apply, flipZ]
  rw [kronOne_mulVec_apply, kronOne_mulVec_apply]
  rfl

omit [DecidableEq N₀] in
theorem tv_lin {k : ℕ} (A : Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ) (c : ℂ)
    (u w : Qubits (halveDesc d n).totalWires × N₀ → ℂ) : tv k A (c • (u + w)) = c • (tv k A u + tv k A w) := by
  simp only [tv]
  rw [show (c • (u + w)) ∘ (turnSplit (halveDesc d n) k N₀).symm =
    c • (u ∘ (turnSplit (halveDesc d n) k N₀).symm + w ∘ (turnSplit (halveDesc d n) k N₀).symm) from rfl,
    mulVec_smul, mulVec_add]
  rfl

theorem kron_lin {M : ℕ} (B : Matrix (Qubits M) (Qubits M) ℂ) (c : ℂ) (u w : Qubits M × N₀ → ℂ) :
    (B ⊗ₖ (1 : Matrix N₀ N₀ ℂ)) *ᵥ (c • (u + w)) = c • ((B ⊗ₖ (1 : Matrix N₀ N₀ ℂ)) *ᵥ u +
      (B ⊗ₖ (1 : Matrix N₀ N₀ ℂ)) *ᵥ w) := by
  rw [mulVec_smul, mulVec_add]

/-! ## The run -/

variable (d n N₀) in
/-- The run of the halved description against unitary turns `A` and initial memory `ι`. -/
noncomputable def hRun (A : ∀ k, Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ)
    (ι : N₀ → ℂ) : ℕ → Qubits (halveDesc d n).totalWires × N₀ → ℂ
  | 0 => (blockMat (halveDesc d n) 0 ⊗ₖ (1 : Matrix N₀ N₀ ℂ)) *ᵥ
      fun p => zeroVec (halveDesc d n).totalWires p.1 * ι p.2
  | k + 1 => (blockMat (halveDesc d n) (k + 1) ⊗ₖ (1 : Matrix N₀ N₀ ℂ)) *ᵥ tv k (A k) (hRun A ι k)

theorem hRun_zero (A : ∀ k, Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ)
    (ι : N₀ → ℂ) : hRun d n N₀ A ι 0 = fun p => zeroVec (halveDesc d n).totalWires p.1 * ι p.2 := by
  rw [hRun, blockMat, blocks_getD_halve (by omega), hBlock, if_pos rfl, List.filterMap_nil, kron_layer_mulVec]
  rfl

section Run

variable (A : ∀ k, Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ) (ι : N₀ → ℂ)
  (UF UB : Turns d (N₀ × MB d n))

variable (d n) in
/-- The forward branch after block `n + 1 + j` of `d`. -/
noncomputable def gF (j : ℕ) : Qubits d.totalWires × (N₀ × MB d n) → ℂ :=
  sufOp UF (n + 1) j *ᵥ cutVec d n (A 0) ι

variable (d n) in
/-- The backward branch with blocks `n + 2 - j, …, n + 1` of `d` undone. -/
noncomputable def gB (j : ℕ) : Qubits d.totalWires × (N₀ × MB d n) → ℂ :=
  (sufOp UB (n + 1 - j) j)ᴴ *ᵥ cutVec d n (A 0) ι

theorem gF_succ (j : ℕ) : gF d n A ι UF (j + 1) =
    bOp d n N₀ (n + 1 + j + 1) (turnOp (UF (n + 1 + j)) *ᵥ gF d n A ι UF j) := by
  simp only [gF, bOp, sufOp, ← mulVec_mulVec]

theorem gB_succ {j : ℕ} (hj : j ≤ n) : gB d n A ι UB (j + 1) =
    (turnOp (UB (n - j)))ᴴ *ᵥ bOpH d n N₀ (n + 1 - j) (gB d n A ι UB j) := by
  simp only [gB, bOpH]
  rw [show n + 1 - (j + 1) = n - j by omega, sufOp_succ', show n - j + 1 = n + 1 - j by omega,
    conjTranspose_mul, conjTranspose_mul, ← mulVec_mulVec, ← mulVec_mulVec]

end Run


section Run2

variable (A : ∀ k, Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ) (ι : N₀ → ℂ)
  (UF UB : Turns d (N₀ × MB d n))

variable (d n) in
/-- The forward component after block `k'`. -/
noncomputable def fH (k : ℕ) : Qubits d.totalWires × (N₀ × MB d n) → ℂ :=
  ifOp (k % 2 = 1) (swOp d n N₀ k (n + k)) (gF d n A ι UF (k - 1))

variable (d n) in
/-- The backward component after block `k'`. -/
noncomputable def bH (k : ℕ) : Qubits d.totalWires × (N₀ × MB d n) → ℂ :=
  ifOp (k % 2 = 1) (swOp d n N₀ k (n + 1 - k))
    (ifOp (k = 1) (flipOp d n N₀) (bOpH d n N₀ (n + 2 - k) (gB d n A ι UB (k - 1))))

/-- **The run of the halved description**, block by block. -/
theorem hRun_eq (hd : d.Valid) (hn : 1 ≤ n)
    (hUF : ∀ k, 1 ≤ k → k ≤ n → ∀ v, turnOp (UF (n + k)) *ᵥ v = tfOp d n N₀ A k v)
    (hUB : ∀ k, 1 ≤ k → k ≤ n → ∀ v, (turnOp (UB (n + 1 - k)))ᴴ *ᵥ v = tbOp d n N₀ A k v) :
    ∀ k, 1 ≤ k → k ≤ n → hRun d n N₀ A ι k =
      (Real.sqrt 2 : ℂ)⁻¹ • (Φ false (fH d n A ι UF k) + Φ true (bH d n A ι UB k)) := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro _
    funext ⟨y, μ⟩
    rw [hRun, hRun_zero, blockMat, blocks_getD_halve (by omega), kron_layer_mulVec]
    simp only
    rw [runLayer_hBlock_one hd hn]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, fH, bH, gF, gB, sufOp, one_mulVec,
      conjTranspose_one, ifOp, Nat.sub_self, show n + 2 - 1 = n + 1 by omega, show n + 1 - 1 = n by omega,
      show 1 % 2 = 1 from rfl, if_true]
    rw [bOpH_flip]
    rfl
  | succ k hk1 ih =>
    intro hkn
    rw [hRun, ih (by omega), tv_lin, tv_Φ, tv_Φ, kron_lin]
    rw [blockMat_halve_Φ (by omega) false _ _ (fun μ => runLayer_hBlock_mid hd (by omega) hkn false _ μ),
      blockMat_halve_Φ (by omega) true _ _ (fun μ => runLayer_hBlock_mid hd (by omega) hkn true _ μ)]
    simp only [if_true, if_false, Bool.false_eq_true]
    congr 3
    · -- forward
      have hg : gF d n A ι UF k = bOp d n N₀ (n + k + 1) (tfOp d n N₀ A k (gF d n A ι UF (k - 1))) := by
        have := gF_succ A ι UF (k - 1)
        rw [show k - 1 + 1 = k by omega, show n + 1 + (k - 1) = n + k by omega, hUF k hk1 (by omega)] at this
        exact this
      simp only [fH, fwdOp, hg, tfOp, show k + 1 - 1 = k by omega, show n + (k + 1) - 1 = n + k by omega]
      rfl
    · -- backward
      have hg : gB d n A ι UB k = tbOp d n N₀ A k (bOpH d n N₀ (n + 2 - k) (gB d n A ι UB (k - 1))) := by
        have := gB_succ A ι UB (j := k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega, show n - (k - 1) = n + 1 - k by omega,
          show n + 1 - (k - 1) = n + 2 - k by omega, hUB k hk1 (by omega)] at this
        exact this
      simp only [bH, bwdOp, hg, tbOp, show k + 1 - 1 = k by omega, show n + 2 - (k + 1) = n + 1 - k by omega,
        if_neg (show k + 1 ≠ 1 by omega), ifOp]
      rfl

end Run2


section Final

variable (A : ∀ k, Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ) (ι : N₀ → ℂ)
  (UF UB : Turns d (N₀ × MB d n))

theorem hBlock_last (hn : 1 ≤ n) : hBlock d n (n + 1) =
    onF d (finF d n ++ [Gate.cnot d.out (hOut d)]) ++ onB d (finB d n) ++
      ztGates (hCoin d) (hOut d) (held0 d) (hAnc d) := by
  rw [hBlock, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rfl

/-- **The final state.** -/
theorem hRun_final (hd : d.Valid) (hn : 1 ≤ n) (hne : n % 2 = 0)
    (hUF : ∀ k, 1 ≤ k → k ≤ n → ∀ v, turnOp (UF (n + k)) *ᵥ v = tfOp d n N₀ A k v)
    (hUB : ∀ k, 1 ≤ k → k ≤ n → ∀ v, (turnOp (UB (n + 1 - k)))ᴴ *ᵥ v = tbOp d n N₀ A k v)
    (hUB0 : ∀ v, (turnOp (UB 0))ᴴ *ᵥ v = v) (y : Qubits (halveDesc d n).totalWires) (μ : N₀) :
    hRun d n N₀ A ι (n + 1) (y, μ) =
      runLayer ((ztGates (hCoin d) (hOut d) (held0 d) (hAnc d)).filterMap
        (Gate.toInstr? (halveDesc d n).totalWires)) ((Real.sqrt 2 : ℂ)⁻¹ • fun y =>
          Φ false (gF d n A ι UF n) (cnotFun (outD d n hd) (outW d n) y, μ) +
            Φ true (bOpH d n N₀ 0 (gB d n A ι UB (n + 1))) (y, μ)) y := by
  have hn2 : n ≠ 1 := by omega
  rw [hRun, hRun_eq A ι UF UB hd hn hUF hUB n hn le_rfl, tv_lin, tv_Φ, tv_Φ, blockMat,
    blocks_getD_halve le_rfl, kron_layer_mulVec, hBlock_last hn]
  simp only
  rw [List.filterMap_append, List.filterMap_append, runLayer_append, runLayer_append]
  congr 1
  have hF := funext (runLayer_onF_fin (N₀ := N₀) hd hn false
    (((1 : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) ⊗ₖ PA d n n (A n)) *ᵥ fH d n A ι UF n) μ)
  have hT := funext (runLayer_onF_fin (N₀ := N₀) hd hn true
    (((1 : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) ⊗ₖ PA d n n (A n)) *ᵥ bH d n A ι UB n) μ)
  simp only [if_true, if_false, Bool.false_eq_true] at hF hT
  rw [show (fun y' => (((Real.sqrt 2 : ℂ)⁻¹ • (Φ false (((1 : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) ⊗ₖ
      PA d n n (A n)) *ᵥ fH d n A ι UF n) + Φ true (((1 : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) ⊗ₖ
      PA d n n (A n)) *ᵥ bH d n A ι UB n))) (y', μ))) =
    (Real.sqrt 2 : ℂ)⁻¹ • ((fun y' => Φ false (((1 : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) ⊗ₖ
      PA d n n (A n)) *ᵥ fH d n A ι UF n) (y', μ)) + fun y' => Φ true (((1 : Matrix (Qubits d.totalWires)
      (Qubits d.totalWires) ℂ) ⊗ₖ PA d n n (A n)) *ᵥ bH d n A ι UB n) (y', μ)) from rfl,
    runLayer_smul, runLayer_add, hF, hT, runLayer_smul]
  rw [show (fun y => Φ false (finFOp d n N₀ (((1 : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) ⊗ₖ
      PA d n n (A n)) *ᵥ fH d n A ι UF n)) (cnotFun (outD d n hd) (outW d n) y, μ)) +
      (fun y => Φ true (((1 : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) ⊗ₖ PA d n n (A n)) *ᵥ
        bH d n A ι UB n) (y, μ)) =
      fun y => Φ false (finFOp d n N₀ (((1 : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) ⊗ₖ
        PA d n n (A n)) *ᵥ fH d n A ι UF n)) (cnotFun (outD d n hd) (outW d n) y, μ) +
        Φ true (((1 : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) ⊗ₖ PA d n n (A n)) *ᵥ
          bH d n A ι UB n) (y, μ) from rfl, runLayer_onB_fin hd hn]
  have hFin : finFOp d n N₀ (((1 : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) ⊗ₖ
      PA d n n (A n)) *ᵥ fH d n A ι UF n) = gF d n A ι UF n := by
    have := gF_succ A ι UF (n - 1)
    rw [show n - 1 + 1 = n by omega, show n + 1 + (n - 1) = n + n by omega, hUF n hn le_rfl] at this
    rw [this]
    simp only [finFOp, fH, tfOp, ifOp, if_pos hne, if_neg (show ¬ n % 2 = 1 by omega), id, proverOp,
      show n + n = 2 * n by omega]
  have hBin : finBOp d n N₀ (((1 : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) ⊗ₖ
      PA d n n (A n)) *ᵥ bH d n A ι UB n) = bOpH d n N₀ 0 (gB d n A ι UB (n + 1)) := by
    have h1 := gB_succ A ι UB (j := n) le_rfl
    rw [Nat.sub_self, hUB0, show n + 1 - n = 1 by omega] at h1
    have h2 := gB_succ A ι UB (j := n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega, show n - (n - 1) = n + 1 - n by omega,
      show n + 1 - (n - 1) = n + 2 - n by omega, hUB n hn le_rfl] at h2
    rw [h1, h2]
    simp only [finBOp, bH, tbOp, ifOp, if_pos hne, if_neg (show ¬ n % 2 = 1 by omega), if_neg hn2, id,
      proverOp, show n + 1 - n = 1 by omega]
  rw [hFin, hBin]

end Final


section Accept

variable (A : ∀ k, Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ) (ι : N₀ → ℂ)
  (UF UB : Turns d (N₀ × MB d n))

theorem outBit_halve (y : Qubits (halveDesc d n).totalWires) :
    outBit (halveDesc d n) y ↔ y (outW d n) = true :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨(outW d n).2, h⟩⟩

theorem preOp_adj_halve : (preOp UB (n + 1))ᴴ *ᵥ cutVec d n (A 0) ι =
    bOpH d n N₀ 0 (gB d n A ι UB (n + 1)) := by
  have h := preOp_add UB 0 (n + 1)
  rw [zero_add] at h
  rw [h, conjTranspose_mul, ← mulVec_mulVec]
  simp only [gB, bOpH, Nat.sub_self]
  rfl

/-- **Acceptance of the halved description**: half the forward and half the backward success. -/
theorem accept_hRun (hd : d.Valid) (hn : 1 ≤ n) (hne : n % 2 = 0) (hm : d.numMsgs = 2 * n + 1)
    (hUF : ∀ k, 1 ≤ k → k ≤ n → ∀ v, turnOp (UF (n + k)) *ᵥ v = tfOp d n N₀ A k v)
    (hUB : ∀ k, 1 ≤ k → k ≤ n → ∀ v, (turnOp (UB (n + 1 - k)))ᴴ *ᵥ v = tbOp d n N₀ A k v)
    (hUB0 : ∀ v, (turnOp (UB 0))ᴴ *ᵥ v = v) :
    (∑ y, ∑ μ, if outBit (halveDesc d n) y then ‖hRun d n N₀ A ι (n + 1) (y, μ)‖ ^ 2 else 0) =
      (1 / 2 : ℝ) * (fwdP UF (n + 1) (cutVec d n (A 0) ι) + bwdP UB (n + 1) (cutVec d n (A 0) ι)) := by
  rw [Finset.sum_comm]
  have hslice : ∀ μ : N₀, (∑ y, if outBit (halveDesc d n) y then ‖hRun d n N₀ A ι (n + 1) (y, μ)‖ ^ 2 else 0) =
      (1 / 2 : ℝ) * ((∑ x, ∑ β, if outBit d x then ‖gF d n A ι UF n (x, (μ, β))‖ ^ 2 else 0) +
        ∑ x, ∑ β, if Zero0 d x then ‖bOpH d n N₀ 0 (gB d n A ι UB (n + 1)) (x, (μ, β))‖ ^ 2 else 0) := by
    intro μ
    rw [← accept_slice hd]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [if_congr (outBit_halve y) rfl rfl, hRun_final A ι UF UB hd hn hne hUF hUB hUB0]
  rw [Finset.sum_congr rfl fun μ _ => hslice μ, ← Finset.mul_sum, Finset.sum_add_distrib]
  congr 2
  · rw [fwdP, hm, show 2 * n + 1 - (n + 1) = n by omega, nsq_projQ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]
    rfl
  · rw [bwdP, preOp_adj_halve, nsq_projQ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]

/-! ## The cut state is a unit vector -/

variable (d n) in
/-- Working-copy labels are labels of message `0'`. -/
def regOfE : Qubits d.totalWires ≃ Reg (halveDesc d n) 0 where
  toFun := regOf d n
  invFun r := fun w => r ⟨⟨hPriv d + w, by have := hPriv_add_W_le (d := d) (n := n); omega⟩,
    (inReg_zero_iff _).mpr ⟨by simp, by simp⟩⟩
  left_inv x := by funext w; simp [regOf]
  right_inv r := by
    funext w
    have hw := (inReg_zero_iff w.1).mp w.2
    simp only [regOf]
    congr 1
    apply Subtype.ext; apply Fin.ext; simp only; omega

theorem nsq_cutVec (hA : A 0 ∈ Matrix.unitaryGroup _ ℂ) (hι : ∑ μ, ‖ι μ‖ ^ 2 = 1) :
    nsq (cutVec d n (A 0) ι) = 1 := by
  have h0 : ∀ x μ, (∑ β : MB d n, ‖cutVec d n (A 0) ι (x, (μ, β))‖ ^ 2) = ‖cvec d n (A 0) ι (regOf d n x, μ)‖ ^ 2 := by
    intro x μ
    rw [Finset.sum_eq_single (fun _ => false)]
    · simp [cutVec]
    · intro β _ hβ
      have : ¬ ∀ u, β u = false := fun h => hβ (funext h)
      show ‖(if ∀ u, β u = false then _ else 0)‖ ^ 2 = 0
      rw [if_neg this]; simp
    · simp
  rw [nsq, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, h0]
  rw [show (∑ x, ∑ μ, ‖cvec d n (A 0) ι (regOf d n x, μ)‖ ^ 2) =
      ∑ r, ∑ μ, ‖cvec d n (A 0) ι (r, μ)‖ ^ 2 from Equiv.sum_comp (regOfE d n) (fun r => ∑ μ, ‖cvec d n (A 0) ι (r, μ)‖ ^ 2)]
  have hc : ∀ p, cvec d n (A 0) ι p = (A 0 *ᵥ fun q => if q.1 = (fun _ => false) then ι q.2 else 0) p := by
    intro p
    simp only [cvec, mulVec, dotProduct, Fintype.sum_prod_type, mul_ite, mul_zero]
    rw [Finset.sum_eq_single (fun _ => false)]
    · simp
    · intro r _ hr; simp [hr]
    · simp
  have := nsq_unitary hA (fun q : Reg (halveDesc d n) 0 × N₀ => if q.1 = (fun _ => false) then ι q.2 else 0)
  rw [nsq, nsq, Fintype.sum_prod_type, Fintype.sum_prod_type] at this
  simp only [← hc] at this
  rw [this, Finset.sum_eq_single (fun _ => false)]
  · simpa using hι
  · intro r _ hr; simp [hr]
  · simp

end Accept


/-! ## The turn families -/

theorem turnOp_conjTranspose {N : Type} [Fintype N] [DecidableEq N] {k : ℕ}
    (U : Matrix (PS d k × N) (PS d k × N) ℂ) : turnOp Uᴴ = (turnOp U)ᴴ := by
  rw [turnOp, turnOp, conjTranspose_submatrix, conjTranspose_kronecker, conjTranspose_one]

theorem turnOp_one {N : Type} [Fintype N] [DecidableEq N] {k : ℕ} :
    turnOp (1 : Matrix (PS d k × N) (PS d k × N) ℂ) = 1 := by
  rw [turnOp, one_kronecker_one]; exact submatrix_one_equiv _

section Families

variable (A : ∀ k, Matrix (Reg (halveDesc d n) k × N₀) (Reg (halveDesc d n) k × N₀) ℂ)

theorem exists_UF (hA : ∀ k, A k ∈ Matrix.unitaryGroup _ ℂ) :
    ∃ UF : Turns d (N₀ × MB d n), (∀ t, UF t ∈ Matrix.unitaryGroup (PS d t × (N₀ × MB d n)) ℂ) ∧
      ∀ k, 1 ≤ k → k ≤ n → ∀ v, turnOp (UF (n + k)) *ᵥ v = tfOp d n N₀ A k v := by
  have key : ∀ t, ∃ U ∈ Matrix.unitaryGroup (PS d t × (N₀ × MB d n)) ℂ,
      ∀ k, 1 ≤ k → k ≤ n → t = n + k → ∀ v, turnOp U *ᵥ v = tfOp d n N₀ A k v := by
    intro t
    by_cases ht : n + 1 ≤ t ∧ t ≤ 2 * n
    · obtain ⟨k, rfl⟩ : ∃ k, t = n + k := ⟨t - n, by omega⟩
      have hk1 : 1 ≤ k := by omega
      have hkn : k ≤ n := by omega
      have hs := exists_turn_sw (N₀ := N₀) (d := d) (j := n + k) hk1 hkn (wd_le_hw_fwd hk1)
      obtain ⟨U, hU, hUv⟩ := exists_turn_mul (exists_turn_ifOp (k % 2 = 0) hs)
        (exists_turn_mul (exists_turn_prover (t := n + k) (hA k)) (exists_turn_ifOp (k % 2 = 1) hs))
      refine ⟨U, hU, fun k' _ _ hk' v => ?_⟩
      obtain rfl : k' = k := by omega
      exact hUv v
    · exact ⟨1, one_mem _, fun k h1 h2 h3 => absurd ⟨by omega, by omega⟩ ht⟩
  choose UF hU hUF using key
  exact ⟨UF, hU, fun k h1 h2 v => hUF (n + k) k h1 h2 rfl v⟩

theorem exists_UB (hA : ∀ k, A k ∈ Matrix.unitaryGroup _ ℂ) :
    ∃ UB : Turns d (N₀ × MB d n), (∀ t, UB t ∈ Matrix.unitaryGroup (PS d t × (N₀ × MB d n)) ℂ) ∧
      (∀ k, 1 ≤ k → k ≤ n → ∀ v, (turnOp (UB (n + 1 - k)))ᴴ *ᵥ v = tbOp d n N₀ A k v) ∧
      ∀ v, (turnOp (UB 0))ᴴ *ᵥ v = v := by
  have key : ∀ t, ∃ U ∈ Matrix.unitaryGroup (PS d t × (N₀ × MB d n)) ℂ,
      (∀ k, 1 ≤ k → k ≤ n → t = n + 1 - k → ∀ v, (turnOp U)ᴴ *ᵥ v = tbOp d n N₀ A k v) ∧
      (t = 0 → ∀ v, (turnOp U)ᴴ *ᵥ v = v) := by
    intro t
    by_cases ht : 1 ≤ t ∧ t ≤ n
    · obtain ⟨k, hk1, hkn, rfl⟩ : ∃ k, 1 ≤ k ∧ k ≤ n ∧ t = n + 1 - k :=
        ⟨n + 1 - t, by omega, by omega, by omega⟩
      have hs := exists_turn_sw (N₀ := N₀) (d := d) (j := n + 1 - k) hk1 hkn (wd_le_hw_bwd hk1)
      obtain ⟨U, hU, hUv⟩ := exists_turn_mul (exists_turn_ifOp (k % 2 = 0) hs)
        (exists_turn_mul (exists_turn_prover (t := n + 1 - k) (hA k))
          (exists_turn_mul (exists_turn_ifOp (k % 2 = 1) hs)
            (exists_turn_ifOp (k = 1) (exists_turn_flip (d := d) (n := n) (N₀ := N₀) (n + 1 - k)))))
      refine ⟨Uᴴ, ?_, fun k' _ _ hk' v => ?_, fun h => absurd h (by omega)⟩
      · rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hU
      · obtain rfl : k' = k := by omega
        rw [turnOp_conjTranspose, conjTranspose_conjTranspose]
        exact hUv v
    · refine ⟨1, one_mem _, fun k h1 h2 h3 => absurd ⟨by omega, by omega⟩ ht, fun _ v => ?_⟩
      rw [turnOp_one, conjTranspose_one, one_mulVec]
  choose UB hU hUB using key
  exact ⟨UB, hU, fun k h1 h2 v => (hUB (n + 1 - k)).1 k h1 h2 rfl v, (hUB 0).2 rfl⟩

end Families

/-! ## Soundness -/

section Sound

variable (T : IsoStrategy (Reg (halveDesc d n)) (Reg (halveDesc d n)) (halveDesc d n).numMsgs)

theorem pureRun_dilateU_hRun : ∀ k, pureRun (dilateU T) k =
    hRun d n (DilMem (halveDesc d n) T) (dilU T) (dilateU T).init k
  | 0 => rfl
  | k + 1 => by
    rw [pureRun, hRun, ← pureRun_dilateU_hRun k]
    rfl

theorem sum_norm_init : ∑ μ, ‖(dilateU T).init μ‖ ^ 2 = 1 :=
  (isDensity_pure_iff _).mp (dilateU T).init_density

/-- **Soundness of halving**, for one prover. -/
theorem accept_halve_le (hd : d.Valid) (hn : 1 ≤ n) (hne : n % 2 = 0) (hm : d.numMsgs = 2 * n + 1) :
    accept (dilateU T).toOp ≤ (1 + Real.sqrt (value d)) / 2 := by
  obtain ⟨UF, hUFu, hUF⟩ := exists_UF (d := d) (n := n) (dilU T) (fun k => dilU_mem T)
  obtain ⟨UB, hUBu, hUB, hUB0⟩ := exists_UB (d := d) (n := n) (dilU T) (fun k => dilU_mem T)
  have hacc := accept_hRun (dilU T) (dilateU T).init UF UB hd hn hne hm hUF hUB hUB0
  have hcut := cut_bound hd (show n + 1 < d.numMsgs by omega) UF UB hUFu hUBu
    (cutVec d n (dilU T 0) (dilateU T).init) (nsq_cutVec (dilU T) _ (dilU_mem T) (sum_norm_init T))
  rw [accept_pureRun, accept_expect]
  have e : ∀ j, j = n + 1 → (∑ y, ∑ μ : DilMem (halveDesc d n) T,
      if outBit (halveDesc d n) y then ‖pureRun (dilateU T) j (y, μ)‖ ^ 2 else 0) =
        (1 / 2 : ℝ) * (fwdP UF (n + 1) (cutVec d n (dilU T 0) (dilateU T).init) +
          bwdP UB (n + 1) (cutVec d n (dilU T 0) (dilateU T).init)) := by
    rintro j rfl
    rw [← hacc, pureRun_dilateU_hRun]
  rw [e _ (numMsgs_halveDesc d n)]
  linarith

/-- **Soundness of halving.** -/
theorem value_halve_le (hd : d.Valid) (hn : 1 ≤ n) (hne : n % 2 = 0) (hm : d.numMsgs = 2 * n + 1) :
    value (halveDesc d n) ≤ (1 + Real.sqrt (value d)) / 2 := by
  rw [← value_le_iff]
  intro P
  obtain ⟨T, hT⟩ := exists_isoProver P
  rw [← hT, ← accept_dilateU T]
  exact accept_halve_le T hd hn hne hm

end Sound

end ShiQIP
