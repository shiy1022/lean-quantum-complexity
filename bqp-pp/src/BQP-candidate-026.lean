import Definitions.Def_ShiShallow_Core
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiShallow_circuit_amplitude_is_a_path_sum_over_hadamard_branches

namespace BQPReferenceValidation.Source26

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiShallow

/-! PATH-1: the amplitude of a flat gate list as a sum over branch assignments.

`hcnt gs` counts the Hadamards in `gs`; a branch is a bit for each Hadamard, supplied as a
`List Bool` (fed by `List.ofFn` from `Fin (hcnt gs) → Bool`).  `pamp` is the product of the
per-gate coefficients along a branch and `pmap` the composed basis-string map; both are
recursions over the gate list, consuming one branch bit at each `.h`.  Non-Hadamard gates are
handled through the abstract `coef`/`perm` data (the BRANCH-1 interface). -/


private def hcnt {n : ℕ} : List (Instr n) → ℕ
  | [] => 0
  | (Instr.h _) :: gs => hcnt gs + 1
  | (Instr.s _) :: gs => hcnt gs
  | (Instr.t _) :: gs => hcnt gs
  | (Instr.x _) :: gs => hcnt gs
  | (Instr.cnot _ _ _) :: gs => hcnt gs

private def pmap {n : ℕ} (perm : Instr n → Bits n → Bits n) :
    List (Instr n) → Bits n → List Bool → Bits n
  | [], y, _ => y
  | (Instr.h i) :: gs, y, bits =>
      Function.update (pmap perm gs y bits.tail) i (bits.headD false)
  | (Instr.s j) :: gs, y, bits => perm (Instr.s j) (pmap perm gs y bits)
  | (Instr.t j) :: gs, y, bits => perm (Instr.t j) (pmap perm gs y bits)
  | (Instr.x j) :: gs, y, bits => perm (Instr.x j) (pmap perm gs y bits)
  | (Instr.cnot a b hab) :: gs, y, bits => perm (Instr.cnot a b hab) (pmap perm gs y bits)

private noncomputable def pamp {n : ℕ} (coef : Instr n → Bits n → ℂ)
    (perm : Instr n → Bits n → Bits n) :
    List (Instr n) → Bits n → List Bool → ℂ
  | [], _, _ => 1
  | (Instr.h i) :: gs, y, bits =>
      pamp coef perm gs y bits.tail * hMat (pmap perm gs y bits.tail i) (bits.headD false)
  | (Instr.s j) :: gs, y, bits =>
      pamp coef perm gs y bits * coef (Instr.s j) (pmap perm gs y bits)
  | (Instr.t j) :: gs, y, bits =>
      pamp coef perm gs y bits * coef (Instr.t j) (pmap perm gs y bits)
  | (Instr.x j) :: gs, y, bits =>
      pamp coef perm gs y bits * coef (Instr.x j) (pmap perm gs y bits)
  | (Instr.cnot a b hab) :: gs, y, bits =>
      pamp coef perm gs y bits * coef (Instr.cnot a b hab) (pmap perm gs y bits)

/-! ### Elementary rewriting lemmas -/

private lemma pmap_cons_nonh {n : ℕ} (perm : Instr n → Bits n → Bits n) (g : Instr n)
    (hg : ∀ i, g ≠ Instr.h i) (gs : List (Instr n)) (y : Bits n) (bits : List Bool) :
    pmap perm (g :: gs) y bits = perm g (pmap perm gs y bits) := by
  cases g with
  | h i => exact absurd rfl (hg i)
  | s j => first | rfl | simp [pmap]
  | t j => first | rfl | simp [pmap]
  | x j => first | rfl | simp [pmap]
  | cnot a b hab => first | rfl | simp [pmap]

private lemma pamp_cons_nonh {n : ℕ} (coef : Instr n → Bits n → ℂ)
    (perm : Instr n → Bits n → Bits n) (g : Instr n) (hg : ∀ i, g ≠ Instr.h i)
    (gs : List (Instr n)) (y : Bits n) (bits : List Bool) :
    pamp coef perm (g :: gs) y bits
      = pamp coef perm gs y bits * coef g (pmap perm gs y bits) := by
  cases g with
  | h i => exact absurd rfl (hg i)
  | s j => first | rfl | simp [pamp]
  | t j => first | rfl | simp [pamp]
  | x j => first | rfl | simp [pamp]
  | cnot a b hab => first | rfl | simp [pamp]

private lemma hcnt_cons_nonh {n : ℕ} (g : Instr n) (hg : ∀ i, g ≠ Instr.h i)
    (gs : List (Instr n)) : hcnt (g :: gs) = hcnt gs := by
  cases g with
  | h i => exact absurd rfl (hg i)
  | s j => first | rfl | simp [hcnt]
  | t j => first | rfl | simp [hcnt]
  | x j => first | rfl | simp [hcnt]
  | cnot a b hab => first | rfl | simp [hcnt]

/-! ### Summing over `Fin k → Bool` -/

private lemma sum_zero_index {M : Type*} [AddCommMonoid M] {k : ℕ} (hk : k = 0)
    (f : (Fin k → Bool) → M) (x : Fin k → Bool) : ∑ b : Fin k → Bool, f b = f x := by
  subst hk
  exact Fintype.sum_subsingleton f x

private def consEq (k : ℕ) : (Bool × (Fin k → Bool)) ≃ (Fin (k + 1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun g := (g 0, Fin.tail g)
  left_inv := by rintro ⟨c, b⟩; simp
  right_inv := by intro g; simp [Fin.cons_self_tail]

private lemma sum_pi_bool_succ {M : Type*} [AddCommMonoid M] {k : ℕ}
    (f : (Fin (k + 1) → Bool) → M) :
    ∑ b : Fin (k + 1) → Bool, f b = ∑ c : Bool, ∑ b : Fin k → Bool, f (Fin.cons c b) := by
  have h1 : ∑ b : Fin (k + 1) → Bool, f b
      = ∑ p : Bool × (Fin k → Bool), f (Fin.cons p.1 p.2) := by
    refine Fintype.sum_equiv (consEq k).symm f (fun p => f (Fin.cons p.1 p.2)) ?_
    intro x
    simp [consEq, Fin.cons_self_tail]
  rw [h1, Fintype.sum_prod_type]

private lemma sum_pi_bool_two {M : Type*} [AddCommMonoid M] (f : (Fin 2 → Bool) → M) :
    ∑ b : Fin 2 → Bool, f b
      = ∑ c : Bool, ∑ d : Bool, f (Fin.cons c (Fin.cons d (fun _ => false))) := by
  refine Eq.trans (sum_pi_bool_succ (k := 1) f) ?_
  refine Finset.sum_congr rfl (fun c _ => ?_)
  refine Eq.trans (sum_pi_bool_succ (k := 0) (fun b => f (Fin.cons c b))) ?_
  refine Finset.sum_congr rfl (fun d _ => ?_)
  exact Fintype.sum_subsingleton _ (fun _ => false)

private lemma ofFn_cons_bool {k : ℕ} (c : Bool) (b : Fin k → Bool) :
    List.ofFn (Fin.cons c b : Fin (k + 1) → Bool) = c :: List.ofFn b := by
  rw [List.ofFn_succ]
  simp

/-! ### The Hadamard coefficient is `(√2)⁻¹` times a power of `ω` -/

private lemma om_pow_four : (Complex.exp (Complex.I * Real.pi / 4)) ^ 4 = -1 := by
  have h : (Complex.exp (Complex.I * Real.pi / 4)) ^ 4
      = Complex.exp (Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4
          + Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4) := by
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]
    ring
  have h2 : Complex.I * (Real.pi : ℂ) / 4 + Complex.I * (Real.pi : ℂ) / 4
      + Complex.I * (Real.pi : ℂ) / 4 + Complex.I * (Real.pi : ℂ) / 4
      = (Real.pi : ℂ) * Complex.I := by
    ring
  rw [h, h2, Complex.exp_pi_mul_I]

private lemma hMat_eq (a c : Bool) :
    hMat a c = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
      * (Complex.exp (Complex.I * Real.pi / 4)) ^ (if a && c then 4 else 0) := by
  cases a <;> cases c <;> simp [hMat, om_pow_four]

/-! ### The induction -/

private lemma key_nonh {n : ℕ} (coef : Instr n → Bits n → ℂ) (perm : Instr n → Bits n → Bits n)
    (hNH : ∀ g : Instr n, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState n) (x : Bits n),
        Instr.apply g ψ x = coef g x * ψ (perm g x))
    (g : Instr n) (hg : ∀ i, g ≠ Instr.h i) (gs : List (Instr n))
    (ih : ∀ (ψ : QState n) (y : Bits n),
      (gs.foldl (fun st g' => Instr.apply g' st) ψ) y
        = ∑ b : Fin (hcnt gs) → Bool,
            pamp coef perm gs y (List.ofFn b) * ψ (pmap perm gs y (List.ofFn b)))
    (ψ : QState n) (y : Bits n) :
    ((g :: gs).foldl (fun st g' => Instr.apply g' st) ψ) y
      = ∑ b : Fin (hcnt gs) → Bool,
          pamp coef perm (g :: gs) y (List.ofFn b)
            * ψ (pmap perm (g :: gs) y (List.ofFn b)) := by
  simp only [List.foldl_cons]
  rw [ih]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [hNH g hg, pamp_cons_nonh coef perm g hg, pmap_cons_nonh perm g hg]
  ring

private lemma key_h {n : ℕ} (coef : Instr n → Bits n → ℂ) (perm : Instr n → Bits n → Bits n)
    (i : Fin n) (gs : List (Instr n))
    (ih : ∀ (ψ : QState n) (y : Bits n),
      (gs.foldl (fun st g' => Instr.apply g' st) ψ) y
        = ∑ b : Fin (hcnt gs) → Bool,
            pamp coef perm gs y (List.ofFn b) * ψ (pmap perm gs y (List.ofFn b)))
    (ψ : QState n) (y : Bits n) :
    ((Instr.h i :: gs).foldl (fun st g' => Instr.apply g' st) ψ) y
      = ∑ B : Fin (hcnt gs + 1) → Bool,
          pamp coef perm (Instr.h i :: gs) y (List.ofFn B)
            * ψ (pmap perm (Instr.h i :: gs) y (List.ofFn B)) := by
  simp only [List.foldl_cons]
  rw [ih]
  have lhs0 : ∀ x : Bits n, Instr.apply (Instr.h i) ψ x
      = ∑ c : Bool, hMat (x i) c * ψ (Function.update x i c) := fun _ => rfl
  simp only [lhs0, Finset.mul_sum]
  rw [Finset.sum_comm, sum_pi_bool_succ]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [ofFn_cons_bool, pamp, pmap, List.tail_cons, List.headD_cons]
  ring

private lemma path_decomp {n : ℕ} (coef : Instr n → Bits n → ℂ) (perm : Instr n → Bits n → Bits n)
    (hNH : ∀ g : Instr n, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState n) (x : Bits n),
        Instr.apply g ψ x = coef g x * ψ (perm g x)) :
    ∀ (gs : List (Instr n)) (ψ : QState n) (y : Bits n),
      (gs.foldl (fun st g' => Instr.apply g' st) ψ) y
        = ∑ b : Fin (hcnt gs) → Bool,
            pamp coef perm gs y (List.ofFn b) * ψ (pmap perm gs y (List.ofFn b)) := by
  intro gs
  induction gs with
  | nil =>
      intro ψ y
      rw [sum_zero_index (k := hcnt ([] : List (Instr n))) rfl
        (fun b => pamp coef perm [] y (List.ofFn b) * ψ (pmap perm [] y (List.ofFn b)))
        (fun _ => false)]
      simp [pamp, pmap]
  | cons g gs ih =>
      intro ψ y
      cases g with
      | h i => exact key_h coef perm i gs ih ψ y
      | s j => exact key_nonh coef perm hNH (Instr.s j) (fun _ h => by cases h) gs ih ψ y
      | t j => exact key_nonh coef perm hNH (Instr.t j) (fun _ h => by cases h) gs ih ψ y
      | x j => exact key_nonh coef perm hNH (Instr.x j) (fun _ h => by cases h) gs ih ψ y
      | cnot a b hab =>
          exact key_nonh coef perm hNH (Instr.cnot a b hab) (fun _ h => by cases h) gs ih ψ y

/-! ### The `(√2)⁻¹ ^ h · ω ^ k` normal form -/

private lemma form_nonh {n : ℕ} (coef : Instr n → Bits n → ℂ)
    (perm : Instr n → Bits n → Bits n)
    (hco : ∀ g : Instr n, (∀ i, g ≠ Instr.h i) → ∀ x : Bits n,
        ∃ k : ℕ, coef g x = Complex.exp (Complex.I * Real.pi / 4) ^ k)
    (g : Instr n) (hg : ∀ i, g ≠ Instr.h i) (gs : List (Instr n)) (y : Bits n)
    (ih : ∃ e : (Fin (hcnt gs) → Bool) → ℕ, ∀ b : Fin (hcnt gs) → Bool,
        pamp coef perm gs y (List.ofFn b)
          = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ (hcnt gs)
              * Complex.exp (Complex.I * Real.pi / 4) ^ (e b)) :
    ∃ e : (Fin (hcnt gs) → Bool) → ℕ, ∀ b : Fin (hcnt gs) → Bool,
      pamp coef perm (g :: gs) y (List.ofFn b)
        = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ (hcnt gs)
            * Complex.exp (Complex.I * Real.pi / 4) ^ (e b) := by
  obtain ⟨e, he⟩ := ih
  choose mm hmm using fun b : Fin (hcnt gs) → Bool =>
    hco g hg (pmap perm gs y (List.ofFn b))
  refine ⟨fun b => e b + mm b, fun b => ?_⟩
  rw [pamp_cons_nonh coef perm g hg gs y (List.ofFn b), he b, hmm b]
  simp only [pow_add]
  ring

private lemma form_h {n : ℕ} (coef : Instr n → Bits n → ℂ) (perm : Instr n → Bits n → Bits n)
    (i : Fin n) (gs : List (Instr n)) (y : Bits n)
    (ih : ∃ e : (Fin (hcnt gs) → Bool) → ℕ, ∀ b : Fin (hcnt gs) → Bool,
        pamp coef perm gs y (List.ofFn b)
          = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ (hcnt gs)
              * Complex.exp (Complex.I * Real.pi / 4) ^ (e b)) :
    ∃ e : (Fin (hcnt gs + 1) → Bool) → ℕ, ∀ B : Fin (hcnt gs + 1) → Bool,
      pamp coef perm (Instr.h i :: gs) y (List.ofFn B)
        = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ (hcnt gs + 1)
            * Complex.exp (Complex.I * Real.pi / 4) ^ (e B) := by
  obtain ⟨e, he⟩ := ih
  refine ⟨fun B => e (Fin.tail B)
      + (if (pmap perm gs y (List.ofFn (Fin.tail B)) i) && (B 0) then 4 else 0), fun B => ?_⟩
  have hB : List.ofFn B = B 0 :: List.ofFn (Fin.tail B) := by
    rw [List.ofFn_succ]
    rfl
  rw [hB]
  simp only [pamp, List.tail_cons, List.headD_cons]
  rw [he, hMat_eq]
  simp only [pow_add, pow_one]
  ring

private lemma amp_form {n : ℕ} (coef : Instr n → Bits n → ℂ)
    (perm : Instr n → Bits n → Bits n)
    (hco : ∀ g : Instr n, (∀ i, g ≠ Instr.h i) → ∀ x : Bits n,
        ∃ k : ℕ, coef g x = Complex.exp (Complex.I * Real.pi / 4) ^ k) :
    ∀ (gs : List (Instr n)) (y : Bits n),
      ∃ e : (Fin (hcnt gs) → Bool) → ℕ, ∀ b : Fin (hcnt gs) → Bool,
        pamp coef perm gs y (List.ofFn b)
          = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ (hcnt gs)
              * Complex.exp (Complex.I * Real.pi / 4) ^ (e b) := by
  intro gs
  induction gs with
  | nil =>
      intro y
      exact ⟨fun _ => 0, fun b => by simp [pamp, hcnt]⟩
  | cons g gs ih =>
      intro y
      cases g with
      | h i => exact form_h coef perm i gs y (ih y)
      | s j => exact form_nonh coef perm hco (Instr.s j) (fun _ h => by cases h) gs y (ih y)
      | t j => exact form_nonh coef perm hco (Instr.t j) (fun _ h => by cases h) gs y (ih y)
      | x j => exact form_nonh coef perm hco (Instr.x j) (fun _ h => by cases h) gs y (ih y)
      | cnot a b hab =>
          exact form_nonh coef perm hco (Instr.cnot a b hab) (fun _ h => by cases h) gs y (ih y)

/-! ### One gate per layer -/

private lemma runLayered_flat {n : ℕ} (gs : List (Instr n)) (ψ : QState n) :
    runLayered (gs.map (fun g => [g])) ψ = gs.foldl (fun st g' => Instr.apply g' st) ψ := by
  unfold runLayered
  rw [List.foldl_map]
  rfl

/-! ### A concrete two-Hadamard witness on two wires -/

private abbrev gsW : List (Instr 2) := [Instr.h 0, Instr.x 1, Instr.h 0]

private noncomputable abbrev psW : QState 2 :=
  fun x => (if x 0 then (2 : ℂ) else 1) * (if x 1 then 3 else 5)

private abbrev yW : Bits 2 := fun _ => false

private abbrev coW : Instr 2 → Bits 2 → ℂ := fun _ _ => 1

private abbrev peW : Instr 2 → Bits 2 → Bits 2 := fun _ x => Function.update x 1 (!(x 1))

private lemma sqrt_two_inv_sq :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

private lemma witness_direct :
    (gsW.foldl (fun st g' => Instr.apply g' st) psW) yW = 3 := by
  have h1 : (gsW.foldl (fun st g' => Instr.apply g' st) psW) yW
      = 6 * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by
    simp [gsW, psW, yW, Instr.apply, apply1, hMat, xMat, Fintype.sum_bool,
      Function.update_apply]
    all_goals ring
  rw [h1, sqrt_two_inv_sq]
  norm_num

private lemma witness_path :
    ∑ b : Fin 2 → Bool,
        pamp coW peW gsW yW (List.ofFn b) * psW (pmap peW gsW yW (List.ofFn b)) = 3 := by
  have h2 : ∑ b : Fin 2 → Bool,
      pamp coW peW gsW yW (List.ofFn b) * psW (pmap peW gsW yW (List.ofFn b))
      = 6 * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by
    rw [sum_pi_bool_two]
    simp [Fintype.sum_bool, ofFn_cons_bool, List.ofFn_zero, gsW, psW, yW, coW, peW,
      pamp, pmap, hMat, Function.update_apply]
    all_goals ring
  rw [h2, sqrt_two_inv_sq]
  norm_num

/-! ### Bridge from BRANCH-1's per-gate existential to the uniform `coef`/`perm` data -/

private lemma skolem_nonh {m : ℕ}
    (hb : ∀ g : Instr m, (∀ i, g ≠ Instr.h i) →
        ∃ coef : Bits m → ℂ, ∃ perm : Bits m → Bits m,
          ∀ ψ : QState m, Instr.apply g ψ = fun x => coef x * ψ (perm x)) :
    ∃ (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
      ∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (x : Bits m),
        Instr.apply g ψ x = coef g x * ψ (perm g x) := by
  classical
  choose! co pe hco using hb
  exact ⟨co, pe, fun g hg ψ x => congrFun (hco g hg ψ) x⟩

private lemma witness_coef_ok (ψ : QState 2) (x : Bits 2) :
    Instr.apply (Instr.x 1) ψ x = 1 * ψ (Function.update x 1 (!(x 1))) := by
  cases hx : x 1 <;>
    simp [Instr.apply, apply1, xMat, Fintype.sum_bool, hx]


/-- The amplitude of a flat gate list, as an explicit sum over branch assignments: one bit per
Hadamard, an explicit product of per-gate coefficients (`A`), an explicit composed basis-string
map (`P`), together with the `(√2)⁻¹ ^ h · ω ^ k` normal form for every branch amplitude, the
one-gate-per-layer `runLayered` corollary, and a concrete two-Hadamard witness. -/
theorem _root_.BQPReferenceValidation.candidate26 :
    ∃ (N : ∀ m : ℕ, List (Instr m) → ℕ)
      (A : ∀ m : ℕ, (Instr m → Bits m → ℂ) → (Instr m → Bits m → Bits m) →
            List (Instr m) → Bits m → List Bool → ℂ)
      (P : ∀ m : ℕ, (Instr m → Bits m → Bits m) →
            List (Instr m) → Bits m → List Bool → Bits m),
      -- `N` counts the Hadamard gates
      (∀ m : ℕ, N m [] = 0)
    ∧ (∀ (m : ℕ) (i : Fin m) (gs : List (Instr m)), N m (Instr.h i :: gs) = N m gs + 1)
    ∧ (∀ (m : ℕ) (g : Instr m) (gs : List (Instr m)), (∀ i, g ≠ Instr.h i) →
          N m (g :: gs) = N m gs)
      -- `A` and `P` are explicit recursions over the gate list
    ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m)
          (y : Bits m) (bits : List Bool), A m coef perm [] y bits = 1)
    ∧ (∀ (m : ℕ) (perm : Instr m → Bits m → Bits m) (y : Bits m) (bits : List Bool),
          P m perm [] y bits = y)
    ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m)
          (i : Fin m) (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
          A m coef perm (Instr.h i :: gs) y bits
            = A m coef perm gs y bits.tail
                * hMat (P m perm gs y bits.tail i) (bits.headD false))
    ∧ (∀ (m : ℕ) (perm : Instr m → Bits m → Bits m)
          (i : Fin m) (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
          P m perm (Instr.h i :: gs) y bits
            = Function.update (P m perm gs y bits.tail) i (bits.headD false))
    ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m)
          (g : Instr m) (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
          (∀ i, g ≠ Instr.h i) →
          A m coef perm (g :: gs) y bits
            = A m coef perm gs y bits * coef g (P m perm gs y bits))
    ∧ (∀ (m : ℕ) (perm : Instr m → Bits m → Bits m)
          (g : Instr m) (gs : List (Instr m)) (y : Bits m) (bits : List Bool),
          (∀ i, g ≠ Instr.h i) →
          P m perm (g :: gs) y bits = perm g (P m perm gs y bits))
      -- the path decomposition for a flat gate list
    ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
          (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (x : Bits m),
              Instr.apply g ψ x = coef g x * ψ (perm g x)) →
          ∀ (gs : List (Instr m)) (ψ : QState m) (y : Bits m),
            (gs.foldl (fun st g => Instr.apply g st) ψ) y
              = ∑ b : Fin (N m gs) → Bool,
                  A m coef perm gs y (List.ofFn b) * ψ (P m perm gs y (List.ofFn b)))
      -- the same for a one-gate-per-layer `runLayered` circuit
    ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
          (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (x : Bits m),
              Instr.apply g ψ x = coef g x * ψ (perm g x)) →
          ∀ (gs : List (Instr m)) (ψ : QState m) (y : Bits m),
            runLayered (gs.map (fun g => [g])) ψ y
              = ∑ b : Fin (N m gs) → Bool,
                  A m coef perm gs y (List.ofFn b) * ψ (P m perm gs y (List.ofFn b)))
      -- every branch amplitude is `(√2)⁻¹ ^ h` times a power of `ω = exp (iπ/4)`
    ∧ (∀ (m : ℕ) (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
          (∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ x : Bits m,
              ∃ k : ℕ, coef g x = Complex.exp (Complex.I * Real.pi / 4) ^ k) →
          ∀ (gs : List (Instr m)) (y : Bits m),
            ∃ e : (Fin (N m gs) → Bool) → ℕ, ∀ b : Fin (N m gs) → Bool,
              A m coef perm gs y (List.ofFn b)
                = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ (N m gs)
                    * Complex.exp (Complex.I * Real.pi / 4) ^ (e b))
      -- non-vacuity: two Hadamards and one non-Hadamard gate on two wires, four branches,
      -- the fold and the path sum computed independently
    ∧ N 2 [Instr.h 0, Instr.x 1, Instr.h 0] = 2
    ∧ (([Instr.h 0, Instr.x 1, Instr.h 0] : List (Instr 2)).foldl
          (fun st g => Instr.apply g st)
          (fun x => (if x 0 then (2 : ℂ) else 1) * (if x 1 then 3 else 5)))
          (fun _ => false) = 3
    ∧ (∑ b : Fin 2 → Bool,
          A 2 (fun _ _ => 1) (fun _ x => Function.update x 1 (!(x 1)))
              [Instr.h 0, Instr.x 1, Instr.h 0] (fun _ => false) (List.ofFn b)
            * (fun x : Bits 2 => (if x 0 then (2 : ℂ) else 1) * (if x 1 then 3 else 5))
                (P 2 (fun _ x => Function.update x 1 (!(x 1)))
                  [Instr.h 0, Instr.x 1, Instr.h 0] (fun _ => false) (List.ofFn b))) = 3
    ∧ (∀ (ψ : QState 2) (x : Bits 2),
          Instr.apply (Instr.x 1) ψ x = 1 * ψ (Function.update x 1 (!(x 1))))
      -- BRANCH-1's per-gate existential supplies the `coef`/`perm` data used above
    ∧ (∀ m : ℕ,
          (∀ g : Instr m, (∀ i, g ≠ Instr.h i) →
              ∃ coef : Bits m → ℂ, ∃ perm : Bits m → Bits m,
                ∀ ψ : QState m, Instr.apply g ψ = fun x => coef x * ψ (perm x)) →
          ∃ (coef : Instr m → Bits m → ℂ) (perm : Instr m → Bits m → Bits m),
            ∀ g : Instr m, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState m) (x : Bits m),
              Instr.apply g ψ x = coef g x * ψ (perm g x)) := by
  refine ⟨fun m => @hcnt m, fun m => @pamp m, fun m => @pmap m, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    first | rfl | simp [hcnt]
  · intro m i gs
    first | rfl | simp [hcnt]
  · intro m g gs hg
    exact hcnt_cons_nonh g hg gs
  · intro m coef perm y bits
    first | rfl | simp [pamp]
  · intro m perm y bits
    first | rfl | simp [pmap]
  · intro m coef perm i gs y bits
    first | rfl | simp [pamp]
  · intro m perm i gs y bits
    first | rfl | simp [pmap]
  · intro m coef perm g gs y bits hg
    exact pamp_cons_nonh coef perm g hg gs y bits
  · intro m perm g gs y bits hg
    exact pmap_cons_nonh perm g hg gs y bits
  · intro m coef perm hNH gs ψ y
    exact path_decomp coef perm hNH gs ψ y
  · intro m coef perm hNH gs ψ y
    rw [runLayered_flat]
    exact path_decomp coef perm hNH gs ψ y
  · intro m coef perm hco gs y
    exact amp_form coef perm hco gs y
  · first | rfl | simp [hcnt]
  · exact witness_direct
  · exact witness_path
  · intro ψ x
    exact witness_coef_ok ψ x
  · intro m hb
    exact skolem_nonh hb

end BQPReferenceValidation.Source26

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate26
    let target ← getConstInfo ``ShiShallow.circuit_amplitude_is_a_path_sum_over_hadamard_branches
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiShallow.circuit_amplitude_is_a_path_sum_over_hadamard_branches"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiShallow.circuit_amplitude_is_a_path_sum_over_hadamard_branches"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiShallow.circuit_amplitude_is_a_path_sum_over_hadamard_branches"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate26
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiShallow.circuit_amplitude_is_a_path_sum_over_hadamard_branches; axioms {axioms}"
