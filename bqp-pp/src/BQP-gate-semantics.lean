import «BQP-closed-references»

/-! Concrete gate data for the path expansion. No gate-action or phase
hypotheses are assumed: both are derived from the original circuit definitions. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace BQPGates
open ShiShallow

noncomputable def omega : ℂ := Complex.exp (Complex.I * Real.pi / 4)

def exponent {n : ℕ} (g : Instr n) (x : Bits n) : ℕ :=
  match g with
  | .s i => if x i then 2 else 0
  | .t i => if x i then 1 else 0
  | _ => 0

def predecessor {n : ℕ} (g : Instr n) (x : Bits n) : Bits n :=
  match g with
  | .x i => Function.update x i (!(x i))
  | .cnot i j _ => Function.update x j (xor (x j) (x i))
  | _ => x

noncomputable def coefficient {n : ℕ} (g : Instr n) (x : Bits n) : ℂ :=
  omega ^ exponent g x

private theorem diagonal {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n)
    (ψ : QState n) (x : Bits n) (hU : ∀ a b, a ≠ b → U a b = 0) :
    apply1 U i ψ x = U (x i) (x i) * ψ x := by
  unfold apply1
  rw [Finset.sum_eq_single (x i)]
  · simp
  · intro b _ hb
    rw [hU _ _ (Ne.symm hb)]
    simp
  · simp

theorem omega_sq : omega ^ 2 = Complex.I :=
  (BQPChecked.reference12.1 omega rfl).2.2.2.1

/-- The non-Hadamard transition used by the path expansion is the actual gate action. -/
theorem apply_non_hadamard {n : ℕ} (g : Instr n)
    (hg : ∀ i, g ≠ Instr.h i) (ψ : QState n) (x : Bits n) :
    Instr.apply g ψ x = coefficient g x * ψ (predecessor g x) := by
  cases g with
  | h i => exact False.elim (hg i rfl)
  | s i =>
      change apply1 sMat i ψ x = _
      rw [diagonal sMat i ψ x (by intro a b hab; simp [sMat, hab])]
      cases hx : x i <;> simp [sMat, coefficient, exponent, predecessor, hx, omega_sq]
  | t i =>
      change apply1 tMat i ψ x = _
      rw [diagonal tMat i ψ x (by intro a b hab; simp [tMat, hab])]
      cases hx : x i <;> simp [tMat, coefficient, exponent, predecessor, hx, omega]
  | x i =>
      change apply1 xMat i ψ x = _
      rw [apply1, Fintype.sum_bool]
      cases hx : x i <;> simp [xMat, coefficient, exponent, predecessor, hx]
  | cnot i j hij =>
      simp [Instr.apply, cnotState, coefficient, exponent, predecessor]

theorem coefficient_is_eighth_root {n : ℕ} (g : Instr n) (x : Bits n) :
    ∃ k : ℕ, coefficient g x = Complex.exp (Complex.I * Real.pi / 4) ^ k :=
  ⟨exponent g x, rfl⟩

/-- The classical part of each gate is an involution; CNOT retains its distinct-wire premise. -/
theorem predecessor_involutive {n : ℕ} (g : Instr n) :
    Function.Involutive (predecessor g) := by
  intro x
  cases g with
  | h i => rfl
  | s i => rfl
  | t i => rfl
  | x i =>
      funext k
      by_cases hk : k = i
      · subst k
        simp [predecessor]
      · simp [predecessor, Function.update_of_ne hk]
  | cnot i j hij =>
      funext k
      by_cases hk : k = j
      · subst k
        simp only [predecessor, Function.update_self, Function.update_of_ne hij]
        cases x j <;> cases x i <;> rfl
      · simp [predecessor, Function.update_of_ne hk]

def forward {n : ℕ} (g : Instr n) (a : Bool) (x : Bits n) : Bits n :=
  match g with
  | .h i => Function.update x i a
  | _ => predecessor g x

theorem forward_non_hadamard {n : ℕ} (g : Instr n) (hg : ∀ i, g ≠ Instr.h i)
    (a : Bool) (x : Bits n) : forward g a x = predecessor g x := by
  cases g with
  | h i => exact False.elim (hg i rfl)
  | s i => rfl
  | t i => rfl
  | x i => rfl
  | cnot i j hij => rfl

/-- A weighted-permutation description of the real gate has a uniquely determined
basis-state map, since the genuine coefficient is never zero. -/
theorem predecessor_unique {n : ℕ} (g : Instr n) (hg : ∀ i, g ≠ Instr.h i)
    (c : Bits n → ℂ) (p : Bits n → Bits n)
    (hp : ∀ (ψ : QState n) (x : Bits n), Instr.apply g ψ x = c x * ψ (p x))
    (x : Bits n) : p x = predecessor g x := by
  classical
  by_contra hne
  let ψ : QState n := fun z => if z = predecessor g x then 1 else 0
  have he := (apply_non_hadamard g hg ψ x).symm.trans (hp ψ x)
  have hz : coefficient g x = 0 := by simpa [ψ, hne] using he
  exact (pow_ne_zero (exponent g x) (Complex.exp_ne_zero _)) hz

/-- This closes the universally quantified inverse-map premise of BRIDGE-SIMh. -/
theorem compatible_map_inverts_forward {n : ℕ}
    (coef : Instr n → Bits n → ℂ) (perm : Instr n → Bits n → Bits n)
    (hsem : ∀ g : Instr n, (∀ i, g ≠ Instr.h i) → ∀ (ψ : QState n) (z : Bits n),
      Instr.apply g ψ z = coef g z * ψ (perm g z))
    (g : Instr n) (hg : ∀ i, g ≠ Instr.h i) (a : Bool) (z : Bits n) :
    perm g (forward g a z) = z := by
  rw [predecessor_unique g hg (coef g) (perm g) (hsem g hg), forward_non_hadamard g hg]
  exact predecessor_involutive g z

/-- Flattening preserves the order of gate execution, including empty layers. -/
theorem runLayered_flatten {n : ℕ} (c : Layered n) (ψ : QState n) :
    runLayered c ψ = c.flatten.foldl (fun st g => Instr.apply g st) ψ := by
  induction c generalizing ψ with
  | nil => rfl
  | cons l c ih =>
      simp only [runLayered, List.foldl_cons, List.flatten_cons, List.foldl_append]
      exact ih (runLayer l ψ)

/-- A path expansion for the actual gate set, with both semantic premises discharged.
The next interface is relating these backward paths to the compiled forward checker. -/
theorem concrete_path_expansion :
    ∃ (N : ∀ n : ℕ, List (Instr n) → ℕ)
      (A : ∀ n : ℕ, List (Instr n) → Bits n → List Bool → ℂ)
      (P : ∀ n : ℕ, List (Instr n) → Bits n → List Bool → Bits n),
      (∀ (n : ℕ) (gs : List (Instr n)), N n gs =
        gs.countP (fun g => match g with | .h _ => true | _ => false)) ∧
      (∀ (n : ℕ) (c : Layered n) (ψ : QState n) (y : Bits n),
        runLayered c ψ y = ∑ b : Fin (N n c.flatten) → Bool,
          A n c.flatten y (List.ofFn b) * ψ (P n c.flatten y (List.ofFn b))) ∧
      (∀ (n : ℕ) (gs : List (Instr n)) (y : Bits n),
        ∃ e : (Fin (N n gs) → Bool) → ℕ, ∀ b : Fin (N n gs) → Bool,
          A n gs y (List.ofFn b) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ N n gs * omega ^ e b) := by
  obtain ⟨N, A, P, hN0, hNh, hNg, hA0, hP0, hAh, hPh, hAg, hPg,
    hflat, hsingle, hphase, hrest⟩ := BQPChecked.reference26
  refine ⟨N, (fun n => A n coefficient predecessor), (fun n => P n predecessor), ?_, ?_, ?_⟩
  · intro n gs
    induction gs with
    | nil => simpa using hN0 n
    | cons g gs ih =>
        cases g with
        | h i => rw [hNh, ih]; simp
        | s i => rw [hNg n (.s i) gs (by intro j; simp), ih]; simp
        | t i => rw [hNg n (.t i) gs (by intro j; simp), ih]; simp
        | x i => rw [hNg n (.x i) gs (by intro j; simp), ih]; simp
        | cnot i j hij => rw [hNg n (.cnot i j hij) gs (by intro k; simp), ih]; simp
  · intro n c ψ y
    rw [runLayered_flatten]
    exact hflat n coefficient predecessor
      (fun g hg ψ x => apply_non_hadamard g hg ψ x) c.flatten ψ y
  · intro n gs y
    exact hphase n coefficient predecessor
      (fun g _ x => coefficient_is_eighth_root g x) gs y

end BQPGates
