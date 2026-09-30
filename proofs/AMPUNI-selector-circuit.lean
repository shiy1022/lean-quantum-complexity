import «AMPUNI-centering-reference-closure»
import «AMPUNI-computable-centering»

/-! Concrete centering circuit components, checked together to avoid repeated
imports of the large recovered QMA library. No theorem below assumes a circuit
or an encoding transducer with the desired acceptance behavior. -/

/-! ## AMPUNI-selector-circuit -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace ShiQMACenteringCircuit
open ShiShallow ShiExplicitCirc

private theorem wire_ne {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w)
    {i j : Fin 4} (h : i ≠ j) : w i ≠ w j := fun he => h (hw he)

/-- Clean reference proof of the explicit 37-gate Toffoli, specialized to a
four-wire interface. All gates remain explicit terms in the resulting circuit. -/
private theorem toff_spec {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∀ ψ : QState N,
      runLayered (toffCirc (w i) (w j) (w k)
        (wire_ne w hw hij) (wire_ne w hw hik) (wire_ne w hw hjk)) ψ =
      fun x => ψ (Function.update x (w k) (xor (x (w k)) (x (w i) && x (w j))))) ∧
    (∀ l ∈ toffCirc (w i) (w j) (w k)
      (wire_ne w hw hij) (wire_ne w hw hik) (wire_ne w hw hjk), LayerOk l) := by
  obtain ⟨tof, heq, hact, hwf, _⟩ :=
    (ShiQMACenteringReference.toffoli
      (w i) (w j) (w k) (wire_ne w hw hij) (wire_ne w hw hik) (wire_ne w hw hjk)
      (w 0) (w 1) (w 2) (w 3)
      (wire_ne w hw (by decide : (0 : Fin 4) ≠ 1))
      (wire_ne w hw (by decide : (0 : Fin 4) ≠ 2))
      (wire_ne w hw (by decide : (1 : Fin 4) ≠ 2))
      (wire_ne w hw (by decide : (0 : Fin 4) ≠ 3))
      (wire_ne w hw (by decide : (1 : Fin 4) ≠ 3))
      (wire_ne w hw (by decide : (2 : Fin 4) ≠ 3)) 0).1
  subst tof
  exact ⟨hact, hwf⟩

/-- Wire order: fair selector, verifier output, coin output, fresh result.
The result is XORed with the selected input, making this a reversible circuit. -/
def selectorCirc {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w) : Layered N :=
  ([[Instr.cnot (w 2) (w 3) (wire_ne w hw (by decide))]] ++
    toffCirc (w 0) (w 2) (w 3)
      (wire_ne w hw (by decide)) (wire_ne w hw (by decide)) (wire_ne w hw (by decide))) ++
    toffCirc (w 0) (w 1) (w 3)
      (wire_ne w hw (by decide)) (wire_ne w hw (by decide)) (wire_ne w hw (by decide))

private theorem selector_run_append {N : Nat} (a b : Layered N) (ψ : QState N) :
    runLayered (a ++ b) ψ = runLayered b (runLayered a ψ) := by
  simp [runLayered, List.foldl_append]

/-- Exact amplitude action, valid on arbitrary states, including entangled states. -/
theorem selectorCirc_action {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w)
    (ψ : QState N) :
    runLayered (selectorCirc w hw) ψ = fun x =>
      ψ (Function.update x (w 3) (xor (x (w 3)) (if x (w 0) then x (w 1) else x (w 2)))) := by
  have h02 := toff_spec w hw 0 2 3 (by decide) (by decide) (by decide)
  have h01 := toff_spec w hw 0 1 3 (by decide) (by decide) (by decide)
  rw [selectorCirc, selector_run_append, selector_run_append, h01.1, h02.1]
  funext x
  simp only [runLayered, runLayer, List.foldl_cons, List.foldl_nil, Instr.apply, cnotState]
  have h03 : w 0 ≠ w 3 := wire_ne w hw (by decide)
  have h13 : w 1 ≠ w 3 := wire_ne w hw (by decide)
  have h23 : w 2 ≠ w 3 := wire_ne w hw (by decide)
  simp only [Function.update_self, Function.update_of_ne h03, Function.update_of_ne h13,
    Function.update_of_ne h23, Function.update_idem]
  congr 2
  cases x (w 0) <;> cases x (w 1) <;> cases x (w 2) <;> cases x (w 3) <;> rfl

theorem selectorCirc_depth {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w) :
    depth (selectorCirc w hw) = 75 := by
  simp [selectorCirc, depth, toffCirc, toffGates]

theorem selectorCirc_wellFormed {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w) :
    ∀ l ∈ selectorCirc w hw, LayerOk l := by
  intro l hl
  rcases List.mem_append.mp hl with h | h
  · rcases List.mem_append.mp h with h | h
    · simp only [List.mem_singleton] at h
      subst l
      simp [LayerOk]
    · exact (toff_spec w hw 0 2 3 (by decide) (by decide) (by decide)).2 l h
  · exact (toff_spec w hw 0 1 3 (by decide) (by decide) (by decide)).2 l h

/-- The reversible Boolean transformation implemented by the selector. -/
def selectorMap {N : Nat} (w : Fin 4 → Fin N) (x : Bits N) : Bits N :=
  Function.update x (w 3) (xor (x (w 3)) (if x (w 0) then x (w 1) else x (w 2)))

theorem selectorMap_involutive {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w) :
    Function.Involutive (selectorMap w) := by
  intro x
  have h03 : w 0 ≠ w 3 := wire_ne w hw (by decide)
  have h13 : w 1 ≠ w 3 := wire_ne w hw (by decide)
  have h23 : w 2 ≠ w 3 := wire_ne w hw (by decide)
  simp only [selectorMap, Function.update_self, Function.update_of_ne h03,
    Function.update_of_ne h13, Function.update_of_ne h23, Function.update_idem]
  have hb : xor (xor (x (w 3)) (if x (w 0) then x (w 1) else x (w 2)))
      (if x (w 0) then x (w 1) else x (w 2)) = x (w 3) := by
    cases x (w 0) <;> cases x (w 1) <;> cases x (w 2) <;> cases x (w 3) <;> rfl
  rw [hb]
  exact Function.update_eq_self _ _

/-- Measurement of a zero-initialized result wire after the concrete selector
is exactly measurement of the selected Boolean event on the original state.
No product-state assumption is made. -/
theorem selectorCirc_accept_weight {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w)
    (ψ : QState N) (hz : ∀ x : Bits N, x (w 3) = true → ψ x = 0) :
    (∑ x : Bits N, if x (w 3) then ‖runLayered (selectorCirc w hw) ψ x‖ ^ 2 else 0) =
      ∑ x : Bits N, if (if x (w 0) then x (w 1) else x (w 2)) then ‖ψ x‖ ^ 2 else 0 := by
  let e : Bits N ≃ Bits N := {
    toFun := selectorMap w
    invFun := selectorMap w
    left_inv := selectorMap_involutive w hw
    right_inv := selectorMap_involutive w hw }
  have he := e.sum_comp (fun x : Bits N =>
    if x (w 3) then ‖runLayered (selectorCirc w hw) ψ x‖ ^ 2 else 0)
  rw [← he]
  apply Finset.sum_congr rfl
  intro x _
  have hact : runLayered (selectorCirc w hw) ψ (e x) = ψ x := by
    rw [selectorCirc_action]
    exact congrArg ψ (selectorMap_involutive w hw x)
  rw [hact]
  by_cases ho : x (w 3) = true
  · rw [hz x ho]
    simp
  · have hf : x (w 3) = false := Bool.eq_false_iff.mpr ho
    change (if (selectorMap w x) (w 3) then ‖ψ x‖ ^ 2 else 0) = _
    simp [selectorMap, hf]

theorem selectorCirc_total_weight {N : Nat} (w : Fin 4 → Fin N)
    (hw : Function.Injective w) (ψ : QState N) :
    (∑ x : Bits N, ‖runLayered (selectorCirc w hw) ψ x‖ ^ 2) =
      ∑ x : Bits N, ‖ψ x‖ ^ 2 := by
  let e : Bits N ≃ Bits N := {
    toFun := selectorMap w
    invFun := selectorMap w
    left_inv := selectorMap_involutive w hw
    right_inv := selectorMap_involutive w hw }
  rw [selectorCirc_action]
  exact e.sum_comp (fun x => ‖ψ x‖ ^ 2)

theorem selectorCirc_event_weight {N : Nat} (w : Fin 4 → Fin N)
    (hw : Function.Injective w) (ψ : QState N) (a : Bits N → Bool) :
    (∑ x : Bits N, if a x then ‖runLayered (selectorCirc w hw) ψ x‖ ^ 2 else 0) =
      ∑ x : Bits N, if a (selectorMap w x) then ‖ψ x‖ ^ 2 else 0 := by
  let e : Bits N ≃ Bits N := {
    toFun := selectorMap w
    invFun := selectorMap w
    left_inv := selectorMap_involutive w hw
    right_inv := selectorMap_involutive w hw }
  have he := e.sum_comp (fun x : Bits N => if a x then
    ‖runLayered (selectorCirc w hw) ψ x‖ ^ 2 else 0)
  rw [← he]
  apply Finset.sum_congr rfl
  intro x _
  have hact : runLayered (selectorCirc w hw) ψ (e x) = ψ x := by
    rw [selectorCirc_action]
    exact congrArg ψ (selectorMap_involutive w hw x)
  rw [hact]
  rfl

end ShiQMACenteringCircuit



/-! ## AMPUNI-fair-selector -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace ShiQMACenteringCircuit
open ShiShallow

def flipBit {N : Nat} (i : Fin N) (x : Bits N) : Bits N :=
  Function.update x i (!x i)

theorem flipBit_involutive {N : Nat} (i : Fin N) : Function.Involutive (flipBit i) := by
  intro x
  simp [flipBit, Function.update_idem]

private theorem set_false_after_flip {N : Nat} (i : Fin N) (x : Bits N) (hx : x i = false) :
    Function.update (flipBit i x) i false = x := by
  simp only [flipBit, Function.update_idem]
  simpa only [hx] using Function.update_eq_self i x

/-- A fresh fair selector averages the weights of two events. -/
theorem fair_event_weight {N : Nat} (i : Fin N) (p : Bits N → ℝ)
    (hp : ∀ x, x i = true → p x = 0) (a b : Bits N → Bool)
    (ha : ∀ x, a (flipBit i x) = a x) :
    (∑ x : Bits N, if (if x i then a x else b x) then
      p (Function.update x i false) / 2 else 0) =
      ((∑ x : Bits N, if a x then p x else 0) +
        (∑ x : Bits N, if b x then p x else 0)) / 2 := by
  let e : Bits N ≃ Bits N := {
    toFun := flipBit i
    invFun := flipBit i
    left_inv := flipBit_involutive i
    right_inv := flipBit_involutive i }
  have ht : (∑ x : Bits N, if x i then
      (if a x then p (Function.update x i false) / 2 else 0) else 0) =
      (∑ x : Bits N, if a x then p x else 0) / 2 := by
    have he := e.sum_comp (fun x : Bits N => if x i then
      (if a x then p (Function.update x i false) / 2 else 0) else 0)
    rw [← he, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    change (if (flipBit i x) i then
      (if a (flipBit i x) then p (Function.update (flipBit i x) i false) / 2 else 0) else 0) = _
    rw [ha]
    cases hx : x i
    · rw [set_false_after_flip i x hx]
      simp [flipBit, hx, ite_div]
    · simp [flipBit, hx, hp x hx]
  have hf : (∑ x : Bits N, if x i then 0 else
      (if b x then p (Function.update x i false) / 2 else 0)) =
      (∑ x : Bits N, if b x then p x else 0) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    cases hx : x i
    · have hu : Function.update x i false = x := by
        simpa only [hx] using Function.update_eq_self i x
      simp [hu, ite_div]
    · simp [hp x hx]
  calc
    _ = (∑ x : Bits N, if x i then
        (if a x then p (Function.update x i false) / 2 else 0) else 0) +
        (∑ x : Bits N, if x i then 0 else
        (if b x then p (Function.update x i false) / 2 else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      cases x i <;> simp
    _ = _ := by rw [ht, hf]; ring

theorem hadamard_zero_action {N : Nat} (i : Fin N) (ψ : QState N)
    (hz : ∀ x : Bits N, x i = true → ψ x = 0) (x : Bits N) :
    apply1 hMat i ψ x = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ψ (Function.update x i false) := by
  have ht := hz (Function.update x i true) (by simp)
  simp [apply1, hMat, Fintype.sum_bool, ht]

theorem hadamard_zero_weight {N : Nat} (i : Fin N) (ψ : QState N)
    (hz : ∀ x : Bits N, x i = true → ψ x = 0) (x : Bits N) :
    ‖apply1 hMat i ψ x‖ ^ 2 = ‖ψ (Function.update x i false)‖ ^ 2 / 2 := by
  rw [hadamard_zero_action i ψ hz x, norm_mul, mul_pow]
  have hh : ‖((Real.sqrt 2 : ℝ) : ℂ)⁻¹‖ ^ 2 = (1 : ℝ) / 2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hh]
  ring

/-- One Hadamard followed by the explicit reversible selector. -/
def fairSelectorCirc {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w) : Layered N :=
  [[Instr.h (w 0)]] ++ selectorCirc w hw

/-- Exact affine acceptance formula for the concrete 76-layer circuit.
Only the selector and result wires must initially be zero. The other wires may
be arbitrarily entangled, and normalization is not needed for this identity. -/
theorem fairSelectorCirc_accept_weight {N : Nat} (w : Fin 4 → Fin N)
    (hw : Function.Injective w) (ψ : QState N)
    (hs : ∀ x : Bits N, x (w 0) = true → ψ x = 0)
    (ho : ∀ x : Bits N, x (w 3) = true → ψ x = 0) :
    (∑ x : Bits N, if x (w 3) then ‖runLayered (fairSelectorCirc w hw) ψ x‖ ^ 2 else 0) =
      ((∑ x : Bits N, if x (w 1) then ‖ψ x‖ ^ 2 else 0) +
        (∑ x : Bits N, if x (w 2) then ‖ψ x‖ ^ 2 else 0)) / 2 := by
  have h30 : w 3 ≠ w 0 := fun h => (by decide : (3 : Fin 4) ≠ 0) (hw h)
  have h10 : w 1 ≠ w 0 := fun h => (by decide : (1 : Fin 4) ≠ 0) (hw h)
  have hout : ∀ x : Bits N, x (w 3) = true → apply1 hMat (w 0) ψ x = 0 := by
    intro x hx
    rw [hadamard_zero_action _ _ hs]
    have he : (Function.update x (w 0) false) (w 3) = true := by
      simpa [Function.update_of_ne h30] using hx
    rw [ho _ he, mul_zero]
  have hrun : runLayered (fairSelectorCirc w hw) ψ =
      runLayered (selectorCirc w hw) (apply1 hMat (w 0) ψ) := by
    simp [fairSelectorCirc, runLayered, List.foldl_append, runLayer, Instr.apply]
  rw [hrun, selectorCirc_accept_weight w hw _ hout]
  simp_rw [hadamard_zero_weight _ _ hs]
  apply fair_event_weight (w 0) (fun x => ‖ψ x‖ ^ 2)
  · intro x hx
    rw [hs x hx]
    simp
  · intro x
    simp [flipBit, Function.update_of_ne h10]

theorem fairSelectorCirc_depth {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w) :
    depth (fairSelectorCirc w hw) = 76 := by
  have h : (selectorCirc w hw).length = 75 := selectorCirc_depth w hw
  simp [fairSelectorCirc, depth, h]

theorem fairSelectorCirc_wellFormed {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w) :
    ∀ l ∈ fairSelectorCirc w hw, LayerOk l := by
  intro l hl
  rcases List.mem_append.mp hl with h | h
  · simp only [List.mem_singleton] at h
    subst l
    simp [LayerOk]
  · exact selectorCirc_wellFormed w hw l h

theorem hadamard_zero_total_weight {N : Nat} (i : Fin N) (ψ : QState N)
    (hs : ∀ x : Bits N, x i = true → ψ x = 0) :
    (∑ x : Bits N, ‖apply1 hMat i ψ x‖ ^ 2) = ∑ x : Bits N, ‖ψ x‖ ^ 2 := by
  simp_rw [hadamard_zero_weight i ψ hs]
  have h := fair_event_weight i (fun x => ‖ψ x‖ ^ 2)
    (fun x hx => by rw [hs x hx]; simp) (fun _ => true) (fun _ => true) (fun _ => rfl)
  simp at h
  linarith only [h]

theorem fairSelectorCirc_total_weight {N : Nat} (w : Fin 4 → Fin N)
    (hw : Function.Injective w) (ψ : QState N)
    (hs : ∀ x : Bits N, x (w 0) = true → ψ x = 0) :
    (∑ x : Bits N, ‖runLayered (fairSelectorCirc w hw) ψ x‖ ^ 2) =
      ∑ x : Bits N, ‖ψ x‖ ^ 2 := by
  have hrun : runLayered (fairSelectorCirc w hw) ψ =
      runLayered (selectorCirc w hw) (apply1 hMat (w 0) ψ) := by
    simp [fairSelectorCirc, runLayered, List.foldl_append, runLayer, Instr.apply]
  rw [hrun, selectorCirc_total_weight]
  exact hadamard_zero_total_weight _ _ hs

/-- Gates on another wire preserve a zero-support condition, even on entangled states. -/
theorem apply1_zero_other {N : Nat} (U : Matrix Bool Bool ℂ) (i j : Fin N) (hji : j ≠ i)
    (ψ : QState N) (hz : ∀ x : Bits N, x j = true → ψ x = 0) :
    ∀ x : Bits N, x j = true → apply1 U i ψ x = 0 := by
  intro x hx
  apply Finset.sum_eq_zero
  intro b _
  have he : (Function.update x i b) j = true := by simpa [Function.update_of_ne hji] using hx
  rw [hz _ he, mul_zero]

theorem fairSelectorCirc_zero_other {N : Nat} (w : Fin 4 → Fin N)
    (hw : Function.Injective w) (i : Fin N) (hi0 : i ≠ w 0) (hi3 : i ≠ w 3)
    (ψ : QState N) (hz : ∀ x : Bits N, x i = true → ψ x = 0) :
    ∀ x : Bits N, x i = true → runLayered (fairSelectorCirc w hw) ψ x = 0 := by
  have hh := apply1_zero_other hMat (w 0) i hi0 ψ hz
  have hrun : runLayered (fairSelectorCirc w hw) ψ =
      runLayered (selectorCirc w hw) (apply1 hMat (w 0) ψ) := by
    simp [fairSelectorCirc, runLayered, List.foldl_append, runLayer, Instr.apply]
  intro x hx
  rw [hrun, selectorCirc_action]
  apply hh
  simpa [Function.update_of_ne hi3] using hx

theorem hadamard_zero_event_weight {N : Nat} (i : Fin N) (ψ : QState N)
    (hs : ∀ x : Bits N, x i = true → ψ x = 0) (a : Bits N → Bool)
    (ha : ∀ x, a (flipBit i x) = a x) :
    (∑ x : Bits N, if a x then ‖apply1 hMat i ψ x‖ ^ 2 else 0) =
      ∑ x : Bits N, if a x then ‖ψ x‖ ^ 2 else 0 := by
  simp_rw [hadamard_zero_weight i ψ hs]
  have h := fair_event_weight i (fun x => ‖ψ x‖ ^ 2)
    (fun x hx => by rw [hs x hx]; simp) a a ha
  simp only [ite_self] at h
  linarith only [h]

theorem fairSelectorCirc_other_weight {N : Nat} (w : Fin 4 → Fin N)
    (hw : Function.Injective w) (i : Fin N) (hi0 : i ≠ w 0) (hi3 : i ≠ w 3)
    (ψ : QState N) (hs : ∀ x : Bits N, x (w 0) = true → ψ x = 0) :
    (∑ x : Bits N, if x i then ‖runLayered (fairSelectorCirc w hw) ψ x‖ ^ 2 else 0) =
      ∑ x : Bits N, if x i then ‖ψ x‖ ^ 2 else 0 := by
  have hrun : runLayered (fairSelectorCirc w hw) ψ =
      runLayered (selectorCirc w hw) (apply1 hMat (w 0) ψ) := by
    simp [fairSelectorCirc, runLayered, List.foldl_append, runLayer, Instr.apply]
  rw [hrun, selectorCirc_event_weight]
  simp only [selectorMap, Function.update_of_ne hi3]
  apply hadamard_zero_event_weight _ _ hs
  intro x
  simp [flipBit, Function.update_of_ne hi0]

end ShiQMACenteringCircuit


/-! ## AMPUNI-coin-step -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace ShiQMACenteringCircuit
open ShiShallow

/-- Applying X is a basis permutation. -/
theorem x_action {N : Nat} (i : Fin N) (ψ : QState N) :
    apply1 xMat i ψ = fun x => ψ (flipBit i x) := by
  funext x
  cases hx : x i <;> simp [apply1, xMat, Fintype.sum_bool, flipBit, hx]

theorem x_event_weight {N : Nat} (i : Fin N) (ψ : QState N) (a : Bits N → Bool) :
    (∑ x : Bits N, if a x then ‖apply1 xMat i ψ x‖ ^ 2 else 0) =
      ∑ x : Bits N, if a (flipBit i x) then ‖ψ x‖ ^ 2 else 0 := by
  let e : Bits N ≃ Bits N := {
    toFun := flipBit i
    invFun := flipBit i
    left_inv := flipBit_involutive i
    right_inv := flipBit_involutive i }
  have he := e.sum_comp (fun x : Bits N => if a x then ‖apply1 xMat i ψ x‖ ^ 2 else 0)
  rw [← he]
  apply Finset.sum_congr rfl
  intro x _
  rw [x_action]
  change (if a (flipBit i x) then ‖ψ (flipBit i (flipBit i x))‖ ^ 2 else 0) = _
  rw [flipBit_involutive]

theorem x_other_weight {N : Nat} (i j : Fin N) (hji : j ≠ i) (ψ : QState N) :
    (∑ x : Bits N, if x j then ‖apply1 xMat i ψ x‖ ^ 2 else 0) =
      ∑ x : Bits N, if x j then ‖ψ x‖ ^ 2 else 0 := by
  rw [x_event_weight]
  simp [flipBit, Function.update_of_ne hji]

theorem x_target_weight_of_zero {N : Nat} (i : Fin N) (ψ : QState N)
    (hz : ∀ x : Bits N, x i = true → ψ x = 0) :
    (∑ x : Bits N, if x i then ‖apply1 xMat i ψ x‖ ^ 2 else 0) =
      ∑ x : Bits N, ‖ψ x‖ ^ 2 := by
  rw [x_event_weight]
  apply Finset.sum_congr rfl
  intro x _
  cases hx : x i <;> simp [flipBit, hx, hz x]

theorem x_total_weight {N : Nat} (i : Fin N) (ψ : QState N) :
    (∑ x : Bits N, ‖apply1 xMat i ψ x‖ ^ 2) = ∑ x : Bits N, ‖ψ x‖ ^ 2 := by
  have h := x_event_weight i ψ (fun _ => true)
  simpa using h

private theorem x_zero_other {N : Nat} (i j : Fin N) (hji : j ≠ i) (ψ : QState N)
    (hz : ∀ x : Bits N, x j = true → ψ x = 0) :
    ∀ x : Bits N, x j = true → apply1 xMat i ψ x = 0 := by
  intro x hx
  rw [x_action]
  apply hz
  simpa [flipBit, Function.update_of_ne hji] using hx

/-- One binary fractional digit: prepare the constant digit, then average it
with the previous coin output using a fresh Hadamard selector. -/
def coinStep {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w) (b : Bool) : Layered N :=
  (if b then [[Instr.x (w 2)]] else []) ++ fairSelectorCirc w hw

theorem coinStep_accept_weight {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w)
    (b : Bool) (ψ : QState N)
    (hs : ∀ x : Bits N, x (w 0) = true → ψ x = 0)
    (hc : ∀ x : Bits N, x (w 2) = true → ψ x = 0)
    (ho : ∀ x : Bits N, x (w 3) = true → ψ x = 0) :
    (∑ x : Bits N, if x (w 3) then ‖runLayered (coinStep w hw b) ψ x‖ ^ 2 else 0) =
      ((∑ x : Bits N, if x (w 1) then ‖ψ x‖ ^ 2 else 0) +
        (if b then ∑ x : Bits N, ‖ψ x‖ ^ 2 else 0)) / 2 := by
  cases b
  · have h := fairSelectorCirc_accept_weight w hw ψ hs ho
    have hcoin : (∑ x : Bits N, if x (w 2) then ‖ψ x‖ ^ 2 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      cases hx : x (w 2) <;> simp [hc x, hx]
    simpa [coinStep, hcoin] using h
  · have h02 : w 0 ≠ w 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (hw h)
    have h12 : w 1 ≠ w 2 := fun h => (by decide : (1 : Fin 4) ≠ 2) (hw h)
    have h32 : w 3 ≠ w 2 := fun h => (by decide : (3 : Fin 4) ≠ 2) (hw h)
    have h := fairSelectorCirc_accept_weight w hw (apply1 xMat (w 2) ψ)
      (x_zero_other _ _ h02 ψ hs) (x_zero_other _ _ h32 ψ ho)
    rw [x_other_weight _ _ h12, x_target_weight_of_zero _ _ hc] at h
    simpa [coinStep, runLayered, List.foldl_append, runLayer, Instr.apply] using h

theorem coinStep_total_weight {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w)
    (b : Bool) (ψ : QState N)
    (hs : ∀ x : Bits N, x (w 0) = true → ψ x = 0) :
    (∑ x : Bits N, ‖runLayered (coinStep w hw b) ψ x‖ ^ 2) =
      ∑ x : Bits N, ‖ψ x‖ ^ 2 := by
  cases b
  · simpa [coinStep] using fairSelectorCirc_total_weight w hw ψ hs
  · have h02 : w 0 ≠ w 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (hw h)
    have h := fairSelectorCirc_total_weight w hw (apply1 xMat (w 2) ψ)
      (x_zero_other _ _ h02 ψ hs)
    rw [x_total_weight] at h
    simpa [coinStep, runLayered, List.foldl_append, runLayer, Instr.apply] using h

theorem coinStep_depth_le {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w) (b : Bool) :
    depth (coinStep w hw b) ≤ 77 := by
  have h : (fairSelectorCirc w hw).length = 76 := fairSelectorCirc_depth w hw
  cases b <;> simp [coinStep, depth, h]

theorem coinStep_wellFormed {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w) (b : Bool) :
    ∀ l ∈ coinStep w hw b, LayerOk l := by
  intro l hl
  rcases List.mem_append.mp hl with h | h
  · cases b <;> simp_all [LayerOk]
  · exact fairSelectorCirc_wellFormed w hw l h

theorem coinStep_zero_other {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w)
    (b : Bool) (i : Fin N) (hi0 : i ≠ w 0) (hi2 : i ≠ w 2) (hi3 : i ≠ w 3)
    (ψ : QState N) (hz : ∀ x : Bits N, x i = true → ψ x = 0) :
    ∀ x : Bits N, x i = true → runLayered (coinStep w hw b) ψ x = 0 := by
  cases b
  · simpa [coinStep] using fairSelectorCirc_zero_other w hw i hi0 hi3 ψ hz
  · have hx := x_zero_other (w 2) i hi2 ψ hz
    have h := fairSelectorCirc_zero_other w hw i hi0 hi3 (apply1 xMat (w 2) ψ) hx
    simpa [coinStep, runLayered, List.foldl_append, runLayer, Instr.apply] using h

theorem coinStep_other_weight {N : Nat} (w : Fin 4 → Fin N) (hw : Function.Injective w)
    (b : Bool) (i : Fin N) (hi0 : i ≠ w 0) (hi2 : i ≠ w 2) (hi3 : i ≠ w 3)
    (ψ : QState N) (hs : ∀ x : Bits N, x (w 0) = true → ψ x = 0) :
    (∑ x : Bits N, if x i then ‖runLayered (coinStep w hw b) ψ x‖ ^ 2 else 0) =
      ∑ x : Bits N, if x i then ‖ψ x‖ ^ 2 else 0 := by
  cases b
  · simpa [coinStep] using fairSelectorCirc_other_weight w hw i hi0 hi3 ψ hs
  · have h02 : w 0 ≠ w 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (hw h)
    have h := fairSelectorCirc_other_weight w hw i hi0 hi3 (apply1 xMat (w 2) ψ)
      (x_zero_other _ _ h02 ψ hs)
    rw [x_other_weight _ _ hi2] at h
    simpa [coinStep, runLayered, List.foldl_append, runLayer, Instr.apply] using h

end ShiQMACenteringCircuit


/-! ## AMPUNI-dyadic-coin-circuit -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace ShiQMACenteringCircuit
open ShiShallow ShiQMACenteredGap

/-- Three fresh wires per fractional digit; the previous result is reused as a control. -/
def coinWires {N : Nat} (base k : Nat) (h : base + 3 * (k + 1) < N) : Fin 4 → Fin N :=
  ![⟨base + 3 * k + 1, by omega⟩, ⟨base + 3 * k, by omega⟩,
    ⟨base + 3 * k + 2, by omega⟩, ⟨base + 3 * k + 3, by omega⟩]

theorem coinWires_injective {N : Nat} (base k : Nat) (h : base + 3 * (k + 1) < N) :
    Function.Injective (coinWires base k h) := by
  intro i j he
  have hv := congrArg Fin.val he
  fin_cases i <;> fin_cases j <;> simp [coinWires] at hv ⊢ <;> omega

/-- Explicit dyadic coin circuit on a contiguous clean register. The gates are
synthesized recursively from the supplied fractional bits; no real number is inspected. -/
def coinCircuit {N : Nat} (base : Nat) :
    (bs : List Bool) → base + 3 * bs.length < N → Layered N
  | [], _ => []
  | b :: bs, h =>
    coinCircuit base bs (by simp only [List.length_cons] at h; omega) ++
      coinStep (coinWires base bs.length (by simpa only [List.length_cons] using h))
        (coinWires_injective base bs.length (by simpa only [List.length_cons] using h)) b

private theorem coin_run_append {N : Nat} (a b : Layered N) (ψ : QState N) :
    runLayered (a ++ b) ψ = runLayered b (runLayered a ψ) := by
  simp [runLayered, List.foldl_append]

/-- Wires above the coin's used register keep any initial zero-support property. -/
theorem coinCircuit_zero_above {N : Nat} (base : Nat) (bs : List Bool)
    (h : base + 3 * bs.length < N) (ψ : QState N) (i : Fin N)
    (hi : base + 3 * bs.length < i.val)
    (hz : ∀ x : Bits N, x i = true → ψ x = 0) :
    ∀ x : Bits N, x i = true → runLayered (coinCircuit base bs h) ψ x = 0 := by
  induction bs with
  | nil => simpa [coinCircuit, runLayered] using hz
  | cons b bs ih =>
    have ht : base + 3 * bs.length < N := by simp only [List.length_cons] at h; omega
    have hi' : base + 3 * bs.length < i.val := by simp only [List.length_cons] at hi; omega
    have hp := ih ht hi'
    rw [coinCircuit, coin_run_append]
    apply coinStep_zero_other
    · intro he
      have hv := congrArg Fin.val he
      simp [coinWires] at hv
      simp only [List.length_cons] at hi
      omega
    · intro he
      have hv := congrArg Fin.val he
      simp [coinWires] at hv
      simp only [List.length_cons] at hi
      omega
    · intro he
      have hv := congrArg Fin.val he
      simp [coinWires] at hv
      simp only [List.length_cons] at hi
      omega
    · exact hp

private theorem dyadicValue_cons (b : Bool) (bs : List Bool) :
    dyadicValue (b :: bs) = (dyadicValue bs + if b then 1 else 0) / 2 := by
  cases b <;> simp [dyadicValue, binaryNumerator, pow_succ] <;> field_simp <;> ring

/-- Exact coin semantics and mass preservation on any state whose coin register
starts at zero. An arbitrary environment outside that register is permitted. -/
theorem coinCircuit_spec {N : Nat} (base : Nat) (bs : List Bool)
    (h : base + 3 * bs.length < N) (ψ : QState N)
    (hz : ∀ i : Fin N, base ≤ i.val → i.val ≤ base + 3 * bs.length →
      ∀ x : Bits N, x i = true → ψ x = 0) :
    (∑ x : Bits N, ‖runLayered (coinCircuit base bs h) ψ x‖ ^ 2) =
      (∑ x : Bits N, ‖ψ x‖ ^ 2) ∧
    (∑ x : Bits N, if x ⟨base + 3 * bs.length, h⟩ then
      ‖runLayered (coinCircuit base bs h) ψ x‖ ^ 2 else 0) =
      dyadicValue bs * (∑ x : Bits N, ‖ψ x‖ ^ 2) := by
  induction bs with
  | nil =>
    constructor
    · rfl
    · simp only [coinCircuit, runLayered, List.foldl_nil, dyadicValue,
        binaryNumerator, List.length_nil, Nat.cast_zero, zero_div, zero_mul]
      apply Finset.sum_eq_zero
      intro x _
      have hz0 := hz (⟨base, h⟩ : Fin N) (by simp) (by simp)
      cases hx : x ⟨base, h⟩ <;> simp [hx, hz0 x]
  | cons b bs ih =>
    have ht : base + 3 * bs.length < N := by simp only [List.length_cons] at h; omega
    have hw : base + 3 * (bs.length + 1) < N := h
    let w := coinWires base bs.length hw
    let χ := runLayered (coinCircuit base bs ht) ψ
    have hprev := ih ht (fun i hl hu => hz i hl (by simp only [List.length_cons]; omega))
    have hfresh (i : Fin N) (hl : base + 3 * bs.length < i.val)
        (hu : i.val ≤ base + 3 * (bs.length + 1)) :
        ∀ x : Bits N, x i = true → χ x = 0 :=
      coinCircuit_zero_above base bs ht ψ i hl
        (hz i (by omega) hu)
    have hs : ∀ x : Bits N, x (w 0) = true → χ x = 0 :=
      hfresh (w 0) (by dsimp [w, coinWires]; omega) (by dsimp [w, coinWires]; omega)
    have hc : ∀ x : Bits N, x (w 2) = true → χ x = 0 :=
      hfresh (w 2) (by dsimp [w, coinWires]; omega) (by dsimp [w, coinWires]; omega)
    have ho : ∀ x : Bits N, x (w 3) = true → χ x = 0 :=
      hfresh (w 3) (by dsimp [w, coinWires]; omega) (by dsimp [w, coinWires]; omega)
    have hr : runLayered (coinCircuit base (b :: bs) h) ψ =
        runLayered (coinStep w (coinWires_injective base bs.length hw) b) χ := by
      rw [coinCircuit, coin_run_append]
    have hm : (∑ x : Bits N, ‖χ x‖ ^ 2) = ∑ x : Bits N, ‖ψ x‖ ^ 2 := hprev.1
    have hp : (∑ x : Bits N, if x (w 1) then ‖χ x‖ ^ 2 else 0) =
        dyadicValue bs * (∑ x : Bits N, ‖ψ x‖ ^ 2) := hprev.2
    constructor
    · rw [hr, coinStep_total_weight w _ b χ hs, hm]
    · have hout : (⟨base + 3 * (b :: bs).length, h⟩ : Fin N) = w 3 := by
        apply Fin.ext
        simp [w, coinWires] <;> omega
      rw [hr, hout, coinStep_accept_weight w _ b χ hs hc ho, hm, hp, dyadicValue_cons]
      cases b <;> simp <;> ring

theorem coinCircuit_depth_le {N : Nat} (base : Nat) (bs : List Bool)
    (h : base + 3 * bs.length < N) : depth (coinCircuit base bs h) ≤ 77 * bs.length := by
  induction bs with
  | nil => simp [coinCircuit, depth]
  | cons b bs ih =>
    have ht : base + 3 * bs.length < N := by simp only [List.length_cons] at h; omega
    have htail := ih ht
    have hs := coinStep_depth_le (coinWires base bs.length h)
      (coinWires_injective base bs.length h) b
    simp only [coinCircuit, depth, List.length_append, List.length_cons] at *
    omega

theorem coinCircuit_wellFormed {N : Nat} (base : Nat) (bs : List Bool)
    (h : base + 3 * bs.length < N) : ∀ l ∈ coinCircuit base bs h, LayerOk l := by
  induction bs with
  | nil => simp [coinCircuit]
  | cons b bs ih =>
    intro l hl
    rcases List.mem_append.mp hl with htail | hstep
    · exact ih (by simp only [List.length_cons] at h; omega) l htail
    · exact coinStep_wellFormed _ _ _ l hstep

/-- Coin preparation preserves every output probability in the earlier register. -/
theorem coinCircuit_other_weight {N : Nat} (base : Nat) (bs : List Bool)
    (h : base + 3 * bs.length < N) (ψ : QState N)
    (hz : ∀ j : Fin N, base ≤ j.val → j.val ≤ base + 3 * bs.length →
      ∀ x : Bits N, x j = true → ψ x = 0)
    (i : Fin N) (hi : i.val < base) :
    (∑ x : Bits N, if x i then ‖runLayered (coinCircuit base bs h) ψ x‖ ^ 2 else 0) =
      ∑ x : Bits N, if x i then ‖ψ x‖ ^ 2 else 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have ht : base + 3 * bs.length < N := by simp only [List.length_cons] at h; omega
    have hw : base + 3 * (bs.length + 1) < N := h
    let w := coinWires base bs.length hw
    let χ := runLayered (coinCircuit base bs ht) ψ
    have hs : ∀ x : Bits N, x (w 0) = true → χ x = 0 :=
      coinCircuit_zero_above base bs ht ψ (w 0) (by dsimp [w, coinWires]; omega)
        (hz (w 0) (by dsimp [w, coinWires]; omega)
          (by dsimp [w, coinWires]; omega))
    have hn (j : Fin 4) : i ≠ w j := by
      intro he
      have hv := congrArg Fin.val he
      fin_cases j <;> simp [w, coinWires] at hv <;> omega
    have hr : runLayered (coinCircuit base (b :: bs) h) ψ =
        runLayered (coinStep w (coinWires_injective base bs.length hw) b) χ := by
      rw [coinCircuit, coin_run_append]
    rw [hr, coinStep_other_weight w _ b i (hn 0) (hn 2) (hn 3) χ hs]
    exact ih ht (fun j hl hu => hz j hl (by simp only [List.length_cons]; omega))

end ShiQMACenteringCircuit



/-! ## A complete finite-register centering suffix -/
namespace ShiQMACenteringCircuit
open ShiShallow ShiQMACenteredGap ShiEmbed ShiSpread

/-- The final selector uses the original output, the prepared coin, and two fresh wires. -/
def centeringWires (m k : Nat) (out : Fin m) : Fin 4 → Fin (m + (3 * k + 3)) :=
  ![⟨m + 3 * k + 1, by omega⟩, Fin.castAdd (3 * k + 3) out,
    ⟨m + 3 * k, by omega⟩, ⟨m + 3 * k + 2, by omega⟩]

theorem centeringWires_injective (m k : Nat) (out : Fin m) :
    Function.Injective (centeringWires m k out) := by
  intro i j he
  have hv := congrArg Fin.val he
  have ho := out.isLt
  fin_cases i <;> fin_cases j <;> simp [centeringWires] at hv ⊢ <;> omega

def centeringSuffix (m : Nat) (out : Fin m) (bs : List Bool) : Layered (m + (3 * bs.length + 3)) :=
  coinCircuit m bs (by omega) ++
    fairSelectorCirc (centeringWires m bs.length out) (centeringWires_injective m bs.length out)

private theorem spread_zero_after {m r : Nat} (ψ : QState m) (i : Fin (m + r))
    (hi : m ≤ i.val) :
    ∀ x : Bits (m + r), x i = true → spread (Fin.castAdd r) ψ x = 0 := by
  intro x hx
  have hoff : OffImage (Fin.castAdd r) i := by
    intro j he
    have hv := congrArg Fin.val he
    have hj := j.isLt
    simp only [Fin.val_castAdd] at hv
    omega
  unfold spread
  split_ifs with h
  · have hz := h i hoff
    rw [hx] at hz
    contradiction
  · rfl

/-- Exact quantum centering on a larger register. The input on the original
register can be any state; only the newly added ancillas are initialized to zero. -/
theorem centeringSuffix_accept_weight (m : Nat) (out : Fin m) (bs : List Bool) (ψ : QState m) :
    let e := Fin.castAdd (3 * bs.length + 3) (n := m)
    let o : Fin (m + (3 * bs.length + 3)) := ⟨m + 3 * bs.length + 2, by omega⟩
    (∑ x : Bits (m + (3 * bs.length + 3)), if x o then
      ‖runLayered (centeringSuffix m out bs) (spread e ψ) x‖ ^ 2 else 0) =
      ((∑ x : Bits m, if x out then ‖ψ x‖ ^ 2 else 0) +
        dyadicValue bs * (∑ x : Bits m, ‖ψ x‖ ^ 2)) / 2 := by
  dsimp only
  let e : Fin m → Fin (m + (3 * bs.length + 3)) := Fin.castAdd (3 * bs.length + 3)
  let ρ := spread e ψ
  let χ := runLayered (coinCircuit m bs (by omega)) ρ
  let w := centeringWires m bs.length out
  have hz (i : Fin (m + (3 * bs.length + 3))) (hi : m ≤ i.val) :
      ∀ x, x i = true → ρ x = 0 := spread_zero_after ψ i hi
  have hcoin := coinCircuit_spec m bs (by omega) ρ (fun i hl _ => hz i hl)
  have hs : ∀ x, x (w 0) = true → χ x = 0 :=
    coinCircuit_zero_above m bs (by omega) ρ (w 0)
      (by dsimp [w, centeringWires]; omega) (hz (w 0) (by dsimp [w, centeringWires]; omega))
  have ho : ∀ x, x (w 3) = true → χ x = 0 :=
    coinCircuit_zero_above m bs (by omega) ρ (w 3)
      (by dsimp [w, centeringWires]; omega) (hz (w 3) (by dsimp [w, centeringWires]; omega))
  have hm : (∑ x, ‖ρ x‖ ^ 2) = ∑ x : Bits m, ‖ψ x‖ ^ 2 :=
    ShiQMACenteringReference.sumSpread e (Fin.castAdd_injective _ _) ψ
      (fun _ z => ‖z‖ ^ 2) (by intro z; simp)
  have hevent : (∑ x, if x (e out) then ‖ρ x‖ ^ 2 else 0) =
      ∑ x : Bits m, if x out then ‖ψ x‖ ^ 2 else 0 :=
    ShiQMACenteringReference.sumSpread e (Fin.castAdd_injective _ _) ψ
      (fun z a => if z out then ‖a‖ ^ 2 else 0) (by intro z; simp)
  have hsource := coinCircuit_other_weight m bs (by omega) ρ
    (fun i hl _ => hz i hl) (e out) out.isLt
  have hprev : (∑ x, if x (w 1) then ‖χ x‖ ^ 2 else 0) =
      ∑ x : Bits m, if x out then ‖ψ x‖ ^ 2 else 0 := hsource.trans hevent
  have hc : (∑ x, if x (w 2) then ‖χ x‖ ^ 2 else 0) =
      dyadicValue bs * (∑ x : Bits m, ‖ψ x‖ ^ 2) := by
    exact hcoin.2.trans (congrArg (fun t : ℝ => dyadicValue bs * t) hm)
  have hr : runLayered (centeringSuffix m out bs) (spread e ψ) =
      runLayered (fairSelectorCirc w (centeringWires_injective m bs.length out)) χ := by
    rw [centeringSuffix, selector_run_append]
  change (∑ x, if x (w 3) then ‖runLayered (centeringSuffix m out bs) (spread e ψ) x‖ ^ 2 else 0) = _
  rw [hr, fairSelectorCirc_accept_weight w _ χ hs ho, hprev, hc]

/-- The complete finite circuit: run the original circuit, prepare the coin,
and select the final output. Original wire indices remain unchanged. -/
def centeredCircuit {m : Nat} (c : Layered m) (out : Fin m) (bs : List Bool) :
    Layered (m + (3 * bs.length + 3)) :=
  embedCirc (Fin.castAdd (3 * bs.length + 3)) (Fin.castAdd_injective _ _) c ++
    centeringSuffix m out bs

theorem centeredCircuit_accept_weight {m : Nat} (c : Layered m) (out : Fin m)
    (bs : List Bool) (ψ : QState m) :
    let e := Fin.castAdd (3 * bs.length + 3) (n := m)
    let o : Fin (m + (3 * bs.length + 3)) := ⟨m + 3 * bs.length + 2, by omega⟩
    (∑ x : Bits (m + (3 * bs.length + 3)), if x o then
      ‖runLayered (centeredCircuit c out bs) (spread e ψ) x‖ ^ 2 else 0) =
      ((∑ x : Bits m, if x out then ‖runLayered c ψ x‖ ^ 2 else 0) +
        dyadicValue bs * (∑ x : Bits m, ‖runLayered c ψ x‖ ^ 2)) / 2 := by
  dsimp only
  rw [centeredCircuit, selector_run_append,
    ShiQMACenteringReference.embedSpread]
  exact centeringSuffix_accept_weight m out bs (runLayered c ψ)

theorem centeringSuffix_depth_le (m : Nat) (out : Fin m) (bs : List Bool) :
    depth (centeringSuffix m out bs) ≤ 77 * bs.length + 76 := by
  have hc := coinCircuit_depth_le (N := m + (3 * bs.length + 3)) m bs (by omega)
  have hs := fairSelectorCirc_depth (centeringWires m bs.length out)
    (centeringWires_injective m bs.length out)
  simp only [centeringSuffix, depth, List.length_append] at *
  omega

theorem centeringSuffix_wellFormed (m : Nat) (out : Fin m) (bs : List Bool) :
    ∀ l ∈ centeringSuffix m out bs, LayerOk l := by
  intro l hl
  rcases List.mem_append.mp hl with h | h
  · exact coinCircuit_wellFormed m bs (by omega) l h
  · exact fairSelectorCirc_wellFormed _ _ l h

end ShiQMACenteringCircuit


namespace ShiQMACenteringCircuit
open ShiShallow ShiQMACenteredGap ShiSpread

/-- On normalized inputs, the concrete suffix realizes the exact affine map
used by the numerical general-gap proof. -/
theorem centeringSuffix_normalized (m : Nat) (out : Fin m) (bs : List Bool) (ψ : QState m)
    (hψ : (∑ x : Bits m, ‖ψ x‖ ^ 2) = 1) :
    let e := Fin.castAdd (3 * bs.length + 3) (n := m)
    let o : Fin (m + (3 * bs.length + 3)) := ⟨m + 3 * bs.length + 2, by omega⟩
    (∑ x : Bits (m + (3 * bs.length + 3)), if x o then
      ‖runLayered (centeringSuffix m out bs) (spread e ψ) x‖ ^ 2 else 0) =
      centeredAcceptance (dyadicValue bs) (∑ x : Bits m, if x out then ‖ψ x‖ ^ 2 else 0) := by
  simpa only [centeredAcceptance, hψ, mul_one] using centeringSuffix_accept_weight m out bs ψ

end ShiQMACenteringCircuit

#print axioms ShiQMACenteringCircuit.centeringSuffix_normalized
