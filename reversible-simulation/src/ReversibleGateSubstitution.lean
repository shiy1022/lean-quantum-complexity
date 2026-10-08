import ReversibleExactToffoli
import ReversibleCore

set_option autoImplicit false
namespace ShiReversibleGateBridge

theorem apply1_x_exact {N : Nat} (t : Fin N) (ψ : ShiShallow.QState N) :
    ShiShallow.apply1 ShiShallow.xMat t ψ = fun x => ψ (Function.update x t (!x t)) := by
  funext x
  simp only [ShiShallow.apply1, Fintype.sum_bool]
  cases hx : x t <;> simp [ShiShallow.xMat, Matrix.of_apply, hx]

/-- Each Boolean gate is replaced by concrete singleton quantum layers. -/
noncomputable def gateCircuit {N : Nat} : ShiReversible.Gate N → ShiShallow.Layered N
  | .x t => [[.x t]]
  | .cx a t hat => [[.cnot a t hat]]
  | .ccx a b t hat hbt =>
      if hab : a = b then [[.cnot a t hat]] else toffoliCircuit a b t hab hat hbt

theorem gateCircuit_correct {N : Nat} (g : ShiReversible.Gate N) (ψ : ShiShallow.QState N) :
    ShiShallow.runLayered (gateCircuit g) ψ = fun x => ψ (g.eval x) := by
  cases g with
  | x t => exact apply1_x_exact t ψ
  | cx a t hat => rfl
  | ccx a b t hat hbt =>
    by_cases hab : a = b
    · subst b
      simp only [gateCircuit, dif_pos rfl]
      funext x
      simp [ShiShallow.runLayered, ShiShallow.runLayer, ShiShallow.Instr.apply,
        ShiShallow.cnotState, ShiReversible.Gate.eval]
    · simpa only [gateCircuit, dif_neg hab, ShiReversible.Gate.eval] using
        toffoliCircuit_correct a b t hab hat hbt ψ

theorem gateCircuit_layerOk {N : Nat} (g : ShiReversible.Gate N) :
    ∀ l ∈ gateCircuit g, ShiShallow.LayerOk l := by
  cases g with
  | x t => simp [gateCircuit, ShiShallow.LayerOk]
  | cx a t hat => simp [gateCircuit, ShiShallow.LayerOk]
  | ccx a b t hat hbt =>
    by_cases hab : a = b
    · simp [gateCircuit, hab, ShiShallow.LayerOk]
    · simpa only [gateCircuit, dif_neg hab] using toffoliCircuit_layerOk a b t hab hat hbt

theorem gateCircuit_depth {N : Nat} (g : ShiReversible.Gate N) :
    ShiShallow.depth (gateCircuit g) ≤ 37 := by
  cases g with
  | x t => simp [gateCircuit, ShiShallow.depth]
  | cx a t hat => simp [gateCircuit, ShiShallow.depth]
  | ccx a b t hat hbt =>
    by_cases hab : a = b
    · simp [gateCircuit, hab, ShiShallow.depth]
    · rw [gateCircuit, dif_neg hab, toffoliCircuit_depth]

noncomputable def substitute {N : Nat} (gs : List (ShiReversible.Gate N)) : ShiShallow.Layered N :=
  gs.flatMap gateCircuit

theorem runLayered_append {N : Nat} (c d : ShiShallow.Layered N) (ψ : ShiShallow.QState N) :
    ShiShallow.runLayered (c ++ d) ψ = ShiShallow.runLayered d (ShiShallow.runLayered c ψ) := by
  simp [ShiShallow.runLayered, List.foldl_append]

/-- The gate-set replacement has exact pullback action on arbitrary quantum states. -/
theorem substitute_correct {N : Nat} (gs : List (ShiReversible.Gate N)) (ψ : ShiShallow.QState N) :
    ShiShallow.runLayered (substitute gs) ψ = fun x => ψ (ShiReversible.run gs.reverse x) := by
  induction gs generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    simp only [substitute, List.flatMap_cons, runLayered_append, gateCircuit_correct]
    rw [← substitute, ih]
    funext x
    rw [List.reverse_cons, ShiReversible.run_append]
    rfl

theorem substitute_layerOk {N : Nat} (gs : List (ShiReversible.Gate N)) :
    ∀ l ∈ substitute gs, ShiShallow.LayerOk l := by
  intro l hl
  obtain ⟨g, _, hl⟩ := List.mem_flatMap.mp hl
  exact gateCircuit_layerOk g l hl

theorem substitute_depth {N : Nat} (gs : List (ShiReversible.Gate N)) :
    ShiShallow.depth (substitute gs) ≤ 37 * gs.length := by
  induction gs with
  | nil => simp [substitute, ShiShallow.depth]
  | cons g gs ih =>
    have hg := gateCircuit_depth g
    simp only [substitute, List.flatMap_cons, ShiShallow.depth, List.length_append,
      List.length_cons, Nat.mul_succ] at *
    omega

theorem gateCircuit_singleton {N : Nat} (g : ShiReversible.Gate N) :
    ∀ l ∈ gateCircuit g, l.length = 1 := by
  cases g with
  | x t => simp [gateCircuit]
  | cx a t hat => simp [gateCircuit]
  | ccx a b t hat hbt =>
    by_cases hab : a = b
    · simp [gateCircuit, hab]
    · intro l hl
      simp only [gateCircuit, dif_neg hab, toffoliCircuit] at hl
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hl
      rfl

theorem singletonLayers_gateCount {α : Type} (c : List (List α))
    (h : ∀ l ∈ c, l.length = 1) : c.flatten.length = c.length := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    have hl := h l (by simp)
    have hc := ih (fun k hk => h k (by simp [hk]))
    simp [hl, hc, Nat.add_comm]

/-- Size counts all emitted elementary quantum gates, not merely the layers. -/
theorem substitute_gateCount {N : Nat} (gs : List (ShiReversible.Gate N)) :
    (substitute gs).flatten.length = ShiShallow.depth (substitute gs) := by
  apply singletonLayers_gateCount
  intro l hl
  obtain ⟨g, _, hl⟩ := List.mem_flatMap.mp hl
  exact gateCircuit_singleton g l hl

end ShiReversibleGateBridge
