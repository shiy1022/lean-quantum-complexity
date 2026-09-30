import «AMPUNI-constructive-integrated-machine»
import «AMPUNI-repeat-concrete-controller»
import «AMPUNI-state-frame»
import «AMPUNI-state-reindex»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
noncomputable section
namespace ShiTMConstructiveConcrete

private def sourceStateEquiv {W : Type} :
    ((Option Bool × W) × Bool) ≃
      (Option Bool × (Bool × W)) where
  toFun x := (x.1.1, (x.2, x.1.2))
  invFun x := ((x.1, x.2.2), x.2.1)
  left_inv := by
    intro x
    rcases x with ⟨⟨v, w⟩, b⟩
    rfl
  right_inv := by
    intro x
    rcases x with ⟨v, b, w⟩
    rfl

/-- Carry the loader's parity bit through each source-machine step. -/
def liftedSource {K L W : Type} [DecidableEq K]
    {G : K → Type}
    (M : L → Stmt G L (Option Bool × W)) :
    L → Stmt G L (Option Bool × (Bool × W)) :=
  ShiTMStateReindex.machine sourceStateEquiv
    (ShiTMStateFrame.machine (W := Bool) M)

def liftedCfg {K L W : Type} {G : K → Type}
    (b : Bool) (c : Cfg G L (Option Bool × W)) :
    Cfg G L (Option Bool × (Bool × W)) :=
  ShiTMStateReindex.cfg sourceStateEquiv
    (ShiTMStateFrame.cfg b c)

/-- Source-machine runs preserve the parity bit used by the constructive
counter loader. This permits the existing one-round source proof to be
reused at either parity when building the repeated-run theorem. -/
theorem liftedSource_run_iter {K L W : Type} [DecidableEq K]
    {G : K → Type}
    (M : L → Stmt G L (Option Bool × W))
    (b : Bool) (t : Nat)
    (c : Option (Cfg G L (Option Bool × W))) :
    (ShiTMSubroutine.run (liftedSource M))^[t]
      (c.map (liftedCfg b)) =
    ((ShiTMSubroutine.run M)^[t] c).map (liftedCfg b) := by
  have hm (c' : Option (Cfg G L (Option Bool × W))) :
      c'.map (liftedCfg b) =
      (c'.map (ShiTMStateFrame.cfg b)).map
        (ShiTMStateReindex.cfg sourceStateEquiv) := by
    cases c' <;> rfl
  rw [hm c, hm ((ShiTMSubroutine.run M)^[t] c)]
  change (ShiTMSubroutine.run
      (ShiTMStateReindex.machine sourceStateEquiv
        (ShiTMStateFrame.machine M)))^[t]
      ((c.map (ShiTMStateFrame.cfg b)).map
        (ShiTMStateReindex.cfg sourceStateEquiv)) = _
  rw [ShiTMStateReindex.run_iter_frame,
    ShiTMStateFrame.run_iter_frame]

abbrev source (k : Nat) := ShiTMRepeatConcrete.source k

/-- A single finite TM2 containing startup, counter construction, and all
amplification rounds. Its full valid-input runtime theorem is established
separately from this finite-program packaging. -/
def finiteMachine (k : Nat) (p : Polynomial ℕ) :
    Turing.FinTM2 := by
  letI : DecidableEq (source k).K := (source k).kDecidableEq
  letI : DecidableEq (source k).Λ := Classical.decEq _
  letI : Fintype (source k).K := (source k).kFin
  letI : Fintype (source k).Λ := (source k).ΛFin
  letI : Fintype ShiTMNormalizedEntry.booleanMachine.σ :=
    ShiTMNormalizedEntry.booleanMachine.σFin
  exact {
    K := (source k).K ⊕ ShiTMRepeatController.Aux
    kDecidableEq := inferInstance
    kFin := inferInstance
    k₀ := .inl (source k).k₀
    k₁ := .inl (source k).k₁
    Γ := ShiTMRepeatController.Gam (source k).Γ
    Λ := ShiTMConstructiveIntegrated.Label (source k).Λ
    main := ShiTMConstructiveIntegrated.scan
    ΛFin := inferInstance
    σ := Option Bool ×
      (Bool × (ShiTMNormalizedEntry.booleanMachine.σ × Bool))
    initialState :=
      (none, (true,
        (ShiTMNormalizedEntry.booleanMachine.initialState, false)))
    σFin := inferInstance
    Γk₀Fin := (source k).Γk₀Fin
    m := ShiTMConstructiveIntegrated.machine p
      (liftedSource (source k).m)
      (source k).main (ShiTMRepeatConcrete.terminal k)
      (source k).k₀ (source k).k₁ id id id
  }

end ShiTMConstructiveConcrete
