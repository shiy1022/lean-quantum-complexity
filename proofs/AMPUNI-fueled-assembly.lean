import «AMPUNI-fuel-transfer-run»
import «AMPUNI-right-frame»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMFueledAssembly
variable {K B V : Type} [DecidableEq K] {G : K → Type}
abbrev Label := ShiTMFuel.Label ⊕ (ShiTMFuelTransfer.Label ⊕ B)
abbrev Gam := ShiTMFuelFrame.Gam (G := G)
abbrev State := Option Bool × V
abbrev fuelLabel (l : ShiTMFuel.Label) : Label (B := B) := .inl l
abbrev transferLabel (l : ShiTMFuelTransfer.Label) : Label (B := B) := .inr (.inl l)
abbrev bodyLabel (l : B) : Label (B := B) := .inr (.inr l)

variable (input fuel : K) (putInput : Bool → G input) (putFuel : Bool → G fuel)
    (k : Nat) (M : B → Stmt G B V) (entry : B)

def machine : Label (B := B) → Stmt (Gam (G := G)) (Label (B := B)) (State (V := V))
  | .inl .done => .goto (fun _ => transferLabel .reverseInput)
  | .inl l => ShiTMSubroutine.stmt fuelLabel (ShiTMFuelFrame.machine k l)
  | .inr (.inl .done) => .goto (fun _ => bodyLabel entry)
  | .inr (.inl l) => ShiTMSubroutine.stmt transferLabel
      (ShiTMFuelTransfer.machine input fuel putInput putFuel l)
  | .inr (.inr l) => ShiTMSubroutine.stmt bodyLabel (ShiTMRightFrame.machine M l)

abbrev run := ShiTMSubroutine.run (machine input fuel putInput putFuel k M entry)

def initial (v : V) (xs : List Bool) : Cfg (Gam (G := G)) (Label (B := B)) (State (V := V)) :=
  ShiTMSubroutine.cfg fuelLabel (ShiTMFuelFrame.cfg v (fun _ => []) .init xs [] [] [])

def prefixCost (xs : List Bool) : Nat :=
  (xs.length+2)*(2*xs.length+3)+1 + 1 + (2*xs.length+k*(xs.length+1)^2+3) + 1

theorem prefixCost_bound (xs : List Bool) : prefixCost k xs ≤ (k+12)*(xs.length+1)^2 := by
  have hf := ShiTMFuel.fuel_cost_bound xs
  have h : 2*xs.length+5 ≤ 5*(xs.length+1)^2 := by nlinarith
  dsimp [prefixCost]
  nlinarith

/-- Compose fuel generation, data transfer, and any subsequent source run.
Both handoffs are charged; the initializer's emptied frame is preserved. -/
theorem assemble (hne : fuel ≠ input) (v : V) (xs : List Bool)
    (steps : Nat) (d : Cfg G B V)
    (hr : (ShiTMSubroutine.run M)^[steps]
      (some ⟨some entry, v,
        ShiTMFuelTransfer.transferred input fuel putInput putFuel xs (k*(xs.length+1)^2)⟩) = some d) :
    (run input fuel putInput putFuel k M entry)^[prefixCost k xs+steps]
      (some (initial (B := B) (G := G) v xs)) =
      some (ShiTMSubroutine.cfg bodyLabel (ShiTMRightFrame.cfg (fun _ => []) none d)) := by
  let Big := machine input fuel putInput putFuel k M entry
  let budget := k*(xs.length+1)^2
  have hf := ShiTMFuelFrame.fuel_run k v (fun j : K => ([] : List (G j))) xs
  have h₀ := ShiTMSubroutine.run_to_terminal
    (ShiTMFuelFrame.machine (G := G) (W := V) k) Big fuelLabel .done rfl
    (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim)
    ((xs.length+2)*(2*xs.length+3)+1) _ _ rfl hf
  have he₀ : (ShiTMSubroutine.run Big)^[1]
      (some (ShiTMSubroutine.cfg fuelLabel
        (ShiTMFuelFrame.cfg v (fun j : K => ([] : List (G j))) .done xs [] [] (List.replicate budget true)))) =
      some ⟨some (transferLabel .reverseInput), (none,v),
        ShiTMStackFrame.extendStacks (ShiTMFuel.storeFn xs [] [] (List.replicate budget true))
          (fun _ => [])⟩ := rfl
  have ht := ShiTMFuelTransfer.transfer_run input fuel putInput putFuel hne v xs budget
  have h₁ := ShiTMSubroutine.run_to_terminal
    (ShiTMFuelTransfer.machine (W := V) input fuel putInput putFuel) Big transferLabel .done rfl
    (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim)
    (2*xs.length+budget+3) _ _ rfl ht
  have he₁ : (ShiTMSubroutine.run Big)^[1]
      (some (ShiTMSubroutine.cfg transferLabel
        ⟨some .done, (none,v), ShiTMStackFrame.extendStacks (fun _ => [])
          (ShiTMFuelTransfer.transferred input fuel putInput putFuel xs budget)⟩)) =
      some (ShiTMSubroutine.cfg bodyLabel (ShiTMRightFrame.cfg (fun _ => []) none
        ⟨some entry, v, ShiTMFuelTransfer.transferred input fuel putInput putFuel xs budget⟩)) := rfl
  have hb := ShiTMRightFrame.run_iter_frame M
    (fun j : ShiTMFuel.Stack => ([] : List (ShiTMFuel.Gam j))) (none : Option Bool) steps
    (some ⟨some entry, v, ShiTMFuelTransfer.transferred input fuel putInput putFuel xs budget⟩)
  rw [hr] at hb
  have h₂ := ShiTMSubroutine.run_iter_lift (ShiTMRightFrame.machine (E := ShiTMFuel.Gam)
      (W := Option Bool) M) Big bodyLabel (by intro l; rfl) steps
    ((some ⟨some entry, v, ShiTMFuelTransfer.transferred input fuel putInput putFuel xs budget⟩).map
      (ShiTMRightFrame.cfg (fun _ => []) none))
  rw [hb] at h₂
  exact ShiTMFuel.iterTwo (ShiTMSubroutine.run Big) _ _ _ _ _
    (ShiTMFuel.iterTwo (ShiTMSubroutine.run Big) _ _ _ _ _
      (ShiTMFuel.iterTwo (ShiTMSubroutine.run Big) _ _ _ _ _
        (ShiTMFuel.iterTwo (ShiTMSubroutine.run Big) _ _ _ _ _ h₀ he₀) h₁) he₁) h₂

end ShiTMFueledAssembly
