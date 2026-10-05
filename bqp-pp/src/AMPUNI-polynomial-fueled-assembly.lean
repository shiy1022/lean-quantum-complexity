import «AMPUNI-fuel-transfer-run»
import «AMPUNI-polynomial-fuel-frame»
import «AMPUNI-right-frame»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMPolynomialFueledAssembly
variable {K B V : Type} [DecidableEq K] {G : K → Type}
abbrev Label (d : Nat) := ShiTMPolynomialFuel.Label d ⊕ (ShiTMFuelTransfer.Label ⊕ B)
abbrev Gam := ShiTMFuelFrame.Gam (G := G)
abbrev State := Option Bool × V
abbrev fuelLabel {d : Nat} (l : ShiTMPolynomialFuel.Label d) : Label (B := B) d := .inl l
abbrev transferLabel {d : Nat} (l : ShiTMFuelTransfer.Label) : Label (B := B) d := .inr (.inl l)
abbrev bodyLabel {d : Nat} (l : B) : Label (B := B) d := .inr (.inr l)

variable (input fuel : K) (putInput : Bool → G input) (putFuel : Bool → G fuel)
    (d k : Nat) (M : B → Stmt G B V) (entry : B)

def machine : Label (B := B) d → Stmt (Gam (G := G)) (Label (B := B) d) (State (V := V))
  | .inl l => if l = ShiTMPolynomialFuel.done then
      .goto (fun _ => transferLabel .reverseInput)
    else ShiTMSubroutine.stmt fuelLabel (ShiTMPolynomialFuelFrame.machine d k l)
  | .inr (.inl .done) => .goto (fun _ => bodyLabel entry)
  | .inr (.inl l) => ShiTMSubroutine.stmt transferLabel
      (ShiTMFuelTransfer.machine input fuel putInput putFuel l)
  | .inr (.inr l) => ShiTMSubroutine.stmt bodyLabel (ShiTMRightFrame.machine M l)

abbrev run := ShiTMSubroutine.run (machine input fuel putInput putFuel d k M entry)

def initial {d : Nat} (v : V) (xs : List Bool) : Cfg (Gam (G := G)) (Label (B := B) d) (State (V := V)) :=
  ShiTMSubroutine.cfg fuelLabel (ShiTMPolynomialFuelFrame.cfg v (fun _ => []) ShiTMPolynomialFuel.init xs [] [] [])

def prefixCost (xs : List Bool) : Nat :=
  (1 + ShiTMPolynomialFuel.work d xs.length k) + 1 +
    (2*xs.length+k*(xs.length+1)^(d+1)+3) + 1

noncomputable def prefixPoly : Polynomial ℕ :=
  ShiTMPolynomialFuel.fuelTimePoly d k + Polynomial.C 2 * Polynomial.X +
    ShiTMPolynomialFuel.budgetPoly d k + Polynomial.C 5

theorem prefixPoly_eval (n : Nat) :
    (prefixPoly d k).eval n =
      (1 + ShiTMPolynomialFuel.work d n k) + 1 +
        (2*n+k*(n+1)^(d+1)+3) + 1 := by
  simp only [prefixPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X,
    ShiTMPolynomialFuel.fuelTimePoly_eval, ShiTMPolynomialFuel.budgetPoly_eval]
  omega

/-- Compose fuel generation, data transfer, and any subsequent source run.
Both handoffs are charged; the initializer's emptied frame is preserved. -/
theorem assemble (hne : fuel ≠ input) (v : V) (xs : List Bool)
    (steps : Nat) (target : Cfg G B V)
    (hr : (ShiTMSubroutine.run M)^[steps]
      (some ⟨some entry, v,
        ShiTMFuelTransfer.transferred input fuel putInput putFuel xs (k*(xs.length+1)^(d+1))⟩) = some target) :
    (run input fuel putInput putFuel d k M entry)^[prefixCost d k xs+steps]
      (some (initial (B := B) (G := G) v xs)) =
      some (ShiTMSubroutine.cfg bodyLabel (ShiTMRightFrame.cfg (fun _ => []) none target)) := by
  let Big := machine input fuel putInput putFuel d k M entry
  let budget := k*(xs.length+1)^(d+1)
  have hf := ShiTMPolynomialFuelFrame.fuel_run d k v (fun j : K => ([] : List (G j))) xs
  have h₀ := ShiTMSubroutine.run_to_terminal
    (ShiTMPolynomialFuelFrame.machine (G := G) (W := V) d k)
    Big fuelLabel ShiTMPolynomialFuel.done rfl
    (by intro l hl; simp only [Big, machine, fuelLabel, if_neg hl])
    (1 + ShiTMPolynomialFuel.work d xs.length k) _ _ rfl hf
  have he₀ : (ShiTMSubroutine.run Big)^[1]
      (some (ShiTMSubroutine.cfg fuelLabel
        (ShiTMPolynomialFuelFrame.cfg v (fun j : K => ([] : List (G j))) ShiTMPolynomialFuel.done xs [] [] (List.replicate budget true)))) =
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

end ShiTMPolynomialFueledAssembly
