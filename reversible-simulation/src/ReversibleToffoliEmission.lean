import ReversibleEmissionSequence
import ReversibleExactToffoli

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

/-- Execution-order printing fields for the actual recovered 37-layer circuit.
The template is fixed; only the three wire-number registers vary with input length. -/
def toffoliEmissionAtoms (p q r : R) : List (EmissionAtom R) :=
  [.natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 0),
    .natural r,
    .natural p,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 4),
    .natural r,
    .natural q,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 4),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .natural q,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 4),
    .natural r,
    .natural p,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 4),
    .natural r,
    .natural p,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 4),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .natural p,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 4),
    .natural r,
    .natural q,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 4),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .natural q,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 4),
    .natural q,
    .natural p,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 4),
    .natural q,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural q,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural q,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural q,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural q,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural q,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural q,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural q,
    .natural p,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 4),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural q,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural p,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 2),
    .natural r,
    .literal (ShiBQP.encNat 1 ++ ShiBQP.encNat 0)]

/-- A syntactically explicit form of the already verified Toffoli layers. -/
def toffoliEmissionLayers {m : Nat} (p q r : Fin m)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : ShiShallow.Layered m :=
  ([ ShiShallow.Instr.h r,
    ShiShallow.Instr.t p, ShiShallow.Instr.t q, ShiShallow.Instr.t r,
    ShiShallow.Instr.cnot p q hpq,
    ShiShallow.Instr.t q, ShiShallow.Instr.t q, ShiShallow.Instr.t q, ShiShallow.Instr.t q, ShiShallow.Instr.t q, ShiShallow.Instr.t q, ShiShallow.Instr.t q,
    ShiShallow.Instr.cnot p q hpq,
    ShiShallow.Instr.cnot q r hqr,
    ShiShallow.Instr.t r, ShiShallow.Instr.t r, ShiShallow.Instr.t r, ShiShallow.Instr.t r, ShiShallow.Instr.t r, ShiShallow.Instr.t r, ShiShallow.Instr.t r,
    ShiShallow.Instr.cnot q r hqr,
    ShiShallow.Instr.cnot p r hpr,
    ShiShallow.Instr.t r, ShiShallow.Instr.t r, ShiShallow.Instr.t r, ShiShallow.Instr.t r, ShiShallow.Instr.t r, ShiShallow.Instr.t r, ShiShallow.Instr.t r,
    ShiShallow.Instr.cnot p r hpr,
    ShiShallow.Instr.cnot p r hpr,
    ShiShallow.Instr.cnot q r hqr,
    ShiShallow.Instr.t r,
    ShiShallow.Instr.cnot q r hqr,
    ShiShallow.Instr.cnot p r hpr,
    ShiShallow.Instr.h r ]).map (fun g => [g])

theorem toffoliEmissionLayers_eq {m : Nat} (p q r : Fin m)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    toffoliEmissionLayers p q r hpq hpr hqr =
      ShiReversibleGateBridge.toffoliCircuit p q r hpq hpr hqr := rfl

/-- Exact payload bytes, including every singleton layer header and unary wire field. -/
theorem toffoliEmissionAtoms_bytes {m : Nat} (p q r : R) (i j k : Fin m)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (cs : R → Nat)
    (hi : cs p = i.val) (hj : cs q = j.val) (hk : cs r = k.val) :
    emissionBytes (toffoliEmissionAtoms p q r) cs =
      ((ShiReversibleGateBridge.toffoliCircuit i j k hij hik hjk).map ShiBQP.encLayer).flatten := by
  rw [← toffoliEmissionLayers_eq]
  simp [toffoliEmissionAtoms, toffoliEmissionLayers, emissionBytes, EmissionAtom.bytes,
    ShiBQP.encLayer, ShiBQP.encStr, ShiBQP.encInstr, hi, hj, hk, List.append_assoc]

/-- Actual finite printer for the full standard-gate Toffoli expansion, with counted runtime. -/
theorem toffoliEmission_run {m : Nat} (p q r : R) (i j k : Fin m)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (caller : L → CounterInstr R L) (buf tmp : R) (stop : L)
    (hp : p ≠ buf ∧ p ≠ tmp) (hq : q ≠ buf ∧ q ≠ tmp) (hr : r ≠ buf ∧ r ≠ tmp)
    (hbt : buf ≠ tmp) (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0)
    (hi : cs p = i.val) (hj : cs q = j.val) (hk : cs r = k.val) (ys : List Bool) :
    CounterRun (emissionCode (toffoliEmissionAtoms p q r) caller buf tmp stop)
      ⟨some (emissionEntry (toffoliEmissionAtoms p q r) stop), cs, ys⟩
      (emissionSteps (toffoliEmissionAtoms p q r) cs)
      ⟨some (emissionExit (toffoliEmissionAtoms p q r) stop), cs,
        ((ShiReversibleGateBridge.toffoliCircuit i j k hij hik hjk).map ShiBQP.encLayer).flatten ++ ys⟩ := by
  have hv : ∀ a ∈ toffoliEmissionAtoms p q r, a.Valid buf tmp := by
    intro a ha
    simp only [toffoliEmissionAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83
    all_goals subst a; simp [EmissionAtom.Valid, hp, hq, hr]
  have h := emissionCode_run (toffoliEmissionAtoms p q r) caller buf tmp stop hv hbt cs hb ht ys
  simpa only [toffoliEmissionAtoms_bytes p q r i j k hij hik hjk cs hi hj hk] using h

/-- The whole fixed Toffoli template has an exact polynomial instruction clock
whenever its address registers are polynomial functions of input length. -/
theorem toffoliEmission_clock (p q r : R) (sizes : R → Polynomial Nat) (n : Nat) :
    emissionSteps (toffoliEmissionAtoms p q r) (fun v => (sizes v).eval n) =
      (emissionClock (toffoliEmissionAtoms p q r) sizes).eval n :=
  (emissionClock_eval (toffoliEmissionAtoms p q r) sizes n).symm

end ShiReversibleGenerator
