import «AMPUNI-joint-generator»
import «AMPUNI-scaled-log-entry»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
noncomputable section
open Turing Turing.TM2

namespace ShiTMThresholdPrecision
open ShiTMUnaryLog

abbrev Label := Option ShiTMUnaryLog.Label

def offset (q : Polynomial ℕ) : Nat := ShiTMScaledLog.scheduleOffset q + 1

def machine (q : Polynomial ℕ) : Label → Stmt Gam Label State
  | none => .push .a (fun _ => true) (.goto (fun _ => some (.scan false)))
  | some l => ShiTMSubroutine.stmt some (ShiTMScaledLog.machine q.natDegree (offset q) l)

def finiteMachine (q : Polynomial ℕ) : FinTM2 where
  K := Stack
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := .a
  k₁ := .counter
  Γ := Gam
  Λ := Label
  main := none
  ΛFin := inferInstance
  σ := State
  initialState := (none, true)
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine q

def run (q : Polynomial ℕ) := ShiTMSubroutine.run (machine q)

private theorem cfg_ext {K L V : Type} {G : K → Type} {c d : Cfg G L V}
    (hl : c.l = d.l) (hv : c.var = d.var) (hs : c.stk = d.stk) : c = d := by
  cases c; cases d; cases hl; cases hv; cases hs; rfl

/-- The leading extra mark changes the logarithm argument from n to n+1. -/
theorem entry_step (q : Polynomial ℕ) (n : Nat) :
    run q (some (Turing.initList (finiteMachine q) (ShiBQP.unary n))) =
      some (ShiTMSubroutine.cfg some
        (Turing.initList (ShiTMScaledLog.finiteMachine q.natDegree (offset q))
          (ShiBQP.unary (n+1)))) := by
  simp only [run, ShiTMSubroutine.run, Option.bind_some, Turing.initList, finiteMachine,
    step, machine, stepAux, ShiTMSubroutine.cfg, ShiTMScaledLog.finiteMachine]
  congr 1
  apply cfg_ext <;> try rfl
  funext j
  cases j <;> simp [ShiBQP.unary, List.replicate_succ]

theorem offset_spec (q : Polynomial ℕ) (n : Nat) :
    offset q + q.natDegree * Nat.log 2 (n+1) = ShiQMAConstructiveSchedule.rounds q n := by
  simp only [offset, ShiTMScaledLog.scheduleOffset, ShiQMAConstructiveSchedule.rounds,
    ShiQMAConstructiveSchedule.exponentBudget, Nat.mul_add, Nat.mul_one]
  omega

/-- Exact requested unary precision, with a linear bound on valid unary input. -/
theorem precision_run (q : Polynomial ℕ) (n : Nat) :
    ∃ t : Nat,
      (run q)^[t] (some (Turing.initList (finiteMachine q) (ShiBQP.unary n))) =
        some (Turing.haltList (finiteMachine q) (ShiBQP.unary (ShiQMAConstructiveSchedule.rounds q n))) ∧
      t ≤ 4*n+10 := by
  obtain ⟨t, hr, ht⟩ := ShiTMScaledLog.counter_from_init q.natDegree (offset q) (n+1)
  have hl := ShiTMSubroutine.run_iter_lift
    (ShiTMScaledLog.machine q.natDegree (offset q)) (machine q) some (fun _ => rfl) t
    (some (Turing.initList (ShiTMScaledLog.finiteMachine q.natDegree (offset q)) (ShiBQP.unary (n+1))))
  have hr' : (ShiTMSubroutine.run (ShiTMScaledLog.machine q.natDegree (offset q)))^[t]
      (some (Turing.initList (ShiTMScaledLog.finiteMachine q.natDegree (offset q)) (ShiBQP.unary (n+1)))) =
      some (Turing.haltList (ShiTMScaledLog.finiteMachine q.natDegree (offset q))
        (ShiBQP.unary (ShiQMAConstructiveSchedule.rounds q n))) := by
    simpa only [offset_spec, ShiBQP.unary, ShiTMScaledLog.finiteMachine] using hr
  rw [hr'] at hl
  refine ⟨t+1, ?_, by omega⟩
  rw [Function.iterate_succ_apply, entry_step]
  simpa only [run, Option.map_some, ShiTMSubroutine.cfg, Turing.haltList,
    ShiTMScaledLog.finiteMachine, finiteMachine, Option.map_none] using hl

/-- Total polynomial-time precision generation. The clock handles non-unary
strings as well, while retaining the proved exact output on unary inputs. -/
theorem precision_generator (q : Polynomial ℕ) :
    ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
      ∀ n, g (ShiBQP.unary n) = ShiBQP.unary (ShiQMAConstructiveSchedule.rounds q n) := by
  let tm := finiteMachine q
  let ein : Bool ≃ tm.Γ tm.k₀ := Equiv.refl Bool
  let full := ShiTMTotalPolynomialClocked.finiteMachine tm ein 0 10
  obtain ⟨P, hP⟩ := ShiTMTotalPolynomialClocked.total_polynomial tm ein 0 10
  have hall : ∀ xs : List Bool, ∃ ys : List Bool,
      Nonempty (TM2OutputsInTime full (xs.map (Equiv.refl Bool).symm)
        (some (ys.map (Equiv.refl Bool).symm)) (P.eval xs.length)) := by
    intro xs
    obtain ⟨ys, hy⟩ := hP xs
    have hin : xs.map (Equiv.refl Bool).symm = xs := List.map_id xs
    have hout : ys.map (Equiv.refl Bool).symm = ys := List.map_id ys
    exact ⟨ys, (congrArg₂ (fun (a b : List Bool) =>
      Nonempty (TM2OutputsInTime full a (some b) (P.eval xs.length))) hin hout).mpr hy⟩
  obtain ⟨g, hg, hunique⟩ := ShiTMTotalFunction.function_of_total_polynomial full
    (Equiv.refl Bool) (Equiv.refl Bool) P hall
  obtain ⟨Q, hQ⟩ := ShiTMTotalPolynomialClocked.valid_run_polynomial tm ein 0 10
  refine ⟨g, hg, ?_⟩
  intro n
  let xs := ShiBQP.unary n
  let ys := ShiBQP.unary (ShiQMAConstructiveSchedule.rounds q n)
  obtain ⟨steps, hr, hb⟩ := precision_run q n
  have hin : xs.map ein = xs := List.map_id xs
  have hr' : (ShiTMSubroutine.run tm.m)^[steps]
      (some (Turing.initList tm (xs.map ein))) = some (Turing.haltList tm ys) := by
    exact (congrArg (fun input : List (tm.Γ tm.k₀) =>
      (ShiTMSubroutine.run tm.m)^[steps] (some (Turing.initList tm input))) hin).trans hr
  have hsteps : steps ≤ 10*(xs.length+1)^(0+1) := by
    simp only [xs, ShiBQP.unary, List.length_replicate, Nat.zero_add, pow_one]
    omega
  have hf := hQ xs steps (Turing.haltList tm ys).var (Turing.haltList tm ys).stk hr' hsteps
  have hout : (Turing.haltList tm ys).stk tm.k₁ = ys := by
    simp only [Turing.haltList]
    rw [dif_pos trivial]
    rfl
  have hf' : Nonempty (TM2OutputsInTime full xs (some ys) (Q.eval xs.length)) :=
    (congrArg (fun output : List Bool =>
      Nonempty (TM2OutputsInTime full xs (some output) (Q.eval xs.length))) hout).mp hf
  apply hunique xs ys (Q.eval xs.length)
  have hin' : xs.map (Equiv.refl Bool).symm = xs := List.map_id xs
  have hout' : ys.map (Equiv.refl Bool).symm = ys := List.map_id ys
  exact (congrArg₂ (fun (a b : List Bool) =>
    Nonempty (TM2OutputsInTime full a (some b) (Q.eval xs.length))) hin' hout').mpr hf'

/-- Supply n and the computed precision to the threshold approximation algorithms. -/
theorem request_generator (q : Polynomial ℕ) :
    ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
      ∀ n, g (ShiBQP.unary n) =
        ShiQMAGeneralGap.thresholdInput n (ShiQMAConstructiveSchedule.rounds q n) := by
  obtain ⟨precision, hp, hprecision⟩ := precision_generator q
  refine ⟨fun xs => ShiBQP.encNat xs.length ++ precision xs,
    QMAReferenceRebuilt.«ShiTMInputRetention.polyTimeComputable_length_prefix» precision hp, ?_⟩
  intro n
  dsimp only
  rw [hprecision]
  simp only [ShiBQP.unary, List.length_replicate, ShiQMAGeneralGap.thresholdInput]

end ShiTMThresholdPrecision

namespace ShiTMThresholdSamples
open ShiQMAGeneralGap ShiQMAConstructiveSchedule

/-- Keep unary n in the arithmetic input: the known unary numerator bound is
polynomial in n, while it can be exponential in the precision alone. -/
def input (n : Nat) (as bs : List Bool) : PvsNP.Str :=
  ShiBQP.encNat n ++ ShiTMCenteringPacking.input as bs

theorem input_length (n k : Nat) (as bs : List Bool) (ha : as.length = k) (hb : bs.length = k) :
    (input n as bs).length = n+3*k+2 := by
  simp [input, ShiTMCenteringPacking.input, ShiBQP.encNat, ha, hb]
  omega

/-- Even a unary capacity counter fits a polynomial in the retained packed
input length, not merely in an external parameter. -/
theorem capacity_bound (q : Polynomial ℕ) (n : Nat) (as bs : List Bool)
    (ha : as.length = rounds q n) :
    2^(as.length+1) ≤
      2 * 3^(Nat.log 2 (q.eval 1+1)+q.natDegree+4) * ((input n as bs).length+1)^(2*q.natDegree) := by
  have hn : n+1 ≤ (input n as bs).length+1 := by
    simp only [input, ShiTMCenteringPacking.input, List.length_append, ShiBQP.encNat,
      List.length_replicate, List.length_singleton]
    omega
  have hpow := Nat.pow_le_pow_left hn (2*q.natDegree)
  have hcopies := copies_rounds_le q n
  have htwo := Nat.pow_le_pow_left (by decide : 2 ≤ 3) (rounds q n)
  have hmul := Nat.mul_le_mul_left (3^(Nat.log 2 (q.eval 1+1)+q.natDegree+4)) hpow
  rw [ha, pow_succ]
  nlinarith

/-- Run both supplied approximators at the computed precision and package their
outputs with the original input length. No threshold-arithmetic oracle is used. -/
theorem samples_generator {a b : Nat → ℝ} (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) :
    ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
      ∀ n, g (ShiBQP.unary n) =
        input n (A.approximate (thresholdInput n (rounds q n)))
          (B.approximate (thresholdInput n (rounds q n))) := by
  obtain ⟨request, hr, hrequest⟩ := ShiTMThresholdPrecision.request_generator q
  have ha := ShiTMCenteringPacking.polyTimeComputable_comp request A.approximate hr A.polynomialTime
  have hb := ShiTMCenteringPacking.polyTimeComputable_comp request B.approximate hr B.polynomialTime
  let pair : PvsNP.Str → PvsNP.Str := fun xs =>
    ShiTMCenteringPacking.input (A.approximate (request xs)) (B.approximate (request xs))
  have hp : PvsNP.PolyTimeComputable pair :=
    ShiTMJoint.polyTimeComputable_pair (A.approximate ∘ request) (B.approximate ∘ request) ha hb
  refine ⟨fun xs => ShiBQP.encNat xs.length ++ pair xs,
    QMAReferenceRebuilt.«ShiTMInputRetention.polyTimeComputable_length_prefix» pair hp, ?_⟩
  intro n
  dsimp only [pair]
  rw [hrequest]
  simp only [ShiBQP.unary, List.length_replicate, input]

end ShiTMThresholdSamples

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMThresholdPrecision.entry_step, ``ShiTMThresholdPrecision.offset_spec,
      ``ShiTMThresholdPrecision.precision_run, ``ShiTMThresholdPrecision.precision_generator,
      ``ShiTMThresholdPrecision.request_generator, ``ShiTMThresholdSamples.input_length, ``ShiTMThresholdSamples.capacity_bound,
      ``ShiTMThresholdSamples.samples_generator] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected threshold-samples axiom {ax} in {name}"
    logInfo m!"THRESHOLD_SAMPLES_CHECKED {name}; axioms {axioms}"
