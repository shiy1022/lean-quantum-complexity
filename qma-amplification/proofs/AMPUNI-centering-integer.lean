import «AMPUNI-binary-unary»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
noncomputable section
open Turing Turing.TM2

namespace ShiTMBinaryUnary

theorem zero_digits_numerator (k : Nat) :
    ShiQMACenteredGap.binaryNumerator (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ, ShiQMACenteredGap.binaryNumerator] using ih

/-- Reuse the decoder to construct a unary power of two from an initial one.
The counted zero digits are consumed and the following input is preserved. -/
theorem capacity_run (k : Nat) (rest : List Bool) (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg .scan v (List.replicate k false ++ rest)
        (List.replicate k true) [true] [])) =
        some (cfg .done none rest [] (List.replicate (2^k) true) []) ∧
      t ≤ 3*2^k + 4*k + 1 := by
  obtain ⟨t, hr, ht⟩ := decode_run (List.replicate k false) rest 1 v
  simp only [value, List.length_replicate, zero_digits_numerator,
    Nat.one_mul, Nat.add_zero] at hr ht
  exact ⟨t, hr, by omega⟩

/-- Capacity construction fits the same polynomial clock as the arithmetic
input. The extra factor covers the decoder's doubling and restore passes. -/
theorem threshold_capacity_run (q : Polynomial ℕ) (n : Nat) (as bs rest : List Bool)
    (v : State) (ha : as.length = ShiQMAConstructiveSchedule.rounds q n) :
    ∃ t : Nat,
      run^[t] (some (cfg .scan v (List.replicate (as.length+1) false ++ rest)
        (List.replicate (as.length+1) true) [true] [])) =
        some (cfg .done none rest [] (List.replicate (2^(as.length+1)) true) []) ∧
      t ≤ 16 * 3^(Nat.log 2 (q.eval 1+1)+q.natDegree+4) *
        ((ShiTMThresholdSamples.input n as bs).length+1)^(2*q.natDegree) := by
  obtain ⟨t, hr, ht⟩ := capacity_run (as.length+1) rest v
  have hlen : as.length+1 < 2^(as.length+1) := Nat.lt_two_pow_self
  have hcap := ShiTMThresholdSamples.capacity_bound q n as bs ha
  refine ⟨t, hr, ?_⟩
  nlinarith

end ShiTMBinaryUnary

namespace ShiTMCenteringInteger
inductive Stack where
  | capacity | first | second
  deriving DecidableEq
inductive Label where
  | first | second | done
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.capacity, .first, .second]
  (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList [.first, .second, .done]
  (by intro l; cases l <;> simp)
abbrev Gam (_ : Stack) := Bool
abbrev State := Option Bool

def storeFn (cs as bs : List Bool) : ∀ k : Stack, List (Gam k)
  | .capacity => cs
  | .first => as
  | .second => bs
@[simp] theorem update_capacity (cs as bs zs : List Bool) :
    Function.update (storeFn cs as bs) .capacity zs = storeFn zs as bs := by
  funext k; cases k <;> simp [storeFn]
@[simp] theorem update_first (cs as bs zs : List Bool) :
    Function.update (storeFn cs as bs) .first zs = storeFn cs zs bs := by
  funext k; cases k <;> simp [storeFn]
@[simp] theorem update_second (cs as bs zs : List Bool) :
    Function.update (storeFn cs as bs) .second zs = storeFn cs as zs := by
  funext k; cases k <;> simp [storeFn]

/-- Saturating subtraction. Each operand token removes one capacity token;
popping an empty capacity is harmless, so the routine needs no size premise. -/
def machine : Label → Stmt Gam Label State
  | .first => .pop .first (fun _ x => x)
      (.branch Option.isSome
        (.pop .capacity (fun _ x => x) (.goto (fun _ => .first)))
        (.goto (fun _ => .second)))
  | .second => .pop .second (fun _ x => x)
      (.branch Option.isSome
        (.pop .capacity (fun _ x => x) (.goto (fun _ => .second)))
        (.goto (fun _ => .done)))
  | .done => .halt
abbrev run := ShiTMSubroutine.run machine

def cfg (l : Label) (v : State) (cs as bs : List Bool) : Cfg Gam Label State :=
  ⟨some l, v, storeFn cs as bs⟩

theorem first_step (c : Nat) (v : State) (as bs : List Bool) :
    run (some (cfg .first v (List.replicate c true) (true::as) bs)) =
      some (cfg .first (if c=0 then none else some true)
        (List.replicate (c-1) true) as bs) := by
  cases c <;> simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux,
    storeFn, List.replicate_succ]

theorem first_run (a c : Nat) (v : State) (bs : List Bool) :
    run^[a+1] (some (cfg .first v (List.replicate c true)
      (List.replicate a true) bs)) =
      some (cfg .second none (List.replicate (c-a) true) [] bs) := by
  induction a generalizing c v with
  | zero => simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      simp only [List.replicate_succ]
      rw [first_step, ih, show c-1-a = c-(a+1) by omega]

theorem second_step (c : Nat) (v : State) (as bs : List Bool) :
    run (some (cfg .second v (List.replicate c true) as (true::bs))) =
      some (cfg .second (if c=0 then none else some true)
        (List.replicate (c-1) true) as bs) := by
  cases c <;> simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux,
    storeFn, List.replicate_succ]

theorem second_run (b c : Nat) (v : State) (as : List Bool) :
    run^[b+1] (some (cfg .second v (List.replicate c true)
      as (List.replicate b true))) =
      some (cfg .done none (List.replicate (c-b) true) as []) := by
  induction b generalizing c v with
  | zero => simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]
  | succ b ih =>
      rw [Function.iterate_succ_apply]
      simp only [List.replicate_succ]
      rw [second_step, ih, show c-1-b = c-(b+1) by omega]

/-- Exact subtraction of both decoded numerators, including saturating inputs.
The operand stacks are empty at the terminal label. -/
theorem subtract_run (c a b : Nat) (v : State) :
    run^[a+b+2] (some (cfg .first v (List.replicate c true)
      (List.replicate a true) (List.replicate b true))) =
      some (cfg .done none (List.replicate (c-(a+b)) true) [] []) := by
  rw [show a+b+2 = (b+1)+(a+1) by omega, Function.iterate_add_apply,
    first_run, second_run, Nat.sub_sub]

theorem centering_numerator_run (k a b : Nat) (v : State) :
    run^[a+b+2] (some (cfg .first v (List.replicate (2^(k+1)) true)
      (List.replicate a true) (List.replicate b true))) =
      some (cfg .done none
        (List.replicate (ShiQMACenteredGap.centeringNumerator k a b) true) [] []) :=
  subtract_run (2^(k+1)) a b v

/-- For equally long threshold approximations, subtraction costs at most the
capacity, including its two end-of-stack transitions. -/
theorem subtraction_cost (as bs : List Bool) (hlen : as.length = bs.length) :
    ShiQMACenteredGap.binaryNumerator as + ShiQMACenteredGap.binaryNumerator bs + 2
      ≤ 2^(as.length+1) := by
  have ha := ShiQMACenteredGap.binaryNumerator_lt as
  have hb := ShiQMACenteredGap.binaryNumerator_lt bs
  rw [← hlen] at hb
  rw [pow_succ]
  omega

theorem threshold_subtraction_cost (q : Polynomial ℕ) (n : Nat) (as bs : List Bool)
    (ha : as.length = ShiQMAConstructiveSchedule.rounds q n)
    (hb : bs.length = as.length) :
    ShiQMACenteredGap.binaryNumerator as + ShiQMACenteredGap.binaryNumerator bs + 2 ≤
      2 * 3^(Nat.log 2 (q.eval 1+1)+q.natDegree+4) *
        ((ShiTMThresholdSamples.input n as bs).length+1)^(2*q.natDegree) :=
  (subtraction_cost as bs hb.symm).trans
    (ShiTMThresholdSamples.capacity_bound q n as bs ha)

end ShiTMCenteringInteger

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMBinaryUnary.zero_digits_numerator, ``ShiTMBinaryUnary.capacity_run,
      ``ShiTMBinaryUnary.threshold_capacity_run,
      ``ShiTMCenteringInteger.first_run, ``ShiTMCenteringInteger.second_run,
      ``ShiTMCenteringInteger.subtract_run, ``ShiTMCenteringInteger.centering_numerator_run,
      ``ShiTMCenteringInteger.subtraction_cost, ``ShiTMCenteringInteger.threshold_subtraction_cost] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected centering-integer axiom {ax} in {name}"
    logInfo m!"CENTERING_INTEGER_CHECKED {name}; axioms {axioms}"
