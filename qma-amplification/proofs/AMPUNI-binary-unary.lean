import «AMPUNI-threshold-samples»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
noncomputable section
open Turing Turing.TM2

namespace ShiTMBinaryUnary

inductive Stack where
  | bits | count | value | scratch
  deriving DecidableEq
inductive Label where
  | scan | read | double (b : Bool) | restore (b : Bool) | done
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.bits, .count, .value, .scratch]
  (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList
  [.scan, .read, .double false, .double true, .restore false, .restore true, .done]
  (by intro l; cases l with
      | double b => cases b <;> simp
      | restore b => cases b <;> simp
      | _ => simp)
abbrev Gam (_ : Stack) := Bool
abbrev State := Option Bool

def storeFn (bits count value scratch : List Bool) : ∀ k : Stack, List (Gam k)
  | .bits => bits
  | .count => count
  | .value => value
  | .scratch => scratch

@[simp] theorem update_bits (xs cs vs ss zs : List Bool) :
    Function.update (storeFn xs cs vs ss) .bits zs = storeFn zs cs vs ss := by
  funext k; cases k <;> simp [storeFn]
@[simp] theorem update_count (xs cs vs ss zs : List Bool) :
    Function.update (storeFn xs cs vs ss) .count zs = storeFn xs zs vs ss := by
  funext k; cases k <;> simp [storeFn]
@[simp] theorem update_value (xs cs vs ss zs : List Bool) :
    Function.update (storeFn xs cs vs ss) .value zs = storeFn xs cs zs ss := by
  funext k; cases k <;> simp [storeFn]
@[simp] theorem update_scratch (xs cs vs ss zs : List Bool) :
    Function.update (storeFn xs cs vs ss) .scratch zs = storeFn xs cs vs zs := by
  funext k; cases k <;> simp [storeFn]

/-- Read exactly the number of bits specified by the unary counter. Each bit
updates the unary accumulator by Horner's rule a ↦ 2*a+b. -/
def machine : Label → Stmt Gam Label State
  | .scan => .pop .count (fun _ x => x)
      (.branch Option.isSome (.goto (fun _ => .read)) (.goto (fun _ => .done)))
  | .read => .pop .bits (fun _ x => x) (.goto (fun v => .double (v.getD false)))
  | .double b => .pop .value (fun _ x => x)
      (.branch Option.isSome
        (.push .scratch (fun _ => true) (.push .scratch (fun _ => true)
          (.goto (fun _ => .double b))))
        (.goto (fun _ => .restore b)))
  | .restore b => .pop .scratch (fun _ x => x)
      (.branch Option.isSome
        (.push .value (fun _ => true) (.goto (fun _ => .restore b)))
        (if b then .push .value (fun _ => true) (.goto (fun _ => .scan))
         else .goto (fun _ => .scan)))
  | .done => .halt
abbrev run := ShiTMSubroutine.run machine

def cfg (l : Label) (v : State) (xs cs vs ss : List Bool) : Cfg Gam Label State :=
  ⟨some l, v, storeFn xs cs vs ss⟩

theorem double_step (b : Bool) (v : State) (xs cs vs ss : List Bool) :
    run (some (cfg (.double b) v xs cs (true :: vs) ss)) =
      some (cfg (.double b) (some true) xs cs vs (true :: true :: ss)) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]

theorem double_end (b : Bool) (v : State) (xs cs ss : List Bool) :
    run (some (cfg (.double b) v xs cs [] ss)) =
      some (cfg (.restore b) none xs cs [] ss) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]

theorem double_run (a : Nat) (b : Bool) (v : State) (xs cs ss : List Bool) :
    run^[a+1] (some (cfg (.double b) v xs cs (List.replicate a true) ss)) =
      some (cfg (.restore b) none xs cs [] (List.replicate (2*a) true ++ ss)) := by
  induction a generalizing v ss with
  | zero => simpa using double_end b v xs cs ss
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      simp only [List.replicate_succ]
      rw [double_step, ih]
      congr 2
      simp [show 2*(a+1) = 2*a+2 by omega, List.replicate_add, List.append_assoc]

theorem restore_step (b : Bool) (v : State) (xs cs vs ss : List Bool) :
    run (some (cfg (.restore b) v xs cs vs (true :: ss))) =
      some (cfg (.restore b) (some true) xs cs (true :: vs) ss) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]

theorem restore_end (b : Bool) (v : State) (xs cs vs : List Bool) :
    run (some (cfg (.restore b) v xs cs vs [])) =
      some (cfg .scan none xs cs (List.replicate (if b then 1 else 0) true ++ vs) []) := by
  cases b <;> simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]

theorem restore_run (a : Nat) (b : Bool) (v : State) (xs cs vs : List Bool) :
    run^[a+1] (some (cfg (.restore b) v xs cs vs (List.replicate a true))) =
      some (cfg .scan none xs cs
        (List.replicate (a + if b then 1 else 0) true ++ vs) []) := by
  induction a generalizing v vs with
  | zero => simpa using restore_end b v xs cs vs
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      simp only [List.replicate_succ]
      rw [restore_step, ih]
      congr 2
      rw [show a+1+(if b then 1 else 0) = (a+(if b then 1 else 0))+1 by omega,
        List.replicate_succ']
      simp [List.append_assoc]

theorem digit_run (a : Nat) (b : Bool) (v : State) (xs cs : List Bool) :
    run^[3*a+4]
      (some (cfg .scan v (b::xs) (true::cs) (List.replicate a true) [])) =
      some (cfg .scan none xs cs (List.replicate (2*a + if b then 1 else 0) true) []) := by
  have hscan : run (some (cfg .scan v (b::xs) (true::cs) (List.replicate a true) [])) =
      some (cfg .read (some true) (b::xs) cs (List.replicate a true) []) := by
    simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]
  have hread : run (some (cfg .read (some true) (b::xs) cs (List.replicate a true) [])) =
      some (cfg (.double b) (some b) xs cs (List.replicate a true) []) := by
    simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]
  rw [show 3*a+4 = ((2*a+1)+(a+1))+2 by omega,
    Function.iterate_add_apply]
  rw [Function.iterate_succ_apply (n := 1), Function.iterate_one]
  rw [hscan, hread, Function.iterate_add_apply, double_run]
  simp only [List.append_nil]
  rw [restore_run]
  simp

def value (xs : List Bool) (a : Nat) : Nat :=
  a * 2^xs.length + ShiQMACenteredGap.binaryNumerator xs

theorem value_cons (b : Bool) (xs : List Bool) (a : Nat) :
    value (b::xs) a = value xs (2*a + if b then 1 else 0) := by
  cases b <;> simp [value, ShiQMACenteredGap.binaryNumerator, pow_succ] <;> ring

/-- A length-delimited decoder: the unused suffix is preserved, both working
stacks are empty at the end, and the time is linear in the decoded unary value
plus the number of digits. -/
theorem decode_run (xs rest : List Bool) (a : Nat) (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg .scan v (xs++rest) (List.replicate xs.length true)
        (List.replicate a true) [])) =
        some (cfg .done none rest [] (List.replicate (value xs a) true) []) ∧
      t + 3*a ≤ 3*value xs a + 4*xs.length + 1 := by
  induction xs generalizing a v with
  | nil =>
      refine ⟨1, ?_, ?_⟩
      · simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn,
          value, ShiQMACenteredGap.binaryNumerator]
      · simp [value, ShiQMACenteredGap.binaryNumerator, Nat.add_comm]
  | cons b xs ih =>
      obtain ⟨t, hr, ht⟩ := ih (2*a + if b then 1 else 0) none
      refine ⟨t+(3*a+4), ?_, ?_⟩
      · rw [Function.iterate_add_apply]
        simp only [List.cons_append, List.length_cons, List.replicate_succ]
        rw [digit_run, hr, value_cons]
      · rw [value_cons]
        simp only [List.length_cons]
        omega

theorem numerator_run (xs rest : List Bool) (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg .scan v (xs++rest) (List.replicate xs.length true) [] [])) =
        some (cfg .done none rest []
          (List.replicate (ShiQMACenteredGap.binaryNumerator xs) true) []) ∧
      t ≤ 3 * 2^xs.length + 4*xs.length + 1 := by
  obtain ⟨t, hr, ht⟩ := decode_run xs rest 0 v
  have hb := ShiQMACenteredGap.binaryNumerator_lt xs
  simp only [value, Nat.zero_mul, Nat.zero_add, List.replicate_zero] at hr ht
  exact ⟨t, hr, by omega⟩

/-- At the precision used by threshold sampling, the unary decoder's running
 time is polynomial in the retained packed input length. -/
theorem threshold_numerator_run (q : Polynomial ℕ) (n : Nat)
    (xs rest : List Bool) (v : State)
    (hx : xs.length = ShiQMAConstructiveSchedule.rounds q n) :
    ∃ t : Nat,
      run^[t] (some (cfg .scan v (xs++rest) (List.replicate xs.length true) [] [])) =
        some (cfg .done none rest []
          (List.replicate (ShiQMACenteredGap.binaryNumerator xs) true) []) ∧
      t ≤ 8 * 3^(Nat.log 2 (q.eval 1+1)+q.natDegree+4) *
        ((ShiTMThresholdSamples.input n xs rest).length+1)^(2*q.natDegree) := by
  obtain ⟨t, hr, ht⟩ := numerator_run xs rest v
  have hlen : xs.length < 2^xs.length := Nat.lt_two_pow_self
  have hcap := ShiTMThresholdSamples.capacity_bound q n xs rest hx
  rw [pow_succ] at hcap
  refine ⟨t, hr, ?_⟩
  nlinarith

end ShiTMBinaryUnary

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMBinaryUnary.double_run, ``ShiTMBinaryUnary.restore_run,
      ``ShiTMBinaryUnary.digit_run, ``ShiTMBinaryUnary.value_cons,
      ``ShiTMBinaryUnary.decode_run, ``ShiTMBinaryUnary.numerator_run,
      ``ShiTMBinaryUnary.threshold_numerator_run] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected binary-unary axiom {ax} in {name}"
    logInfo m!"BINARY_UNARY_CHECKED {name}; axioms {axioms}"
