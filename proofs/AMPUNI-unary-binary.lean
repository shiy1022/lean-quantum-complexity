import «AMPUNI-centering-integer»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
noncomputable section
open Turing Turing.TM2

namespace ShiTMUnaryBinary
open ShiQMACenteredGap

/-- Extract least significant bits by division, prepending the later bits. -/
def quotientBits : Nat → Nat → List Bool
  | 0, _ => []
  | k+1, n => quotientBits k (n/2) ++ [decide (n%2=1)]

theorem quotientBits_length (k n : Nat) : (quotientBits k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [quotientBits, ih]

theorem numerator_append_bit (xs : List Bool) (b : Bool) :
    binaryNumerator (xs ++ [b]) = 2*binaryNumerator xs + (if b then 1 else 0) := by
  induction xs with
  | nil => cases b <;> simp [binaryNumerator]
  | cons a xs ih =>
      cases a <;> simp [binaryNumerator, pow_succ, ih]
      ring

theorem numerator_injective (xs ys : List Bool) (hl : xs.length = ys.length)
    (hv : binaryNumerator xs = binaryNumerator ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
      exact hy.symm
  | cons a xs ih =>
      cases ys with
      | nil => simp at hl
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using hl
          have hx := binaryNumerator_lt xs
          have hy := binaryNumerator_lt ys
          rw [← ht] at hy
          cases a <;> cases b <;>
            simp only [binaryNumerator, Bool.false_eq_true, ↓reduceIte, zero_add, ← ht] at hv
          · exact congrArg (List.cons false) (ih ys ht hv)
          · omega
          · omega
          · exact congrArg (List.cons true) (ih ys ht (by omega))

theorem quotientBits_numerator (k n : Nat) (hn : n < 2^k) :
    binaryNumerator (quotientBits k n) = n := by
  induction k generalizing n with
  | zero =>
      have hn0 : n = 0 := by simpa using hn
      subst n
      rfl
  | succ k ih =>
      have hq : n/2 < 2^k := by rw [pow_succ] at hn; omega
      rw [quotientBits, numerator_append_bit, ih (n/2) hq]
      by_cases h : n%2=1 <;> simp [h] <;> omega

/-- Strict range is essential: fractionBits at its upper endpoint does not
coincide with modular binary extraction. -/
theorem quotientBits_eq_fractionBits (k n : Nat) (hn : n < 2^k) :
    quotientBits k n = fractionBits k n := by
  apply numerator_injective
  · rw [quotientBits_length, fractionBits_length]
  · rw [quotientBits_numerator k n hn, fractionBits_numerator k n hn]

inductive Stack where
  | count | value | scratch | output
  deriving DecidableEq
inductive Label where
  | scan | half (parity : Bool) | restore | done
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.count, .value, .scratch, .output]
  (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList [.scan, .half false, .half true, .restore, .done]
  (by intro l; cases l with | half b => cases b <;> simp | _ => simp)
abbrev Gam (_ : Stack) := Bool
abbrev State := Option Bool

def storeFn (cs vs ss os : List Bool) : ∀ k : Stack, List (Gam k)
  | .count => cs
  | .value => vs
  | .scratch => ss
  | .output => os
@[simp] theorem update_count (cs vs ss os zs : List Bool) :
    Function.update (storeFn cs vs ss os) .count zs = storeFn zs vs ss os := by
  funext k; cases k <;> simp [storeFn]
@[simp] theorem update_value (cs vs ss os zs : List Bool) :
    Function.update (storeFn cs vs ss os) .value zs = storeFn cs zs ss os := by
  funext k; cases k <;> simp [storeFn]
@[simp] theorem update_scratch (cs vs ss os zs : List Bool) :
    Function.update (storeFn cs vs ss os) .scratch zs = storeFn cs vs zs os := by
  funext k; cases k <;> simp [storeFn]
@[simp] theorem update_output (cs vs ss os zs : List Bool) :
    Function.update (storeFn cs vs ss os) .output zs = storeFn cs vs ss zs := by
  funext k; cases k <;> simp [storeFn]

/-- One counted pass halves the unary accumulator and prepends its remainder
bit. A restore pass moves the quotient back for the next output digit. -/
def machine : Label → Stmt Gam Label State
  | .scan => .pop .count (fun _ x => x)
      (.branch Option.isSome (.goto (fun _ => .half false)) (.goto (fun _ => .done)))
  | .half b => .pop .value (fun _ x => x)
      (.branch Option.isSome
        (if b then .push .scratch (fun _ => true) (.goto (fun _ => .half false))
         else .goto (fun _ => .half true))
        (.push .output (fun _ => b) (.goto (fun _ => .restore))))
  | .restore => .pop .scratch (fun _ x => x)
      (.branch Option.isSome
        (.push .value (fun _ => true) (.goto (fun _ => .restore)))
        (.goto (fun _ => .scan)))
  | .done => .halt
abbrev run := ShiTMSubroutine.run machine

def cfg (l : Label) (v : State) (cs vs ss os : List Bool) : Cfg Gam Label State :=
  ⟨some l, v, storeFn cs vs ss os⟩

theorem half_first (v : State) (cs vs ss os : List Bool) :
    run (some (cfg (.half false) v cs (true::vs) ss os)) =
      some (cfg (.half true) (some true) cs vs ss os) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]

theorem half_second (v : State) (cs vs ss os : List Bool) :
    run (some (cfg (.half true) v cs (true::vs) ss os)) =
      some (cfg (.half false) (some true) cs vs (true::ss) os) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]

theorem half_end (b : Bool) (v : State) (cs ss os : List Bool) :
    run (some (cfg (.half b) v cs [] ss os)) =
      some (cfg .restore none cs [] ss (b::os)) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]

theorem pairs_run (m : Nat) (v : State) (cs vs ss os : List Bool) :
    run^[2*m] (some (cfg (.half false) v cs (List.replicate (2*m) true ++ vs) ss os)) =
      some (cfg (.half false) (if m=0 then v else some true) cs vs
        (List.replicate m true ++ ss) os) := by
  induction m generalizing v ss with
  | zero => simp
  | succ m ih =>
      rw [show 2*(m+1)=2*m+2 by omega, Function.iterate_add_apply]
      have hp : List.replicate (2*m+2) true = true::true::List.replicate (2*m) true := by
        rw [show 2*m+2 = 2+2*m by omega, List.replicate_add]; rfl
      rw [hp]
      simp only [List.cons_append]
      rw [Function.iterate_succ_apply (n := 1), Function.iterate_one,
        half_first, half_second, ih]
      simp [List.replicate_succ', List.append_assoc]

theorem half_even (m : Nat) (v : State) (cs ss os : List Bool) :
    run^[2*m+1] (some (cfg (.half false) v cs (List.replicate (2*m) true) ss os)) =
      some (cfg .restore none cs [] (List.replicate m true ++ ss) (false::os)) := by
  rw [show 2*m+1 = 1+2*m by omega, Function.iterate_add_apply, Function.iterate_one]
  simpa using (congrArg run (pairs_run m v cs [] ss os)).trans (half_end false _ _ _ _)

theorem half_odd (m : Nat) (v : State) (cs ss os : List Bool) :
    run^[2*m+2] (some (cfg (.half false) v cs (List.replicate (2*m+1) true) ss os)) =
      some (cfg .restore none cs [] (List.replicate m true ++ ss) (true::os)) := by
  have hp : List.replicate (2*m+1) true = List.replicate (2*m) true ++ [true] := by
    rw [List.replicate_add]; rfl
  rw [show 2*m+2 = 2+2*m by omega, Function.iterate_add_apply, hp, pairs_run]
  rw [Function.iterate_succ_apply (n := 1), Function.iterate_one, half_first, half_end]

theorem half_run (n : Nat) (v : State) (cs ss os : List Bool) :
    run^[n+1] (some (cfg (.half false) v cs (List.replicate n true) ss os)) =
      some (cfg .restore none cs [] (List.replicate (n/2) true ++ ss)
        (decide (n%2=1)::os)) := by
  by_cases h : n%2=1
  · have hn : n = 2*(n/2)+1 := by omega
    have hh := half_odd (n/2) v cs ss os
    rw [show 2*(n/2)+2 = n+1 by omega, ← hn] at hh
    simpa only [h, decide_true] using hh
  · have hn : n = 2*(n/2) := by omega
    have hh := half_even (n/2) v cs ss os
    rw [← hn] at hh
    simpa only [h, decide_false] using hh

theorem restore_run (m : Nat) (v : State) (cs vs os : List Bool) :
    run^[m+1] (some (cfg .restore v cs vs (List.replicate m true) os)) =
      some (cfg .scan none cs (List.replicate m true ++ vs) [] os) := by
  induction m generalizing v vs with
  | zero => simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]
  | succ m ih =>
      have hs : run (some (cfg .restore v cs vs (List.replicate (m+1) true) os)) =
          some (cfg .restore (some true) cs (true::vs) (List.replicate m true) os) := by
        simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn, List.replicate_succ]
      rw [Function.iterate_succ_apply, hs, ih]
      simp [List.replicate_succ', List.append_assoc]

theorem digit_run (n : Nat) (v : State) (cs os : List Bool) :
    run^[n+n/2+3] (some (cfg .scan v (true::cs) (List.replicate n true) [] os)) =
      some (cfg .scan none cs (List.replicate (n/2) true) [] (decide (n%2=1)::os)) := by
  have hs : run (some (cfg .scan v (true::cs) (List.replicate n true) [] os)) =
      some (cfg (.half false) (some true) cs (List.replicate n true) [] os) := by
    simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn]
  rw [show n+n/2+3 = ((n/2+1)+(n+1))+1 by omega,
    Function.iterate_succ_apply, hs, Function.iterate_add_apply, half_run]
  simp only [List.append_nil]
  rw [restore_run]
  simp

/-- Exact fixed-width output and linear cost in unary input plus output width.
All work stacks are empty when the input lies below the requested capacity. -/
theorem encode_run (k n : Nat) (hn : n < 2^k) (v : State) (os : List Bool) :
    ∃ t : Nat,
      run^[t] (some (cfg .scan v (List.replicate k true) (List.replicate n true) [] os)) =
        some (cfg .done none [] [] [] (quotientBits k n ++ os)) ∧
      t ≤ 3*n+3*k+1 := by
  induction k generalizing n v os with
  | zero =>
      have hn0 : n=0 := by simpa using hn
      subst n
      refine ⟨1, ?_, by simp⟩
      simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, storeFn, quotientBits]
  | succ k ih =>
      have hq : n/2 < 2^k := by rw [pow_succ] at hn; omega
      obtain ⟨t, hr, ht⟩ := ih (n/2) hq none (decide (n%2=1)::os)
      refine ⟨t+(n+n/2+3), ?_, by omega⟩
      rw [Function.iterate_add_apply]
      simp only [List.replicate_succ]
      rw [digit_run, hr]
      simp [quotientBits, List.append_assoc]

theorem fractionBits_run (k n : Nat) (hn : n < 2^k) (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg .scan v (List.replicate k true) (List.replicate n true) [] [])) =
        some (cfg .done none [] [] [] (fractionBits k n)) ∧
      t ≤ 3*n+3*k+1 := by
  simpa only [quotientBits_eq_fractionBits k n hn, List.append_nil] using encode_run k n hn v []

/-- The selected threshold precision bounds fixed-width output conversion by
 a polynomial in the retained sampled-input length. -/
theorem threshold_fractionBits_run (q : Polynomial ℕ) (n : Nat) (as bs : List Bool)
    (ha : as.length = ShiQMAConstructiveSchedule.rounds q n)
    (j : Nat) (hj : j < 2^(as.length+1)) (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg .scan v (List.replicate (as.length+1) true)
        (List.replicate j true) [] [])) =
        some (cfg .done none [] [] [] (fractionBits (as.length+1) j)) ∧
      t ≤ 14 * 3^(Nat.log 2 (q.eval 1+1)+q.natDegree+4) *
        ((ShiTMThresholdSamples.input n as bs).length+1)^(2*q.natDegree) := by
  obtain ⟨t, hr, ht⟩ := fractionBits_run (as.length+1) j hj v
  have hlen : as.length+1 < 2^(as.length+1) := Nat.lt_two_pow_self
  have hcap := ShiTMThresholdSamples.capacity_bound q n as bs ha
  refine ⟨t, hr, ?_⟩
  nlinarith

end ShiTMUnaryBinary

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMUnaryBinary.numerator_injective, ``ShiTMUnaryBinary.quotientBits_numerator,
      ``ShiTMUnaryBinary.quotientBits_eq_fractionBits, ``ShiTMUnaryBinary.half_run,
      ``ShiTMUnaryBinary.restore_run, ``ShiTMUnaryBinary.digit_run,
      ``ShiTMUnaryBinary.encode_run, ``ShiTMUnaryBinary.fractionBits_run,
      ``ShiTMUnaryBinary.threshold_fractionBits_run] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected unary-binary axiom {ax} in {name}"
    logInfo m!"UNARY_BINARY_CHECKED {name}; axioms {axioms}"
