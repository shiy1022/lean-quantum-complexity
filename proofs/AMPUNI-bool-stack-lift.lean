import «AMPUNI-unary-binary»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
noncomputable section
open Turing Turing.TM2

/- Stack and control-label embeddings for the Boolean arithmetic routines.
Unmapped controller stacks are preserved throughout a simulated run. -/
namespace ShiTMBoolStackLift
variable {K J L M V : Type}
abbrev Gam (_ : K) := Bool

def store (f : K → J) (S : K → List Bool) (T : J → List Bool) (j : J) : List Bool := by
  classical
  exact if h : ∃ i, f i = j then S (Classical.choose h) else T j

@[simp] theorem store_read (f : K → J) (hf : Function.Injective f)
    (S : K → List Bool) (T : J → List Bool) (i : K) : store f S T (f i) = S i := by
  unfold store
  rw [dif_pos ⟨i, rfl⟩]
  congr 1
  apply hf
  exact Classical.choose_spec (show ∃ k, f k = f i from ⟨i,rfl⟩)

theorem store_frame (f : K → J) (S : K → List Bool) (T : J → List Bool)
    (j : J) (hj : ¬ ∃ i, f i = j) : store f S T j = T j := by
  simp [store, hj]

theorem store_update [DecidableEq K] [DecidableEq J] (f : K → J) (hf : Function.Injective f)
    (S : K → List Bool) (T : J → List Bool) (i : K) (xs : List Bool) :
    Function.update (store f S T) (f i) xs = store f (Function.update S i xs) T := by
  funext j
  by_cases hj : ∃ k, f k = j
  · obtain ⟨k,rfl⟩ := hj
    by_cases hk : k=i
    · subst k; simp [store_read, hf]
    · have hki : f k ≠ f i := fun h => hk (hf h)
      simp [Function.update_of_ne, hk, hki, store_read, hf]
  · have hji : j ≠ f i := by intro h; apply hj; exact ⟨i,h.symm⟩
    simp [Function.update_of_ne, hji, store_frame, hj]

/-- Identify an embedded store using its component values and its preserved frame. -/
theorem store_eq (f : K → J) (hf : Function.Injective f)
    (S : K → List Bool) (T U : J → List Bool)
    (hpart : ∀ i, U (f i) = S i)
    (hframe : ∀ j, (¬ ∃ i, f i = j) → U j = T j) : store f S T = U := by
  funext j
  by_cases hj : ∃ i, f i=j
  · obtain ⟨i,rfl⟩ := hj
    rw [store_read f hf, hpart]
  · rw [store_frame f S T j hj, hframe j hj]

def stmt (f : K → J) (g : Option L → M) :
    Stmt (Gam (K := K)) L V → Stmt (Gam (K := J)) M V
  | .push k a q => .push (f k) a (stmt f g q)
  | .peek k a q => .peek (f k) a (stmt f g q)
  | .pop k a q => .pop (f k) a (stmt f g q)
  | .load a q => .load a (stmt f g q)
  | .branch a q r => .branch a (stmt f g q) (stmt f g r)
  | .goto a => .goto (fun v => g (some (a v)))
  | .halt => .goto (fun _ => g none)

def cfg (f : K → J) (g : Option L → M) (T : J → List Bool)
    (c : Cfg (Gam (K := K)) L V) : Cfg (Gam (K := J)) M V :=
  ⟨some (g c.l), c.var, store f c.stk T⟩

variable [DecidableEq K] [DecidableEq J]

theorem stepAux_lift (f : K → J) (hf : Function.Injective f) (g : Option L → M)
    (q : Stmt (Gam (K := K)) L V) (v : V) (S : K → List Bool) (T : J → List Bool) :
    stepAux (stmt f g q) v (store f S T) = cfg f g T (stepAux q v S) := by
  induction q generalizing v S with
  | push k a q ih =>
      simpa only [stmt, stepAux, store_read f hf, store_update f hf] using
        ih v (Function.update S k (a v :: S k))
  | peek k a q ih =>
      simpa only [stmt, stepAux, store_read f hf] using ih (a v (S k).head?) S
  | pop k a q ih =>
      simpa only [stmt, stepAux, store_read f hf, store_update f hf] using
        ih (a v (S k).head?) (Function.update S k (S k).tail)
  | load a q ih => exact ih _ _
  | branch a q r iq ir => cases h : a v <;> simp [stmt, stepAux, h, iq, ir]
  | goto a => rfl
  | halt => rfl

/-- Simulate an exact run under an injective stack assignment. A source halt
jumps to g none, allowing controllers to connect routines without another axiom. -/
theorem simulate (f : K → J) (hf : Function.Injective f) (g : Option L → M)
    (small : L → Stmt (Gam (K := K)) L V)
    (big : M → Stmt (Gam (K := J)) M V)
    (hbody : ∀ l, big (g (some l)) = stmt f g (small l))
    (T : J → List Bool) (n : Nat) (c d : Cfg (Gam (K := K)) L V)
    (hr : (ShiTMSubroutine.run small)^[n] (some c) = some d) :
    (ShiTMSubroutine.run big)^[n] (some (cfg f g T c)) = some (cfg f g T d) := by
  apply ShiTMJoint.simulate small big (cfg f g T) ?_ n c d hr
  intro l v S
  simp only [ShiTMSubroutine.run, Option.bind_some, cfg, step, hbody]
  exact congrArg some (stepAux_lift f hf g (small l) v S T)

end ShiTMBoolStackLift


/- Shared workspace connecting subtraction to fixed-width output. -/
namespace ShiTMCenteringOutputCore
inductive Stack where
  | capacity | first | second | count | scratch | output
  deriving DecidableEq
inductive Label where
  | subtract (l : ShiTMCenteringInteger.Label)
  | encode (l : ShiTMUnaryBinary.Label)
  | done
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList
  [.capacity, .first, .second, .count, .scratch, .output]
  (by intro j; cases j <;> simp)
instance : Fintype Label := Fintype.ofList
  ((List.map Label.subtract (Finset.toList (Finset.univ : Finset ShiTMCenteringInteger.Label))) ++
    (List.map Label.encode (Finset.toList (Finset.univ : Finset ShiTMUnaryBinary.Label))) ++ [Label.done])
  (by intro l; cases l <;> simp)
abbrev Gam (_ : Stack) := Bool
abbrev State := Option Bool

def subStack : ShiTMCenteringInteger.Stack → Stack
  | .capacity => .capacity
  | .first => .first
  | .second => .second

def outStack : ShiTMUnaryBinary.Stack → Stack
  | .count => .count
  | .value => .capacity
  | .scratch => .scratch
  | .output => .output

theorem subStack_injective : Function.Injective subStack := by
  intro i j h; cases i <;> cases j <;> simp_all [subStack]
theorem outStack_injective : Function.Injective outStack := by
  intro i j h; cases i <;> cases j <;> simp_all [outStack]


def subLabel : Option ShiTMCenteringInteger.Label → Label
  | some l => .subtract l
  | none => .encode .scan

def outLabel : Option ShiTMUnaryBinary.Label → Label
  | some l => .encode l
  | none => .done

def machine : Label → Stmt Gam Label State
  | .subtract l => ShiTMBoolStackLift.stmt subStack subLabel (ShiTMCenteringInteger.machine l)
  | .encode l => ShiTMBoolStackLift.stmt outStack outLabel (ShiTMUnaryBinary.machine l)
  | .done => .halt
abbrev run := ShiTMSubroutine.run machine

def store (c a b k : Nat) (os : List Bool) : Stack → List Bool
  | .capacity => List.replicate c true
  | .first => List.replicate a true
  | .second => List.replicate b true
  | .count => List.replicate k true
  | .scratch => []
  | .output => os

def cfg (l : Label) (v : State) (c a b k : Nat) (os : List Bool) : Cfg Gam Label State :=
  ⟨some l, v, store c a b k os⟩


theorem sub_store (c a b c' a' b' k : Nat) (os : List Bool) :
    ShiTMBoolStackLift.store subStack
      (ShiTMCenteringInteger.storeFn (List.replicate c' true)
        (List.replicate a' true) (List.replicate b' true)) (store c a b k os) =
      store c' a' b' k os := by
  apply ShiTMBoolStackLift.store_eq subStack subStack_injective
  · intro i; cases i <;> rfl
  · intro j hj
    cases j with
    | capacity => exact False.elim (hj ⟨.capacity,rfl⟩)
    | first => exact False.elim (hj ⟨.first,rfl⟩)
    | second => exact False.elim (hj ⟨.second,rfl⟩)
    | count => rfl
    | scratch => rfl
    | output => rfl


theorem out_store (c a b k c' k' : Nat) (os os' : List Bool) :
    ShiTMBoolStackLift.store outStack
      (ShiTMUnaryBinary.storeFn (List.replicate k' true) (List.replicate c' true) [] os')
      (store c a b k os) = store c' a b k' os' := by
  apply ShiTMBoolStackLift.store_eq outStack outStack_injective
  · intro i; cases i <;> rfl
  · intro j hj
    cases j with
    | capacity => exact False.elim (hj ⟨.value,rfl⟩)
    | first => rfl
    | second => rfl
    | count => exact False.elim (hj ⟨.count,rfl⟩)
    | scratch => rfl
    | output => exact False.elim (hj ⟨.output,rfl⟩)


theorem subtraction_run (c a b k : Nat) (v : State) (os : List Bool) :
    run^[a+b+2] (some (cfg (.subtract .first) v c a b k os)) =
      some (cfg (.subtract .done) none (c-(a+b)) 0 0 k os) := by
  have h := ShiTMBoolStackLift.simulate subStack subStack_injective subLabel
    ShiTMCenteringInteger.machine machine (fun _ => rfl) (store c a b k os)
    (a+b+2) _ _ (ShiTMCenteringInteger.subtract_run c a b v)
  have hs0 := sub_store c a b (c-(a+b)) 0 0 k os
  simp only [List.replicate_zero] at hs0
  simpa only [run, ShiTMBoolStackLift.cfg, ShiTMCenteringInteger.cfg, subLabel,
    hs0, sub_store, cfg] using h

theorem output_run (k j : Nat) (hj : j < 2^k) (v : State) (os : List Bool) :
    ∃ t : Nat,
      run^[t] (some (cfg (.encode .scan) v j 0 0 k os)) =
        some (cfg (.encode .done) none 0 0 0 0 (ShiQMACenteredGap.fractionBits k j ++ os)) ∧
      t ≤ 3*j+3*k+1 := by
  obtain ⟨t, hr, ht⟩ := ShiTMUnaryBinary.encode_run k j hj v os
  have h := ShiTMBoolStackLift.simulate outStack outStack_injective outLabel
    ShiTMUnaryBinary.machine machine (fun _ => rfl) (store j 0 0 k os) t _ _ hr
  have hs0 := out_store j 0 0 k 0 0 os (ShiQMACenteredGap.fractionBits k j ++ os)
  simp only [List.replicate_zero] at hs0
  refine ⟨t, ?_, ht⟩
  simpa only [run, ShiTMBoolStackLift.cfg, ShiTMUnaryBinary.cfg, outLabel,
    hs0, out_store, cfg,
    ShiTMUnaryBinary.quotientBits_eq_fractionBits k j hj] using h

theorem subtraction_handoff (c k : Nat) (os : List Bool) :
    run (some (cfg (.subtract .done) none c 0 0 k os)) =
      some (cfg (.encode .scan) none c 0 0 k os) := rfl

theorem output_handoff (os : List Bool) :
    run (some (cfg (.encode .done) none 0 0 0 0 os)) =
      some (cfg .done none 0 0 0 0 os) := rfl

/-- One finite controller subtracts both operands, enters the encoder, and
leaves only the requested fraction bits on the output stack. -/
theorem difference_run (c a b k : Nat) (hj : c-(a+b) < 2^k) (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg (.subtract .first) v c a b k [])) =
        some (cfg .done none 0 0 0 0 (ShiQMACenteredGap.fractionBits k (c-(a+b)))) ∧
      t ≤ a+b+3*(c-(a+b))+3*k+5 := by
  obtain ⟨te, he, ht⟩ := output_run k (c-(a+b)) hj none []
  simp only [List.append_nil] at he
  have hs : run^[a+b+2+1] (some (cfg (.subtract .first) v c a b k [])) =
      some (cfg (.encode .scan) none (c-(a+b)) 0 0 k []) := by
    rw [Function.iterate_succ_apply', subtraction_run, subtraction_handoff]
  have ho : run^[te+1] (some (cfg (.encode .scan) none (c-(a+b)) 0 0 k [])) =
      some (cfg .done none 0 0 0 0 (ShiQMACenteredGap.fractionBits k (c-(a+b)))) := by
    rw [Function.iterate_succ_apply', he, output_handoff]
  refine ⟨(te+1)+(a+b+2+1), ?_, by omega⟩
  rw [Function.iterate_add_apply, hs, ho]

theorem centering_run (k a b : Nat)
    (hj : ShiQMACenteredGap.centeringNumerator k a b < 2^(k+1)) (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg (.subtract .first) v (2^(k+1)) a b (k+1) [])) =
        some (cfg .done none 0 0 0 0
          (ShiQMACenteredGap.fractionBits (k+1) (ShiQMACenteredGap.centeringNumerator k a b))) ∧
      t ≤ a+b+3*(ShiQMACenteredGap.centeringNumerator k a b)+3*(k+1)+5 :=
  difference_run (2^(k+1)) a b (k+1) hj v

/-- The connected subtraction/output controller has a single polynomial bound
in the actual sampled-input length. -/
theorem threshold_run (q : Polynomial ℕ) (n : Nat) (as bs : List Bool)
    (ha : as.length = ShiQMAConstructiveSchedule.rounds q n) (hb : bs.length = as.length)
    (hj : ShiQMACenteredGap.centeringNumerator as.length
      (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs) < 2^(as.length+1))
    (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg (.subtract .first) v (2^(as.length+1))
        (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs)
        (as.length+1) [])) =
        some (cfg .done none 0 0 0 0 (ShiQMACenteredGap.fractionBits (as.length+1)
          (ShiQMACenteredGap.centeringNumerator as.length
            (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs)))) ∧
      t ≤ 24 * 3^(Nat.log 2 (q.eval 1+1)+q.natDegree+4) *
        ((ShiTMThresholdSamples.input n as bs).length+1)^(2*q.natDegree) := by
  obtain ⟨t, hr, ht⟩ := centering_run as.length
    (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs) hj v
  have hsub := ShiTMCenteringInteger.subtraction_cost as bs hb.symm
  have hlen : as.length+1 < 2^(as.length+1) := Nat.lt_two_pow_self
  have hcap := ShiTMThresholdSamples.capacity_bound q n as bs ha
  refine ⟨t, hr, ?_⟩
  nlinarith

end ShiTMCenteringOutputCore

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMBoolStackLift.store_read, ``ShiTMBoolStackLift.store_frame,
      ``ShiTMBoolStackLift.store_update, ``ShiTMBoolStackLift.store_eq,
      ``ShiTMBoolStackLift.stepAux_lift, ``ShiTMBoolStackLift.simulate,
      ``ShiTMCenteringOutputCore.subtraction_run, ``ShiTMCenteringOutputCore.output_run,
      ``ShiTMCenteringOutputCore.difference_run, ``ShiTMCenteringOutputCore.centering_run,
      ``ShiTMCenteringOutputCore.threshold_run] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected bool-stack-lift axiom {ax} in {name}"
    logInfo m!"BOOL_STACK_LIFT_CHECKED {name}; axioms {axioms}"
