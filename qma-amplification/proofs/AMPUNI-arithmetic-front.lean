import «AMPUNI-bool-stack-lift»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
noncomputable section
open Turing Turing.TM2
namespace ShiTMArithmeticFront

inductive Extra where
  | input | firstCount | secondCount | powerBits | powerCount
  deriving DecidableEq
instance : Fintype Extra := Fintype.ofList
  [.input, .firstCount, .secondCount, .powerBits, .powerCount]
  (by intro e; cases e <;> simp)
abbrev Stack := Extra ⊕ ShiTMCenteringOutputCore.Stack
abbrev Gam (_ : Stack) := Bool
abbrev State := Option Bool
inductive Label where
  | first (l : ShiTMBinaryUnary.Label)
  | second (l : ShiTMBinaryUnary.Label)
  | power (l : ShiTMBinaryUnary.Label)
  | core (l : ShiTMCenteringOutputCore.Label)
  | skipN | readK | done
  deriving DecidableEq
instance : Fintype Label := Fintype.ofList
  (List.map Label.first (Finset.toList (Finset.univ : Finset ShiTMBinaryUnary.Label)) ++
   List.map Label.second (Finset.toList (Finset.univ : Finset ShiTMBinaryUnary.Label)) ++
   List.map Label.power (Finset.toList (Finset.univ : Finset ShiTMBinaryUnary.Label)) ++
   List.map Label.core (Finset.toList (Finset.univ : Finset ShiTMCenteringOutputCore.Label)) ++ [Label.skipN, Label.readK, Label.done])
  (by intro l; cases l <;> simp)

def firstStack : ShiTMBinaryUnary.Stack → Stack
  | .bits => .inl .input
  | .count => .inl .firstCount
  | .value => .inr .first
  | .scratch => .inr .scratch

theorem firstStack_injective : Function.Injective firstStack := by
  intro i j h; cases i <;> cases j <;> simp_all [firstStack]

def secondStack : ShiTMBinaryUnary.Stack → Stack
  | .bits => .inl .input
  | .count => .inl .secondCount
  | .value => .inr .second
  | .scratch => .inr .scratch

theorem secondStack_injective : Function.Injective secondStack := by
  intro i j h; cases i <;> cases j <;> simp_all [secondStack]

def powerStack : ShiTMBinaryUnary.Stack → Stack
  | .bits => .inl .powerBits
  | .count => .inl .powerCount
  | .value => .inr .capacity
  | .scratch => .inr .scratch

theorem powerStack_injective : Function.Injective powerStack := by
  intro i j h; cases i <;> cases j <;> simp_all [powerStack]

def coreStack : ShiTMCenteringOutputCore.Stack → Stack := Sum.inr
theorem coreStack_injective : Function.Injective coreStack := Sum.inr_injective

def firstLabel : Option ShiTMBinaryUnary.Label → Label
  | some l => .first l
  | none => .second .scan
def secondLabel : Option ShiTMBinaryUnary.Label → Label
  | some l => .second l
  | none => .power .scan
def powerLabel : Option ShiTMBinaryUnary.Label → Label
  | some l => .power l
  | none => .core (.subtract .first)
def coreLabel : Option ShiTMCenteringOutputCore.Label → Label
  | some l => .core l
  | none => .done

def machine : Label → Stmt Gam Label State
  | .first l => ShiTMBoolStackLift.stmt firstStack firstLabel (ShiTMBinaryUnary.machine l)
  | .second l => ShiTMBoolStackLift.stmt secondStack secondLabel (ShiTMBinaryUnary.machine l)
  | .power l => ShiTMBoolStackLift.stmt powerStack powerLabel (ShiTMBinaryUnary.machine l)
  | .core l => ShiTMBoolStackLift.stmt coreStack coreLabel (ShiTMCenteringOutputCore.machine l)
  | .skipN => .pop (.inl .input) (fun _ x => x)
      (.branch (fun v => v.getD false) (.goto (fun _ => .skipN)) (.goto (fun _ => .readK)))
  | .readK => .pop (.inl .input) (fun _ x => x)
      (.branch (fun v => v.getD false)
        (.push (.inl .firstCount) (fun _ => true)
          (.push (.inl .secondCount) (fun _ => true)
            (.push (.inl .powerCount) (fun _ => true)
              (.push (.inl .powerBits) (fun _ => false)
                (.push (.inr .count) (fun _ => true) (.goto (fun _ => .readK)))))))
        (.push (.inl .powerCount) (fun _ => true)
          (.push (.inl .powerBits) (fun _ => false)
            (.push (.inr .count) (fun _ => true)
              (.push (.inr .capacity) (fun _ => true)
                (.load (fun _ => none) (.goto (fun _ => .first .scan))))))))
  | .done => .halt
abbrev run := ShiTMSubroutine.run machine

def store (xs : List Bool) (ca cb : Nat) (zs : List Bool) (cp c a b k : Nat)
    (os : List Bool) : Stack → List Bool
  | .inl .input => xs
  | .inl .firstCount => List.replicate ca true
  | .inl .secondCount => List.replicate cb true
  | .inl .powerBits => zs
  | .inl .powerCount => List.replicate cp true
  | .inr j => ShiTMCenteringOutputCore.store c a b k os j

def cfg (l : Label) (v : State) (xs : List Bool) (ca cb : Nat) (zs : List Bool)
    (cp c a b k : Nat) (os : List Bool) : Cfg Gam Label State :=
  ⟨some l,v,store xs ca cb zs cp c a b k os⟩

@[simp] theorem update_input (xs : List Bool) (ca cb : Nat) (zs : List Bool)
    (cp c a b k : Nat) (os : List Bool) (xs' : List Bool) :
    Function.update (store xs ca cb zs cp c a b k os) (.inl .input) (xs') =
      store (xs') ca cb zs cp c a b k os := by
  funext j
  rcases j with e | j
  · cases e <;> simp [store]
  · cases j <;> simp [store, ShiTMCenteringOutputCore.store]

@[simp] theorem update_firstCount (xs : List Bool) (ca cb : Nat) (zs : List Bool)
    (cp c a b k : Nat) (os : List Bool)  :
    Function.update (store xs ca cb zs cp c a b k os) (.inl .firstCount) (true :: List.replicate ca true) =
      store xs (ca+1) cb zs cp c a b k os := by
  funext j
  rcases j with e | j
  · cases e <;> simp [store, List.replicate_succ]
  · cases j <;> simp [store, ShiTMCenteringOutputCore.store]

@[simp] theorem update_secondCount (xs : List Bool) (ca cb : Nat) (zs : List Bool)
    (cp c a b k : Nat) (os : List Bool)  :
    Function.update (store xs ca cb zs cp c a b k os) (.inl .secondCount) (true :: List.replicate cb true) =
      store xs ca (cb+1) zs cp c a b k os := by
  funext j
  rcases j with e | j
  · cases e <;> simp [store, List.replicate_succ]
  · cases j <;> simp [store, ShiTMCenteringOutputCore.store]

@[simp] theorem update_powerBits (xs : List Bool) (ca cb : Nat) (zs : List Bool)
    (cp c a b k : Nat) (os : List Bool)  :
    Function.update (store xs ca cb zs cp c a b k os) (.inl .powerBits) (false::zs) =
      store xs ca cb (false::zs) cp c a b k os := by
  funext j
  rcases j with e | j
  · cases e <;> simp [store]
  · cases j <;> simp [store, ShiTMCenteringOutputCore.store]

@[simp] theorem update_powerCount (xs : List Bool) (ca cb : Nat) (zs : List Bool)
    (cp c a b k : Nat) (os : List Bool)  :
    Function.update (store xs ca cb zs cp c a b k os) (.inl .powerCount) (true :: List.replicate cp true) =
      store xs ca cb zs (cp+1) c a b k os := by
  funext j
  rcases j with e | j
  · cases e <;> simp [store, List.replicate_succ]
  · cases j <;> simp [store, ShiTMCenteringOutputCore.store]

@[simp] theorem update_count (xs : List Bool) (ca cb : Nat) (zs : List Bool)
    (cp c a b k : Nat) (os : List Bool)  :
    Function.update (store xs ca cb zs cp c a b k os) (.inr .count) (true :: List.replicate k true) =
      store xs ca cb zs cp c a b (k+1) os := by
  funext j
  rcases j with e | j
  · cases e <;> simp [store]
  · cases j <;> simp [store, ShiTMCenteringOutputCore.store, List.replicate_succ]

@[simp] theorem update_capacity (xs : List Bool) (ca cb : Nat) (zs : List Bool)
    (cp c a b k : Nat) (os : List Bool)  :
    Function.update (store xs ca cb zs cp c a b k os) (.inr .capacity) (true :: List.replicate c true) =
      store xs ca cb zs cp (c+1) a b k os := by
  funext j
  rcases j with e | j
  · cases e <;> simp [store]
  · cases j <;> simp [store, ShiTMCenteringOutputCore.store, List.replicate_succ]

theorem first_store (xs : List Bool) (ca cb : Nat) (zs : List Bool) (cp c a b k : Nat) (os : List Bool)
    (xs' : List Bool) (ca' a' : Nat) :
    ShiTMBoolStackLift.store firstStack
      (ShiTMBinaryUnary.storeFn xs' (List.replicate ca' true) (List.replicate a' true) [])
      (store xs ca cb zs cp c a b k os) = store xs' ca' cb zs cp c a' b k os := by
  apply ShiTMBoolStackLift.store_eq firstStack firstStack_injective
  · intro i; cases i <;> rfl
  · intro j hj
    cases j with
    | inl e =>
        cases e with
        | input => exact False.elim (hj ⟨.bits,rfl⟩)
        | firstCount => exact False.elim (hj ⟨.count,rfl⟩)
        | secondCount => rfl
        | powerBits => rfl
        | powerCount => rfl
    | inr j =>
        cases j with
        | capacity => rfl
        | first => exact False.elim (hj ⟨.value,rfl⟩)
        | second => rfl
        | count => rfl
        | scratch => rfl
        | output => rfl

theorem second_store (xs : List Bool) (ca cb : Nat) (zs : List Bool) (cp c a b k : Nat) (os : List Bool)
    (xs' : List Bool) (cb' b' : Nat) :
    ShiTMBoolStackLift.store secondStack
      (ShiTMBinaryUnary.storeFn xs' (List.replicate cb' true) (List.replicate b' true) [])
      (store xs ca cb zs cp c a b k os) = store xs' ca cb' zs cp c a b' k os := by
  apply ShiTMBoolStackLift.store_eq secondStack secondStack_injective
  · intro i; cases i <;> rfl
  · intro j hj
    cases j with
    | inl e =>
        cases e with
        | input => exact False.elim (hj ⟨.bits,rfl⟩)
        | firstCount => rfl
        | secondCount => exact False.elim (hj ⟨.count,rfl⟩)
        | powerBits => rfl
        | powerCount => rfl
    | inr j =>
        cases j with
        | capacity => rfl
        | first => rfl
        | second => exact False.elim (hj ⟨.value,rfl⟩)
        | count => rfl
        | scratch => rfl
        | output => rfl

theorem power_store (xs : List Bool) (ca cb : Nat) (zs : List Bool) (cp c a b k : Nat) (os : List Bool)
    (zs' : List Bool) (cp' c' : Nat) :
    ShiTMBoolStackLift.store powerStack
      (ShiTMBinaryUnary.storeFn zs' (List.replicate cp' true) (List.replicate c' true) [])
      (store xs ca cb zs cp c a b k os) = store xs ca cb zs' cp' c' a b k os := by
  apply ShiTMBoolStackLift.store_eq powerStack powerStack_injective
  · intro i; cases i <;> rfl
  · intro j hj
    cases j with
    | inl e =>
        cases e with
        | input => rfl
        | firstCount => rfl
        | secondCount => rfl
        | powerBits => exact False.elim (hj ⟨.bits,rfl⟩)
        | powerCount => exact False.elim (hj ⟨.count,rfl⟩)
    | inr j =>
        cases j with
        | capacity => exact False.elim (hj ⟨.value,rfl⟩)
        | first => rfl
        | second => rfl
        | count => rfl
        | scratch => rfl
        | output => rfl

theorem core_store (xs : List Bool) (ca cb : Nat) (zs : List Bool) (cp c a b k : Nat)
    (os : List Bool) (c' a' b' k' : Nat) (os' : List Bool) :
    ShiTMBoolStackLift.store coreStack (ShiTMCenteringOutputCore.store c' a' b' k' os')
      (store xs ca cb zs cp c a b k os) = store xs ca cb zs cp c' a' b' k' os' := by
  apply ShiTMBoolStackLift.store_eq coreStack coreStack_injective
  · intro i; rfl
  · intro j hj
    cases j with
    | inl e => cases e <;> rfl
    | inr i => exact False.elim (hj ⟨i,rfl⟩)

/-- Decode the first counted numerator and hand control to the second decoder. -/
theorem first_run (as rest zs : List Bool) (cb cp c b k : Nat) (os : List Bool) (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg (.first .scan) v (as++rest) as.length cb zs cp c 0 b k os)) =
        some (cfg (.second .scan) none rest 0 cb zs cp c
          (ShiQMACenteredGap.binaryNumerator as) b k os) ∧
      t ≤ 3*2^as.length+4*as.length+2 := by
  obtain ⟨t, hr, ht⟩ := ShiTMBinaryUnary.numerator_run as rest v
  have h := ShiTMBoolStackLift.simulate firstStack firstStack_injective firstLabel
    ShiTMBinaryUnary.machine machine (fun _ => rfl)
    (store (as++rest) as.length cb zs cp c 0 b k os) t _ _ hr
  have hi := first_store (as++rest) as.length cb zs cp c 0 b k os (as++rest) as.length 0
  have he := first_store (as++rest) as.length cb zs cp c 0 b k os rest 0
    (ShiQMACenteredGap.binaryNumerator as)
  simp only [List.replicate_zero] at hi he
  have hh : run^[t] (some (cfg (.first .scan) v (as++rest) as.length cb zs cp c 0 b k os)) =
      some (cfg (.first .done) none rest 0 cb zs cp c (ShiQMACenteredGap.binaryNumerator as) b k os) := by
    simpa only [run, ShiTMBoolStackLift.cfg, ShiTMBinaryUnary.cfg, firstLabel, hi, he, cfg] using h
  refine ⟨t+1, ?_, by omega⟩
  rw [Function.iterate_succ_apply', hh]
  rfl

theorem second_run (bs rest zs : List Bool) (ca cp c a k : Nat) (os : List Bool) (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg (.second .scan) v (bs++rest) ca bs.length zs cp c a 0 k os)) =
        some (cfg (.power .scan) none rest ca 0 zs cp c a
          (ShiQMACenteredGap.binaryNumerator bs) k os) ∧
      t ≤ 3*2^bs.length+4*bs.length+2 := by
  obtain ⟨t, hr, ht⟩ := ShiTMBinaryUnary.numerator_run bs rest v
  have h := ShiTMBoolStackLift.simulate secondStack secondStack_injective secondLabel
    ShiTMBinaryUnary.machine machine (fun _ => rfl)
    (store (bs++rest) ca bs.length zs cp c a 0 k os) t _ _ hr
  have hi := second_store (bs++rest) ca bs.length zs cp c a 0 k os (bs++rest) bs.length 0
  have he := second_store (bs++rest) ca bs.length zs cp c a 0 k os rest 0
    (ShiQMACenteredGap.binaryNumerator bs)
  simp only [List.replicate_zero] at hi he
  have hh : run^[t] (some (cfg (.second .scan) v (bs++rest) ca bs.length zs cp c a 0 k os)) =
      some (cfg (.second .done) none rest ca 0 zs cp c a (ShiQMACenteredGap.binaryNumerator bs) k os) := by
    simpa only [run, ShiTMBoolStackLift.cfg, ShiTMBinaryUnary.cfg, secondLabel, hi, he, cfg] using h
  refine ⟨t+1, ?_, by omega⟩
  rw [Function.iterate_succ_apply', hh]
  rfl

theorem power_run (w : Nat) (xs : List Bool) (ca cb a b k : Nat) (os : List Bool) (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg (.power .scan) v xs ca cb (List.replicate w false) w 1 a b k os)) =
        some (cfg (.core (.subtract .first)) none xs ca cb [] 0 (2^w) a b k os) ∧
      t ≤ 3*2^w+4*w+2 := by
  obtain ⟨t, hr, ht⟩ := ShiTMBinaryUnary.capacity_run w [] v
  simp only [List.append_nil] at hr
  have h := ShiTMBoolStackLift.simulate powerStack powerStack_injective powerLabel
    ShiTMBinaryUnary.machine machine (fun _ => rfl)
    (store xs ca cb (List.replicate w false) w 1 a b k os) t _ _ hr
  have hi := power_store xs ca cb (List.replicate w false) w 1 a b k os (List.replicate w false) w 1
  have he := power_store xs ca cb (List.replicate w false) w 1 a b k os [] 0 (2^w)
  simp only [List.replicate_zero, List.replicate_succ] at hi he
  have hh : run^[t] (some (cfg (.power .scan) v xs ca cb (List.replicate w false) w 1 a b k os)) =
      some (cfg (.power .done) none xs ca cb [] 0 (2^w) a b k os) := by
    simpa only [run, ShiTMBoolStackLift.cfg, ShiTMBinaryUnary.cfg, powerLabel, hi, he, cfg] using h
  refine ⟨t+1, ?_, by omega⟩
  rw [Function.iterate_succ_apply', hh]
  rfl

theorem core_run (w c a b : Nat) (hj : c-(a+b) < 2^w) (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg (.core (.subtract .first)) v [] 0 0 [] 0 c a b w [])) =
        some (cfg .done none [] 0 0 [] 0 0 0 0 0
          (ShiQMACenteredGap.fractionBits w (c-(a+b)))) ∧
      t ≤ a+b+3*(c-(a+b))+3*w+6 := by
  obtain ⟨t, hr, ht⟩ := ShiTMCenteringOutputCore.difference_run c a b w hj v
  have h := ShiTMBoolStackLift.simulate coreStack coreStack_injective coreLabel
    ShiTMCenteringOutputCore.machine machine (fun _ => rfl) (store [] 0 0 [] 0 c a b w []) t _ _ hr
  have hh : run^[t] (some (cfg (.core (.subtract .first)) v [] 0 0 [] 0 c a b w [])) =
      some (cfg (.core .done) none [] 0 0 [] 0 0 0 0 0
        (ShiQMACenteredGap.fractionBits w (c-(a+b)))) := by
    simpa only [run, ShiTMBoolStackLift.cfg, ShiTMCenteringOutputCore.cfg, coreLabel, core_store, cfg] using h
  refine ⟨t+1, ?_, by omega⟩
  rw [Function.iterate_succ_apply', hh]
  rfl

/-- Full arithmetic from prepared sampled bits: both decoders, capacity
construction, subtraction, fixed-width output, and all four handoffs. -/
theorem prepared_run (as bs : List Bool) (hb : bs.length = as.length)
    (hj : ShiQMACenteredGap.centeringNumerator as.length
      (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs) < 2^(as.length+1))
    (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg (.first .scan) v (as++bs) as.length as.length
        (List.replicate (as.length+1) false) (as.length+1) 1 0 0 (as.length+1) [])) =
        some (cfg .done none [] 0 0 [] 0 0 0 0 0
          (ShiQMACenteredGap.fractionBits (as.length+1)
            (ShiQMACenteredGap.centeringNumerator as.length
              (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs)))) ∧
      t ≤ 32*2^(as.length+1) := by
  obtain ⟨t1,h1,ht1⟩ := first_run as bs (List.replicate (as.length+1) false)
    as.length (as.length+1) 1 0 (as.length+1) [] v
  obtain ⟨t2,h2,ht2⟩ := second_run bs [] (List.replicate (as.length+1) false)
    0 (as.length+1) 1 (ShiQMACenteredGap.binaryNumerator as) (as.length+1) [] none
  simp only [List.append_nil, hb] at h2 ht2
  obtain ⟨tp,hp,htp⟩ := power_run (as.length+1) [] 0 0
    (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs) (as.length+1) [] none
  obtain ⟨tc,hc,htc⟩ := core_run (as.length+1) (2^(as.length+1))
    (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs) hj none
  refine ⟨tc+(tp+(t2+t1)), ?_, ?_⟩
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
      h1, h2, hp, hc]
    rfl
  · have hsum := ShiTMCenteringInteger.subtraction_cost as bs hb.symm
    have hlen : as.length+1 < 2^(as.length+1) := Nat.lt_two_pow_self
    have hpow : 2^(as.length+1) = 2*2^as.length := by rw [pow_succ]; omega
    dsimp only [ShiQMACenteredGap.centeringNumerator] at hj
    nlinarith

theorem threshold_prepared_run (q : Polynomial ℕ) (n : Nat) (as bs : List Bool)
    (ha : as.length = ShiQMAConstructiveSchedule.rounds q n) (hb : bs.length = as.length)
    (hj : ShiQMACenteredGap.centeringNumerator as.length
      (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs) < 2^(as.length+1))
    (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg (.first .scan) v (as++bs) as.length as.length
        (List.replicate (as.length+1) false) (as.length+1) 1 0 0 (as.length+1) [])) =
        some (cfg .done none [] 0 0 [] 0 0 0 0 0
          (ShiQMACenteredGap.fractionBits (as.length+1)
            (ShiQMACenteredGap.centeringNumerator as.length
              (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs)))) ∧
      t ≤ 64 * 3^(Nat.log 2 (q.eval 1+1)+q.natDegree+4) *
        ((ShiTMThresholdSamples.input n as bs).length+1)^(2*q.natDegree) := by
  obtain ⟨t,hr,ht⟩ := prepared_run as bs hb hj v
  have hcap := ShiTMThresholdSamples.capacity_bound q n as bs ha
  exact ⟨t,hr,by nlinarith⟩

theorem skip_step (n : Nat) (rest : List Bool) (v : State) :
    run (some (cfg .skipN v (true::(List.replicate n true ++ false::rest)) 0 0 [] 0 0 0 0 0 [])) =
      some (cfg .skipN (some true) (List.replicate n true ++ false::rest) 0 0 [] 0 0 0 0 0 []) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, store]

theorem skip_run (n : Nat) (rest : List Bool) (v : State) :
    run^[n+1] (some (cfg .skipN v (List.replicate n true ++ false::rest) 0 0 [] 0 0 0 0 0 [])) =
      some (cfg .readK (some false) rest 0 0 [] 0 0 0 0 0 []) := by
  induction n generalizing v with
  | zero => simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, store]
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp only [List.replicate_succ, List.cons_append]
      rw [skip_step, ih]

theorem precision_step (m : Nat) (rest : List Bool) (v : State) :
    run (some (cfg .readK v (true::rest) m m (List.replicate m false) m 0 0 0 m [])) =
      some (cfg .readK (some true) rest (m+1) (m+1) (List.replicate (m+1) false)
        (m+1) 0 0 0 (m+1) []) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, store,
    ShiTMCenteringOutputCore.store, List.replicate_succ]

theorem precision_end (m : Nat) (rest : List Bool) (v : State) :
    run (some (cfg .readK v (false::rest) m m (List.replicate m false) m 0 0 0 m [])) =
      some (cfg (.first .scan) none rest m m (List.replicate (m+1) false)
        (m+1) 1 0 0 (m+1) []) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux, store,
    ShiTMCenteringOutputCore.store, List.replicate_succ]

  simpa only [List.replicate_zero] using
    update_capacity rest m m (false :: List.replicate m false) (m+1) 0 0 0 (m+1) []

theorem precision_run (k m : Nat) (rest : List Bool) (v : State) :
    run^[k+1] (some (cfg .readK v (List.replicate k true ++ false::rest)
      m m (List.replicate m false) m 0 0 0 m [])) =
      some (cfg (.first .scan) none rest (k+m) (k+m) (List.replicate (k+m+1) false)
        (k+m+1) 1 0 0 (k+m+1) []) := by
  induction k generalizing m v with
  | zero => simpa using precision_end m rest v
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      rw [List.replicate_succ, List.cons_append]
      rw [precision_step, ih, show k+(m+1) = (k+1)+m by omega]

/-- Parse both headers and prepare every arithmetic counter in linear time. -/
theorem parser_run (n k : Nat) (rest : List Bool) (v : State) :
    run^[n+k+2] (some (cfg .skipN v (ShiBQP.encNat n ++ ShiBQP.encNat k ++ rest)
      0 0 [] 0 0 0 0 0 [])) =
      some (cfg (.first .scan) none rest k k (List.replicate (k+1) false)
        (k+1) 1 0 0 (k+1) []) := by
  rw [show n+k+2 = (k+1)+(n+1) by omega, Function.iterate_add_apply]
  simp only [ShiBQP.encNat, List.append_assoc, List.cons_append]
  rw [skip_run]
  simpa using precision_run k 0 rest (some false)

/-- Raw sampled input through the complete arithmetic controller. -/
theorem sampled_run (n : Nat) (as bs : List Bool) (hb : bs.length = as.length)
    (hj : ShiQMACenteredGap.centeringNumerator as.length
      (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs) < 2^(as.length+1))
    (v : State) :
    ∃ t : Nat,
      run^[t] (some (cfg .skipN v (ShiTMThresholdSamples.input n as bs) 0 0 [] 0 0 0 0 0 [])) =
        some (cfg .done none [] 0 0 [] 0 0 0 0 0
          (ShiQMACenteredGap.fractionBits (as.length+1)
            (ShiQMACenteredGap.centeringNumerator as.length
              (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs)))) ∧
      t ≤ n+as.length+2+32*2^(as.length+1) := by
  obtain ⟨t,hr,ht⟩ := prepared_run as bs hb hj none
  have hp := parser_run n as.length (as++bs) v
  have hi : ShiTMThresholdSamples.input n as bs =
      ShiBQP.encNat n ++ ShiBQP.encNat as.length ++ (as++bs) := by
    simp [ShiTMThresholdSamples.input, ShiTMCenteringPacking.input, List.append_assoc]
  refine ⟨t+(n+as.length+2), ?_, by omega⟩
  rw [Function.iterate_add_apply, hi, hp, hr]

def finiteMachine : FinTM2 where
  K := Stack
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := .inl .input
  k₁ := .inr .output
  Γ := Gam
  Λ := Label
  main := .skipN
  ΛFin := inferInstance
  σ := State
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

theorem init_eq (xs : List Bool) :
    Turing.initList finiteMachine xs = cfg .skipN none xs 0 0 [] 0 0 0 0 0 [] := by
  simp only [Turing.initList, finiteMachine, cfg]
  congr 1
  funext j
  rcases j with e | j
  · cases e <;> simp [store]
  · cases j <;> simp [store, ShiTMCenteringOutputCore.store]

theorem halt_eq (os : List Bool) :
    Turing.haltList finiteMachine os =
      ⟨none,none,store [] 0 0 [] 0 0 0 0 0 os⟩ := by
  simp only [Turing.haltList, finiteMachine]
  congr 1
  funext j
  rcases j with e | j
  · cases e <;> simp [store]
  · cases j <;> simp [store, ShiTMCenteringOutputCore.store]

theorem halt_step (os : List Bool) :
    run (some (cfg .done none [] 0 0 [] 0 0 0 0 0 os)) =
      some (Turing.haltList finiteMachine os) := by
  rw [halt_eq]
  rfl

/-- A complete finite machine run from the ordinary one-input-stack initial
configuration to the canonical halted output configuration. -/
theorem sampled_from_init (n : Nat) (as bs : List Bool) (hb : bs.length = as.length)
    (hj : ShiQMACenteredGap.centeringNumerator as.length
      (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs) < 2^(as.length+1)) :
    ∃ t : Nat,
      run^[t] (some (Turing.initList finiteMachine (ShiTMThresholdSamples.input n as bs))) =
        some (Turing.haltList finiteMachine
          (ShiQMACenteredGap.fractionBits (as.length+1)
            (ShiQMACenteredGap.centeringNumerator as.length
              (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs)))) ∧
      t ≤ n+as.length+3+32*2^(as.length+1) := by
  obtain ⟨t,hr,ht⟩ := sampled_run n as bs hb hj none
  refine ⟨t+1, ?_, by omega⟩
  rw [init_eq, Function.iterate_succ_apply', hr, halt_step]

/-- The full arithmetic machine, including parsing and its real final halt,
fits a single clock polynomial on valid threshold-sample inputs. -/
theorem sampled_polynomial_run (q : Polynomial ℕ) (n : Nat) (as bs : List Bool)
    (ha : as.length = ShiQMAConstructiveSchedule.rounds q n) (hb : bs.length = as.length)
    (hj : ShiQMACenteredGap.centeringNumerator as.length
      (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs) < 2^(as.length+1)) :
    ∃ t : Nat,
      run^[t] (some (Turing.initList finiteMachine (ShiTMThresholdSamples.input n as bs))) =
        some (Turing.haltList finiteMachine
          (ShiQMACenteredGap.fractionBits (as.length+1)
            (ShiQMACenteredGap.centeringNumerator as.length
              (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs)))) ∧
      t ≤ (64 * 3^(Nat.log 2 (q.eval 1+1)+q.natDegree+4)+3) *
        ((ShiTMThresholdSamples.input n as bs).length+1)^(2*q.natDegree+1) := by
  obtain ⟨t,hr,ht⟩ := sampled_from_init n as bs hb hj
  have hcap := ShiTMThresholdSamples.capacity_bound q n as bs ha
  have hsize := ShiTMThresholdSamples.input_length n as.length as bs rfl hb
  have hbase : n+as.length+3 ≤ (ShiTMThresholdSamples.input n as bs).length+1 := by omega
  have hp : 1 ≤ ((ShiTMThresholdSamples.input n as bs).length+1)^(2*q.natDegree) := by
    have hpos : 0 < ((ShiTMThresholdSamples.input n as bs).length+1)^(2*q.natDegree) := by positivity
    omega
  have hm : ((ShiTMThresholdSamples.input n as bs).length+1)^(2*q.natDegree) ≤
      ((ShiTMThresholdSamples.input n as bs).length+1)^(2*q.natDegree) *
        ((ShiTMThresholdSamples.input n as bs).length+1) := by nlinarith
  have hl : (ShiTMThresholdSamples.input n as bs).length+1 ≤
      ((ShiTMThresholdSamples.input n as bs).length+1)^(2*q.natDegree) *
        ((ShiTMThresholdSamples.input n as bs).length+1) := by nlinarith
  have hmul := Nat.mul_le_mul_left (64 * 3^(Nat.log 2 (q.eval 1+1)+q.natDegree+4)) hm
  refine ⟨t,hr,?_⟩
  rw [pow_succ ((ShiTMThresholdSamples.input n as bs).length+1) (2*q.natDegree)]
  nlinarith

/-- Total polynomial-time arithmetic, correct on the valid sampled inputs.
The clock supplies termination even for malformed or excessive-width strings. -/
theorem arithmetic_transducer (q : Polynomial ℕ) :
    ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
      ∀ (n : Nat) (as bs : List Bool),
        as.length = ShiQMAConstructiveSchedule.rounds q n → bs.length = as.length →
        ShiQMACenteredGap.centeringNumerator as.length
          (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs) < 2^(as.length+1) →
        g (ShiTMThresholdSamples.input n as bs) = ShiQMACenteredGap.fractionBits (as.length+1)
          (ShiQMACenteredGap.centeringNumerator as.length
            (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs)) := by
  let tm := finiteMachine
  let ein : Bool ≃ tm.Γ tm.k₀ := Equiv.refl Bool
  let d := 2*q.natDegree
  let c := 64 * 3^(Nat.log 2 (q.eval 1+1)+q.natDegree+4)+3
  let full := ShiTMTotalPolynomialClocked.finiteMachine tm ein d c
  obtain ⟨P,hP⟩ := ShiTMTotalPolynomialClocked.total_polynomial tm ein d c
  have hall : ∀ xs : List Bool, ∃ ys : List Bool,
      Nonempty (TM2OutputsInTime full (xs.map (Equiv.refl Bool).symm)
        (some (ys.map (Equiv.refl Bool).symm)) (P.eval xs.length)) := by
    intro xs
    obtain ⟨ys,hy⟩ := hP xs
    have hin : xs.map (Equiv.refl Bool).symm = xs := List.map_id xs
    have hout : ys.map (Equiv.refl Bool).symm = ys := List.map_id ys
    exact ⟨ys,(congrArg₂ (fun (a b : List Bool) =>
      Nonempty (TM2OutputsInTime full a (some b) (P.eval xs.length))) hin hout).mpr hy⟩
  obtain ⟨g,hg,hunique⟩ := ShiTMTotalFunction.function_of_total_polynomial full
    (Equiv.refl Bool) (Equiv.refl Bool) P hall
  obtain ⟨Q,hQ⟩ := ShiTMTotalPolynomialClocked.valid_run_polynomial tm ein d c
  refine ⟨g,hg,?_⟩
  intro n as bs ha hb hj
  let xs := ShiTMThresholdSamples.input n as bs
  let ys := ShiQMACenteredGap.fractionBits (as.length+1)
    (ShiQMACenteredGap.centeringNumerator as.length
      (ShiQMACenteredGap.binaryNumerator as) (ShiQMACenteredGap.binaryNumerator bs))
  obtain ⟨steps,hr,hsteps⟩ := sampled_polynomial_run q n as bs ha hb hj
  have hin : xs.map ein = xs := List.map_id xs
  have hr' : (ShiTMSubroutine.run tm.m)^[steps]
      (some (Turing.initList tm (xs.map ein))) = some (Turing.haltList tm ys) := by
    exact (congrArg (fun input : List (tm.Γ tm.k₀) =>
      (ShiTMSubroutine.run tm.m)^[steps] (some (Turing.initList tm input))) hin).trans hr
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

end ShiTMArithmeticFront

namespace ShiQMAGeneralGap
open ShiClassQMA ShiClassQMAU ShiQMAConstructiveSchedule

/-- A checked total polynomial-time generator for the actual centering coin. -/
theorem thresholdCoin_generator {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b) (q : Polynomial ℕ)
    (hb : ∀ n, 0 ≤ b n) (hab : ∀ n, b n ≤ a n)
    (hgap : ∀ n, (1 : ℝ) ≤ (↑(q.eval n) : ℝ) * (a n - b n)) :
    ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
      ∀ n, g (ShiBQP.unary n) = thresholdCoinBits A B q n := by
  obtain ⟨samples,hs,hspec⟩ := ShiTMThresholdSamples.samples_generator A B q
  obtain ⟨arithmetic,ha,haspec⟩ := ShiTMArithmeticFront.arithmetic_transducer q
  refine ⟨arithmetic ∘ samples,
    ShiTMCenteringPacking.polyTimeComputable_comp samples arithmetic hs ha, ?_⟩
  intro n
  rw [Function.comp_apply, hspec]
  have hA := A.length_eq n (rounds q n)
  have hB := B.length_eq n (rounds q n)
  have hstrict := thresholdCoinNumerator_lt A B q n (hb n) (hab n) (hgap n)
  have hout := haspec n (A.approximate (thresholdInput n (rounds q n)))
    (B.approximate (thresholdInput n (rounds q n))) hA (hB.trans hA.symm)
    (by simpa only [hA, thresholdCoinNumerator] using hstrict)
  simpa only [hA, thresholdCoinBits, thresholdCoinNumerator] using hout

theorem thresholdFamily_uniform {a b : Nat → ℝ}
    (F : QMAFamily) (hu : UniformQMA F)
    (A : ThresholdApproximation a) (B : ThresholdApproximation b) (q : Polynomial ℕ)
    (hb : ∀ n, 0 ≤ b n) (hab : ∀ n, b n ≤ a n)
    (hgap : ∀ n, (1 : ℝ) ≤ (↑(q.eval n) : ℝ) * (a n - b n)) :
    UniformQMA (thresholdFamily F A B q) := by
  obtain ⟨coin,hcoin,hbits⟩ := thresholdCoin_generator A B q hb hab hgap
  exact ShiTMJoint.centeredFamily_uniform_of_coin_generator F (thresholdCoinBits A B q)
    hu coin hcoin hbits

/-- General efficiently approximable thresholds with an inverse-polynomial gap
admit uniform copy-based amplification to any inverse-exponential polynomial
error target. No centering or amplification transducer is assumed. -/
theorem general_threshold_amplification_closed {a b : Nat → ℝ}
    (F : QMAFamily) (L : Language Bool)
    (hu : UniformQMA F) (hw : ShiBQP.WellFormed F.toFamily) (hp : ShiBQP.PolyBounded F.toFamily)
    (A : ThresholdApproximation a) (B : ThresholdApproximation b) (q p : Polynomial ℕ)
    (hb : ∀ n, 0 ≤ b n) (ha : ∀ n, a n ≤ 1) (hab : ∀ n, b n ≤ a n)
    (hgap : ∀ n, (1 : ℝ) ≤ (↑(q.eval n) : ℝ) * (a n - b n))
    (hv : VerifiesWith F L a b) :
    ∃ G : QMAFamily,
      UniformQMA G ∧ ShiBQP.WellFormed G.toFamily ∧ ShiBQP.PolyBounded G.toFamily ∧
      VerifiesWith G L (fun n => 1 - ((1 : ℝ) / 2) ^ (p.eval n))
        (fun n => ((1 : ℝ) / 2) ^ (p.eval n)) := by
  have hcenter := thresholdFamily_uniform F hu A B q hb hab hgap
  obtain ⟨hcw,hcp,_,hcv⟩ := thresholdFamily_semantics_and_resources F L A B q hw hp hb hab hgap hv
  apply centered_gap_amplification_closed (thresholdFamily F A B q) L hcenter hcw hcp
    (fun n => (a n - b n)/8) (2*q) p ?_ ?_ ?_ hcv
  · intro n; have h := hab n; linarith
  · intro n; have h1 := ha n; have h2 := hb n; linarith
  · intro n
    have h := hgap n
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith

/-- Class-level form of the closed general-threshold amplification theorem. -/
theorem QMAWith_general_threshold_amplification {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b) (q p : Polynomial ℕ)
    (hb : ∀ n, 0 ≤ b n) (ha : ∀ n, a n ≤ 1) (hab : ∀ n, b n ≤ a n)
    (hgap : ∀ n, (1 : ℝ) ≤ (↑(q.eval n) : ℝ) * (a n - b n)) :
    QMAWith a b ⊆ QMAWith (fun n => 1 - ((1 : ℝ)/2)^(p.eval n))
      (fun n => ((1 : ℝ)/2)^(p.eval n)) := by
  intro L hL
  obtain ⟨F,hu,hw,hp,hv⟩ := hL
  exact general_threshold_amplification_closed F L hu hw hp A B q p hb ha hab hgap hv

end ShiQMAGeneralGap

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMArithmeticFront.first_run, ``ShiTMArithmeticFront.second_run,
      ``ShiTMArithmeticFront.power_run, ``ShiTMArithmeticFront.core_run,
      ``ShiTMArithmeticFront.prepared_run, ``ShiTMArithmeticFront.threshold_prepared_run,
      ``ShiTMArithmeticFront.parser_run, ``ShiTMArithmeticFront.sampled_run,
      ``ShiTMArithmeticFront.sampled_from_init, ``ShiTMArithmeticFront.sampled_polynomial_run,
      ``ShiTMArithmeticFront.arithmetic_transducer, ``ShiQMAGeneralGap.thresholdCoin_generator,
      ``ShiQMAGeneralGap.thresholdFamily_uniform, ``ShiQMAGeneralGap.general_threshold_amplification_closed,
      ``ShiQMAGeneralGap.QMAWith_general_threshold_amplification] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected arithmetic-front axiom {ax} in {name}"
    logInfo m!"ARITHMETIC_FRONT_CHECKED {name}; axioms {axioms}"
