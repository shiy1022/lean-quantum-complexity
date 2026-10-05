import «BQP-binary-add»
import «BQP-closed-references»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace BQPBinaryAddPair
open Turing Turing.TM2 BQPBinaryAdd
abbrev K := Fin 5
abbrev Label := Fin 5
abbrev Gam : K → Type
  | ⟨0,_⟩ => Bool ⊕ Bool
  | ⟨_+1,_⟩ => Bool
abbrev Reg := Bool × Bool × Bool

def program : Label → Stmt Gam Label Reg
  | 0 => .pop 0 (fun _ a => (Sum.elim id id (a.getD (.inl false)),
        (match a with | some (.inl _) => true | _ => false),a.isSome))
      (.branch (fun r => r.2.2)
        (.branch (fun r => r.2.1)
          (.push 1 (fun r => r.1) (.goto (fun _ => 0)))
          (.push 2 (fun r => r.1) (.goto (fun _ => 0))))
        (.load (fun _ => (false,false,false)) (.goto (fun _ => 1))))
  | 1 => .peek 1 (fun r a => (r.1,false,a.isSome))
      (.branch (fun r => r.2.2)
        (.pop 1 (fun _ a => (a.getD false,false,false))
          (.push 3 (fun r => r.1) (.goto (fun _ => 1))))
        (.load (fun _ => (false,false,false)) (.goto (fun _ => 2))))
  | 2 => .peek 2 (fun r a => (r.1,false,a.isSome))
      (.branch (fun r => r.2.2)
        (.pop 2 (fun _ a => (a.getD false,false,false))
          (.push 1 (fun r => r.1) (.goto (fun _ => 2))))
        (.load (fun _ => (false,false,false)) (.goto (fun _ => 3))))
  | 3 => .peek 3 (fun r a => (r.1,a.isSome,false))
      (.peek 1 (fun r a => (r.1,r.2.1,a.isSome))
        (.branch (fun r => r.2.1 || r.2.2)
          (.pop 3 (fun r a => (r.1,a.getD false,false))
            (.pop 1 (fun r b => (r.1,r.2.1,b.getD false))
              (.push 2 (fun r => digit r.2.1 r.2.2 r.1)
                (.load (fun r => (nextCarry r.2.1 r.2.2 r.1,false,false))
                  (.goto (fun _ => 3))))))
          (.push 2 (fun r => r.1)
            (.load (fun _ => (false,false,false)) (.goto (fun _ => 4))))))
  | _ => .peek 2 (fun r a => (r.1,false,a.isSome))
      (.branch (fun r => r.2.2)
        (.pop 2 (fun _ a => (a.getD false,false,false))
          (.push 4 (fun r => r.1) (.goto (fun _ => 4))))
        (.load (fun _ => (false,false,false)) .halt))

def tapes (input : List (Bool ⊕ Bool)) (a b c out : List Bool) : ∀ k, List (Gam k)
  | ⟨0,_⟩ => input
  | ⟨1,_⟩ => a
  | ⟨2,_⟩ => b
  | ⟨3,_⟩ => c
  | ⟨_+4,_⟩ => out

def cfg (l : Label) (v : Reg) (input : List (Bool ⊕ Bool)) (a b c out : List Bool) :
    Cfg Gam Label Reg := ⟨some l,v,tapes input a b c out⟩

@[simp] theorem tape0 (input : List (Bool ⊕ Bool)) (a b c out : List Bool) :
    tapes input a b c out 0 = input := rfl
@[simp] theorem update0 (input : List (Bool ⊕ Bool)) (a b c out : List Bool) (u : List (Bool ⊕ Bool)) :
    Function.update (tapes input a b c out) 0 u = tapes u a b c out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape1 (input : List (Bool ⊕ Bool)) (a b c out : List Bool) :
    tapes input a b c out 1 = a := rfl
@[simp] theorem update1 (input : List (Bool ⊕ Bool)) (a b c out : List Bool) (u : List Bool) :
    Function.update (tapes input a b c out) 1 u = tapes input u b c out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape2 (input : List (Bool ⊕ Bool)) (a b c out : List Bool) :
    tapes input a b c out 2 = b := rfl
@[simp] theorem update2 (input : List (Bool ⊕ Bool)) (a b c out : List Bool) (u : List Bool) :
    Function.update (tapes input a b c out) 2 u = tapes input a u c out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape3 (input : List (Bool ⊕ Bool)) (a b c out : List Bool) :
    tapes input a b c out 3 = c := rfl
@[simp] theorem update3 (input : List (Bool ⊕ Bool)) (a b c out : List Bool) (u : List Bool) :
    Function.update (tapes input a b c out) 3 u = tapes input a b u out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape4 (input : List (Bool ⊕ Bool)) (a b c out : List Bool) :
    tapes input a b c out 4 = out := rfl
@[simp] theorem update4 (input : List (Bool ⊕ Bool)) (a b c out : List Bool) (u : List Bool) :
    Function.update (tapes input a b c out) 4 u = tapes input a b c u := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem scan_left (v : Reg) (d : Bool) (input : List (Bool ⊕ Bool)) (a b c out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 0 v (Sum.inl d::input) a b c out)) =
    some (cfg 0 (d,true,true) input (d::a) b c out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem scan_right (v : Reg) (d : Bool) (input : List (Bool ⊕ Bool)) (a b c out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 0 v (Sum.inr d::input) a b c out)) =
    some (cfg 0 (d,false,true) input a (d::b) c out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem scan_nil (v : Reg) (a b c out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 0 v [] a b c out)) =
    some (cfg 1 (false,false,false) [] a b c out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem scan_left_run (s : List Bool) (v : Reg) (input : List (Bool ⊕ Bool)) (a b c out : List Bool) :
    ∃ v', (ShiTMSubroutine.run program)^[s.length]
      (some (cfg 0 v (s.map Sum.inl++input) a b c out)) =
      some (cfg 0 v' input (s.reverse++a) b c out) := by
  induction s generalizing v a with
  | nil => exact ⟨v,rfl⟩
  | cons d s ih =>
      obtain ⟨v',h⟩ := ih (d,true,true) (d::a)
      refine ⟨v',?_⟩
      rw [List.length_cons, Function.iterate_succ_apply]
      simpa only [List.map_cons, List.cons_append, scan_left, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.nil_append] using h

theorem scan_right_run (s : List Bool) (v : Reg) (a b c out : List Bool) :
    (ShiTMSubroutine.run program)^[s.length+1]
      (some (cfg 0 v (s.map Sum.inr) a b c out)) =
      some (cfg 1 (false,false,false) [] a (s.reverse++b) c out) := by
  induction s generalizing v b with
  | nil => exact scan_nil v a b c out
  | cons d s ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simpa only [List.map_cons, scan_right, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.nil_append] using ih (d,false,true) (d::b)

theorem left_cons (v : Reg) (d : Bool) (s b c out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 1 v [] (d::s) b c out)) =
    some (cfg 1 (d,false,false) [] s b (d::c) out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem left_nil (v : Reg) (b c out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 1 v [] [] b c out)) =
    some (cfg 2 (false,false,false) [] [] b c out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem left_run (s b c out : List Bool) (v : Reg) :
    (ShiTMSubroutine.run program)^[s.length+1] (some (cfg 1 v [] s b c out)) =
    some (cfg 2 (false,false,false) [] [] b (s.reverse++c) out) := by
  induction s generalizing c v with
  | nil => exact left_nil v b c out
  | cons d s ih =>
      change (ShiTMSubroutine.run program)^[s.length+1+1] _ = _
      rw [Function.iterate_succ_apply, left_cons]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using ih (d::c) (d,false,false)

theorem right_cons (v : Reg) (d : Bool) (s a c out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 2 v [] a (d::s) c out)) =
    some (cfg 2 (d,false,false) [] (d::a) s c out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem right_nil (v : Reg) (a c out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 2 v [] a [] c out)) =
    some (cfg 3 (false,false,false) [] a [] c out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem right_run (s a c out : List Bool) (v : Reg) :
    (ShiTMSubroutine.run program)^[s.length+1] (some (cfg 2 v [] a s c out)) =
    some (cfg 3 (false,false,false) [] (s.reverse++a) [] c out) := by
  induction s generalizing a v with
  | nil => exact right_nil v a c out
  | cons d s ih =>
      change (ShiTMSubroutine.run program)^[s.length+1+1] _ = _
      rw [Function.iterate_succ_apply, right_cons]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using ih (d::a) (d,false,false)

theorem output_cons (v : Reg) (d : Bool) (s a c out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 4 v [] a (d::s) c out)) =
    some (cfg 4 (d,false,false) [] a s c (d::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem output_nil (v : Reg) (a c out : List Bool) :
    ShiTMSubroutine.run program (some (cfg 4 v [] a [] c out)) =
    some ((⟨none,(false,false,false),tapes [] a [] c out⟩ : Cfg Gam Label Reg)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem output_run (s a c out : List Bool) (v : Reg) :
    (ShiTMSubroutine.run program)^[s.length+1] (some (cfg 4 v [] a s c out)) =
    some ((⟨none,(false,false,false),tapes [] a [] c (s.reverse++out)⟩ : Cfg Gam Label Reg)) := by
  induction s generalizing out v with
  | nil => exact output_nil v a c out
  | cons d s ih =>
      change (ShiTMSubroutine.run program)^[s.length+1+1] _ = _
      rw [Function.iterate_succ_apply, output_cons]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using ih (d::out) (d,false,false)

def acfg (carry : Bool) (s t out : List Bool) : Cfg Gam Label Reg :=
  cfg 3 (carry,false,false) [] t out s []
theorem nil_step (carry : Bool) (out : List Bool) :
    ShiTMSubroutine.run program (some (acfg carry [] [] out)) =
      some (cfg 4 (false,false,false) [] [] (carry::out) [] []) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, acfg, cfg]

theorem both_step (a b carry : Bool) (s t out : List Bool) :
    ShiTMSubroutine.run program (some (acfg carry (a::s) (b::t) out)) =
      some (acfg (nextCarry a b carry) s t (digit a b carry::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, acfg, cfg]

theorem left_step (a carry : Bool) (s out : List Bool) :
    ShiTMSubroutine.run program (some (acfg carry (a::s) [] out)) =
      some (acfg (nextCarry a false carry) s [] (digit a false carry::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, acfg, cfg]

theorem right_step (b carry : Bool) (t out : List Bool) :
    ShiTMSubroutine.run program (some (acfg carry [] (b::t) out)) =
      some (acfg (nextCarry false b carry) [] t (digit false b carry::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, acfg, cfg]

/-- Addition consumes both preloaded inputs in exactly max(widths)+1 steps.
The output stack is reversed, ready for a linear stack-transfer pass. -/
theorem add_run (s t out : List Bool) (carry : Bool) :
    (ShiTMSubroutine.run program)^[max s.length t.length+1]
      (some (acfg carry s t out)) =
      some (cfg 4 (false,false,false) [] [] ((add s t carry).reverse++out) [] []) := by
  induction s generalizing t carry out with
  | nil =>
      induction t generalizing carry out with
      | nil => simpa [add] using nil_step carry out
      | cons b t ih =>
          change (ShiTMSubroutine.run program)^[t.length+1+1] _ = _
          rw [Function.iterate_succ_apply, right_step]
          simpa only [add, List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append,
            List.length_nil, Nat.zero_max] using ih (digit false b carry::out) (nextCarry false b carry)
  | cons a s ih =>
      cases t with
      | nil =>
          change (ShiTMSubroutine.run program)^[s.length+1+1] _ = _
          rw [Function.iterate_succ_apply, left_step]
          simpa only [add, List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append,
            List.length_nil, Nat.max_zero] using ih [] (digit a false carry::out) (nextCarry a false carry)
      | cons b t =>
          simp only [List.length_cons, Nat.add_max_add_right]
          rw [Function.iterate_succ_apply, both_step]
          simpa only [add, List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using
            ih t (digit a b carry::out) (nextCarry a b carry)


private theorem chain {α : Type} (f : α → α) (x y z : α) (a b : ℕ)
    (ha : f^[a] x = y) (hb : f^[b] y = z) : f^[a+b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, ha, hb]

/-- Full tagged-pair addition: parse, restore both inputs, add, and restore output.
No input preparation or arithmetic correctness hypothesis is assumed. -/
theorem pair_run (s t : List Bool) :
    (ShiTMSubroutine.run program)^[2*(s.length+t.length)+2*max s.length t.length+6]
      (some (cfg 0 (false,false,false) (s.map Sum.inl++t.map Sum.inr) [] [] [] [])) =
      some (⟨none,(false,false,false),tapes [] [] [] [] (add s t false)⟩ : Cfg Gam Label Reg) := by
  obtain ⟨v,hl⟩ := scan_left_run s (false,false,false) (t.map Sum.inr) [] [] [] []
  have hr := scan_right_run t v s.reverse [] [] []
  simp only [List.append_nil] at hl hr
  have h1 := chain _ _ _ _ _ _ hl hr
  have h2 := left_run s.reverse t.reverse [] [] (false,false,false)
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h2
  have h3 := right_run t.reverse [] s [] (false,false,false)
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h3
  have h4 := add_run s t [] false
  simp only [acfg, List.append_nil] at h4
  have h5 := output_run (add s t false).reverse [] [] [] (false,false,false)
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil, add_length] at h5
  have h := chain _ _ _ _ _ _ (chain _ _ _ _ _ _ (chain _ _ _ _ _ _ (chain _ _ _ _ _ _ h1 h2) h3) h4) h5
  convert h using 1 <;> congr 1 <;> omega

abbrev machine : FinTM2 where
  K := K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := 0
  k₁ := 4
  Γ := Gam
  Λ := Label
  main := 0
  ΛFin := inferInstance
  σ := Reg
  initialState := (false,false,false)
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := program

theorem initial_eq (input : List (Bool ⊕ Bool)) :
    initList machine input = cfg 0 (false,false,false) input [] [] [] [] := by
  apply congrArg (fun S => (⟨some 0,(false,false,false),S⟩ : Cfg Gam Label Reg))
  funext k; fin_cases k <;> rfl

theorem final_eq (out : List Bool) :
    (⟨none,(false,false,false),tapes [] [] [] [] out⟩ : Cfg Gam Label Reg) = haltList machine out := by
  apply congrArg (fun S => (⟨none,(false,false,false),S⟩ : Cfg Gam Label Reg))
  funext k; fin_cases k <;> rfl

def outputs (s t : List Bool) :
    TM2OutputsInTime machine (PvsNP.encodePair (s,t)) (some (add s t false))
      (4*(s.length+t.length)+6) := by
  refine { steps := 2*(s.length+t.length)+2*max s.length t.length+6
           steps_le_m := by omega
           evals_in_steps := ?_ }
  change (ShiTMSubroutine.run program)^[_] (some (initList machine _)) = some (haltList machine _)
  rw [initial_eq, ← final_eq]
  exact pair_run s t

theorem polyTime :
    Nonempty (TM2ComputableInPolyTime PvsNP.encodePair id
      (fun p : List Bool × List Bool => add p.1 p.2 false)) := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.C 4 * Polynomial.X + Polynomial.C 6
            outputsFun := ?_ }⟩
  rintro ⟨s,t⟩
  simpa only [id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl,
    List.map_id, PvsNP.encodePair, List.length_append, List.length_map,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] using outputs s t

end BQPBinaryAddPair
