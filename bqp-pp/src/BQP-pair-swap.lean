import «BQP-binary-add»
import «BQP-closed-references»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace BQPPairSwap
open Turing Turing.TM2 BQPBinaryAdd
abbrev K := Fin 5
abbrev Label := Fin 5
abbrev Gam : K → Type
  | ⟨0,_⟩ => Bool ⊕ Bool
  | ⟨1,_⟩ => Bool
  | ⟨2,_⟩ => Bool
  | ⟨3,_⟩ => Bool
  | ⟨_+4,_⟩ => Bool ⊕ Bool
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
          (.push 4 (fun r => Sum.inr r.1) (.goto (fun _ => 1))))
        (.load (fun _ => (false,false,false)) (.goto (fun _ => 2))))
  | _ => .peek 2 (fun r a => (r.1,false,a.isSome))
      (.branch (fun r => r.2.2)
        (.pop 2 (fun _ a => (a.getD false,false,false))
          (.push 4 (fun r => Sum.inl r.1) (.goto (fun _ => 2))))
        (.load (fun _ => (false,false,false)) .halt))

def tapes (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) : ∀ k, List (Gam k)
  | ⟨0,_⟩ => input
  | ⟨1,_⟩ => a
  | ⟨2,_⟩ => b
  | ⟨3,_⟩ => c
  | ⟨_+4,_⟩ => out

def cfg (l : Label) (v : Reg) (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    Cfg Gam Label Reg := ⟨some l,v,tapes input a b c out⟩

@[simp] theorem tape0 (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    tapes input a b c out 0 = input := rfl
@[simp] theorem update0 (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) (u : List (Bool ⊕ Bool)) :
    Function.update (tapes input a b c out) 0 u = tapes u a b c out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape1 (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    tapes input a b c out 1 = a := rfl
@[simp] theorem update1 (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) (u : List Bool) :
    Function.update (tapes input a b c out) 1 u = tapes input u b c out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape2 (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    tapes input a b c out 2 = b := rfl
@[simp] theorem update2 (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) (u : List Bool) :
    Function.update (tapes input a b c out) 2 u = tapes input a u c out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape3 (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    tapes input a b c out 3 = c := rfl
@[simp] theorem update3 (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) (u : List Bool) :
    Function.update (tapes input a b c out) 3 u = tapes input a b u out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape4 (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    tapes input a b c out 4 = out := rfl
@[simp] theorem update4 (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) (u : List (Bool ⊕ Bool)) :
    Function.update (tapes input a b c out) 4 u = tapes input a b c u := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem scan_left (v : Reg) (d : Bool) (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 0 v (Sum.inl d::input) a b c out)) =
    some (cfg 0 (d,true,true) input (d::a) b c out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem scan_right (v : Reg) (d : Bool) (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 0 v (Sum.inr d::input) a b c out)) =
    some (cfg 0 (d,false,true) input a (d::b) c out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem scan_nil (v : Reg) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 0 v [] a b c out)) =
    some (cfg 1 (false,false,false) [] a b c out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem scan_left_run (s : List Bool) (v : Reg) (input : List (Bool ⊕ Bool)) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
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

theorem scan_right_run (s : List Bool) (v : Reg) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    (ShiTMSubroutine.run program)^[s.length+1]
      (some (cfg 0 v (s.map Sum.inr) a b c out)) =
      some (cfg 1 (false,false,false) [] a (s.reverse++b) c out) := by
  induction s generalizing v b with
  | nil => exact scan_nil v a b c out
  | cons d s ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simpa only [List.map_cons, scan_right, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.nil_append] using ih (d,false,true) (d::b)


theorem right_cons (v : Reg) (d : Bool) (a b : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 1 v [] (d::a) b [] out)) =
    some (cfg 1 (d,false,false) [] a b [] (Sum.inr d::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem right_nil (v : Reg) (b : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 1 v [] [] b [] out)) =
    some (cfg 2 (false,false,false) [] [] b [] out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem right_run (a b : List Bool) (out : List (Bool ⊕ Bool)) (v : Reg) :
    (ShiTMSubroutine.run program)^[a.length+1] (some (cfg 1 v [] a b [] out)) =
    some (cfg 2 (false,false,false) [] [] b [] ((a.reverse.map Sum.inr)++out)) := by
  induction a generalizing out v with
  | nil => exact right_nil v b out
  | cons d a ih =>
      change (ShiTMSubroutine.run program)^[a.length+1+1] _ = _
      rw [Function.iterate_succ_apply, right_cons]
      simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append, List.nil_append] using ih (Sum.inr d::out) (d,false,false)

theorem left_cons (v : Reg) (d : Bool) (a b : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 2 v [] a (d::b) [] out)) =
    some (cfg 2 (d,false,false) [] a b [] (Sum.inl d::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem left_nil (v : Reg) (a : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 2 v [] a [] [] out)) =
    some ((⟨none,(false,false,false),tapes [] a [] [] out⟩ : Cfg Gam Label Reg)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem left_run (a b : List Bool) (out : List (Bool ⊕ Bool)) (v : Reg) :
    (ShiTMSubroutine.run program)^[b.length+1] (some (cfg 2 v [] a b [] out)) =
    some ((⟨none,(false,false,false),tapes [] a [] [] ((b.reverse.map Sum.inl)++out)⟩ : Cfg Gam Label Reg)) := by
  induction b generalizing out v with
  | nil => exact left_nil v a out
  | cons d b ih =>
      change (ShiTMSubroutine.run program)^[b.length+1+1] _ = _
      rw [Function.iterate_succ_apply, left_cons]
      simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append, List.nil_append] using ih (Sum.inl d::out) (d,false,false)

private theorem chain {α : Type} (f : α → α) (x y z : α) (a b : ℕ)
    (ha : f^[a] x = y) (hb : f^[b] y = z) : f^[a+b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, ha, hb]

theorem swap_run (s t : List Bool) :
    (ShiTMSubroutine.run program)^[2*(s.length+t.length)+3]
      (some (cfg 0 (false,false,false) (PvsNP.encodePair (s,t)) [] [] [] [])) =
      some (⟨none,(false,false,false),tapes [] [] [] [] (PvsNP.encodePair (t,s))⟩ : Cfg Gam Label Reg) := by
  obtain ⟨v,hl⟩ := scan_left_run s (false,false,false) (t.map Sum.inr) [] [] [] []
  have hr := scan_right_run t v s.reverse [] [] []
  have h2 := right_run s.reverse t.reverse [] (false,false,false)
  have h3 := left_run [] t.reverse (s.map Sum.inr) (false,false,false)
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hl hr h2 h3
  have h := chain _ _ _ _ _ _ (chain _ _ _ _ _ _ (chain _ _ _ _ _ _ hl hr) h2) h3
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

theorem final_eq (out : List (Bool ⊕ Bool)) :
    (⟨none,(false,false,false),tapes [] [] [] [] out⟩ : Cfg Gam Label Reg) = haltList machine out := by
  apply congrArg (fun S => (⟨none,(false,false,false),S⟩ : Cfg Gam Label Reg))
  funext k; fin_cases k <;> rfl

def outputs (s t : List Bool) :
    TM2OutputsInTime machine (PvsNP.encodePair (s,t)) (some (PvsNP.encodePair (t,s)))
      (2*(s.length+t.length)+3) := by
  refine { steps := 2*(s.length+t.length)+3, steps_le_m := le_refl _, evals_in_steps := ?_ }
  change (ShiTMSubroutine.run program)^[_] (some (initList machine _)) = some (haltList machine _)
  rw [initial_eq, ← final_eq]
  exact swap_run s t

theorem polyTime : Nonempty (TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair
    (fun p : List Bool × List Bool => (p.2,p.1))) := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
            outputsFun := ?_ }⟩
  rintro ⟨s,t⟩
  simpa only [id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl,
    List.map_id, PvsNP.encodePair, List.length_append, List.length_map,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] using outputs s t

end BQPPairSwap
