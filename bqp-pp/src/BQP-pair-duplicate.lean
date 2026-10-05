import «BQP-map-first-polytime»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace BQPPairDuplicate
open Turing Turing.TM2
abbrev K := Fin 4
abbrev Label := Fin 3
abbrev Gam : K → Type
  | ⟨0,_⟩ => Bool
  | ⟨1,_⟩ => Bool
  | ⟨2,_⟩ => Bool
  | ⟨_+3,_⟩ => Bool ⊕ Bool

def program : Label → Stmt Gam Label Bool
  | 0 => .peek 0 (fun _ a => a.isSome) (.branch id
      (.pop 0 (fun _ a => a.getD false) (.push 1 id (.push 2 id (.goto (fun _ => 0)))))
      (.load (fun _ => false) (.goto (fun _ => 1))))
  | 1 => .peek 1 (fun _ a => a.isSome) (.branch id
      (.pop 1 (fun _ a => a.getD false) (.push 3 Sum.inr (.goto (fun _ => 1))))
      (.load (fun _ => false) (.goto (fun _ => 2))))
  | _ => .peek 2 (fun _ a => a.isSome) (.branch id
      (.pop 2 (fun _ a => a.getD false) (.push 3 Sum.inl (.goto (fun _ => 2))))
      (.load (fun _ => false) .halt))

def tapes (s a b : List Bool) (out : List (Bool ⊕ Bool)) : ∀ k, List (Gam k)
  | ⟨0,_⟩ => s
  | ⟨1,_⟩ => a
  | ⟨2,_⟩ => b
  | ⟨_+3,_⟩ => out

def cfg (l : Label) (v : Bool) (s a b : List Bool) (out : List (Bool ⊕ Bool)) :
    Cfg Gam Label Bool := ⟨some l,v,tapes s a b out⟩

@[simp] theorem tape0 (s a b : List Bool) (out : List (Bool ⊕ Bool)) :
    tapes s a b out 0 = s := rfl
@[simp] theorem update0 (s a b : List Bool) (out : List (Bool ⊕ Bool)) (u : List Bool) :
    Function.update (tapes s a b out) 0 u = tapes u a b out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape1 (s a b : List Bool) (out : List (Bool ⊕ Bool)) :
    tapes s a b out 1 = a := rfl
@[simp] theorem update1 (s a b : List Bool) (out : List (Bool ⊕ Bool)) (u : List Bool) :
    Function.update (tapes s a b out) 1 u = tapes s u b out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape2 (s a b : List Bool) (out : List (Bool ⊕ Bool)) :
    tapes s a b out 2 = b := rfl
@[simp] theorem update2 (s a b : List Bool) (out : List (Bool ⊕ Bool)) (u : List Bool) :
    Function.update (tapes s a b out) 2 u = tapes s a u out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape3 (s a b : List Bool) (out : List (Bool ⊕ Bool)) :
    tapes s a b out 3 = out := rfl
@[simp] theorem update3 (s a b : List Bool) (out : List (Bool ⊕ Bool)) (u : List (Bool ⊕ Bool)) :
    Function.update (tapes s a b out) 3 u = tapes s a b u := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem copy_cons (v d : Bool) (s a b : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 0 v (d::s) a b out)) =
    some (cfg 0 d s (d::a) (d::b) out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem copy_nil (v : Bool) (a b : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 0 v [] a b out)) = some (cfg 1 false [] a b out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem copy_run (s a b : List Bool) (out : List (Bool ⊕ Bool)) (v : Bool) :
    (ShiTMSubroutine.run program)^[s.length+1] (some (cfg 0 v s a b out)) =
    some (cfg 1 false [] (s.reverse++a) (s.reverse++b) out) := by
  induction s generalizing a b v with
  | nil => exact copy_nil v a b out
  | cons d s ih =>
      change (ShiTMSubroutine.run program)^[s.length+1+1] _ = _
      rw [Function.iterate_succ_apply, copy_cons]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using ih (d::a) (d::b) d

theorem right_cons (v d : Bool) (a b : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 1 v [] (d::a) b out)) =
    some (cfg 1 d [] a b (Sum.inr d::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem right_nil (v : Bool) (b : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 1 v [] [] b out)) =
    some (cfg 2 false [] [] b out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem right_run (a b : List Bool) (out : List (Bool ⊕ Bool)) (v : Bool) :
    (ShiTMSubroutine.run program)^[a.length+1] (some (cfg 1 v [] a b out)) =
    some (cfg 2 false [] [] b ((a.reverse.map Sum.inr)++out)) := by
  induction a generalizing out v with
  | nil => exact right_nil v b out
  | cons d a ih =>
      change (ShiTMSubroutine.run program)^[a.length+1+1] _ = _
      rw [Function.iterate_succ_apply, right_cons]
      simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append, List.nil_append] using ih (Sum.inr d::out) d

theorem left_cons (v d : Bool) (a b : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 2 v [] a (d::b) out)) =
    some (cfg 2 d [] a b (Sum.inl d::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem left_nil (v : Bool) (a : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 2 v [] a [] out)) =
    some ((⟨none,false,tapes [] a [] out⟩ : Cfg Gam Label Bool)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]
theorem left_run (a b : List Bool) (out : List (Bool ⊕ Bool)) (v : Bool) :
    (ShiTMSubroutine.run program)^[b.length+1] (some (cfg 2 v [] a b out)) =
    some ((⟨none,false,tapes [] a [] ((b.reverse.map Sum.inl)++out)⟩ : Cfg Gam Label Bool)) := by
  induction b generalizing out v with
  | nil => exact left_nil v a out
  | cons d b ih =>
      change (ShiTMSubroutine.run program)^[b.length+1+1] _ = _
      rw [Function.iterate_succ_apply, left_cons]
      simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append, List.nil_append] using ih (Sum.inl d::out) d

theorem duplicate_run (s : List Bool) :
    (ShiTMSubroutine.run program)^[3*s.length+3] (some (cfg 0 false s [] [] [])) =
    some (⟨none,false,tapes [] [] [] (PvsNP.encodePair (s,s))⟩ : Cfg Gam Label Bool) := by
  have h1 := copy_run s [] [] [] false
  have h2 := right_run s.reverse s.reverse [] false
  have h3 := left_run [] s.reverse (s.map Sum.inr) false
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h1 h2 h3
  have h := BQPMapFirst.iterate_chain _ _ _ _ _ _
    (BQPMapFirst.iterate_chain _ _ _ _ _ _ h1 h2) h3
  convert h using 1 <;> congr 1 <;> omega

abbrev machine : FinTM2 where
  K := K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := 0
  k₁ := 3
  Γ := Gam
  Λ := Label
  main := 0
  ΛFin := inferInstance
  σ := Bool
  initialState := false
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := program

theorem initial_eq (s : List Bool) : initList machine s = cfg 0 false s [] [] [] := by
  apply congrArg (fun S => (⟨some 0,false,S⟩ : Cfg Gam Label Bool))
  funext k; fin_cases k <;> rfl

theorem final_eq (out : List (Bool ⊕ Bool)) :
    (⟨none,false,tapes [] [] [] out⟩ : Cfg Gam Label Bool) = haltList machine out := by
  apply congrArg (fun S => (⟨none,false,S⟩ : Cfg Gam Label Bool))
  funext k; fin_cases k <;> rfl

def outputs (s : List Bool) :
    TM2OutputsInTime machine s (some (PvsNP.encodePair (s,s))) (3*s.length+3) := by
  refine { steps := 3*s.length+3, steps_le_m := le_refl _, evals_in_steps := ?_ }
  change (ShiTMSubroutine.run program)^[_] (some (initList machine s)) = some (haltList machine _)
  rw [initial_eq, ← final_eq]
  exact duplicate_run s

theorem polyTime : Nonempty (TM2ComputableInPolyTime id PvsNP.encodePair
    (fun s : List Bool => (s,s))) := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.C 3 * Polynomial.X + Polynomial.C 3
            outputsFun := ?_ }⟩
  intro s
  simpa only [id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl,
    List.map_id, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] using outputs s

end BQPPairDuplicate
