import «BQP-binary-add»
import «BQP-closed-references»
import Mathlib.Data.List.Induction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace BQPPairCodec
open Turing Turing.TM2 BQPBinaryAdd
abbrev K := Fin 5
abbrev Label := Fin 5
abbrev Gam : K → Type
  | ⟨0,_⟩ => Bool
  | ⟨1,_⟩ => Bool
  | ⟨2,_⟩ => Bool
  | ⟨3,_⟩ => Bool
  | ⟨_+4,_⟩ => Bool ⊕ Bool
abbrev Reg := Bool × Bool × Bool

def program : Label → Stmt Gam Label Reg
  | 0 => .pop 0 (fun _ a => (false,a.getD false,a.isSome))
      (.branch (fun r => r.2.2)
        (.pop 0 (fun r a => (a.getD false,r.2.1,a.isSome))
          (.branch (fun r => r.2.2)
            (.branch (fun r => r.2.1)
              (.push 1 (fun r => r.1) (.goto (fun _ => 0)))
              (.push 2 (fun r => r.1) (.goto (fun _ => 0))))
            (.load (fun _ => (false,false,false)) (.goto (fun _ => 1)))))
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

def tapes (input : List Bool) (a b c : List Bool) (out : List (Bool ⊕ Bool)) : ∀ k, List (Gam k)
  | ⟨0,_⟩ => input
  | ⟨1,_⟩ => a
  | ⟨2,_⟩ => b
  | ⟨3,_⟩ => c
  | ⟨_+4,_⟩ => out

def cfg (l : Label) (v : Reg) (input : List Bool) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    Cfg Gam Label Reg := ⟨some l,v,tapes input a b c out⟩

@[simp] theorem tape0 (input : List Bool) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    tapes input a b c out 0 = input := rfl
@[simp] theorem update0 (input : List Bool) (a b c : List Bool) (out : List (Bool ⊕ Bool)) (u : List Bool) :
    Function.update (tapes input a b c out) 0 u = tapes u a b c out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape1 (input : List Bool) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    tapes input a b c out 1 = a := rfl
@[simp] theorem update1 (input : List Bool) (a b c : List Bool) (out : List (Bool ⊕ Bool)) (u : List Bool) :
    Function.update (tapes input a b c out) 1 u = tapes input u b c out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape2 (input : List Bool) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    tapes input a b c out 2 = b := rfl
@[simp] theorem update2 (input : List Bool) (a b c : List Bool) (out : List (Bool ⊕ Bool)) (u : List Bool) :
    Function.update (tapes input a b c out) 2 u = tapes input a u c out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape3 (input : List Bool) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    tapes input a b c out 3 = c := rfl
@[simp] theorem update3 (input : List Bool) (a b c : List Bool) (out : List (Bool ⊕ Bool)) (u : List Bool) :
    Function.update (tapes input a b c out) 3 u = tapes input a b u out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape4 (input : List Bool) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    tapes input a b c out 4 = out := rfl
@[simp] theorem update4 (input : List Bool) (a b c : List Bool) (out : List (Bool ⊕ Bool)) (u : List (Bool ⊕ Bool)) :
    Function.update (tapes input a b c out) 4 u = tapes input a b c u := by
  funext k; fin_cases k <;> simp [tapes, Function.update]


/-- Total decoding: an unmatched final bit is ignored; tags select either component. -/
def decode : List Bool → List Bool × List Bool
  | [] => ([],[])
  | [_] => ([],[])
  | tag::b::s => if tag then ((decode s).1,b::(decode s).2)
      else (b::(decode s).1,(decode s).2)

def pairCount : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | _::_::s => pairCount s + 1

theorem decode_length (s : List Bool) : (decode s).1.length+(decode s).2.length = pairCount s := by
  induction s using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b s ih _ => cases a <;> simp only [decode, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> simp only [pairCount] <;> omega

theorem pairCount_le (s : List Bool) : pairCount s ≤ s.length := by
  induction s using List.twoStepInduction with
  | nil => simp [pairCount]
  | singleton a => simp [pairCount]
  | cons_cons a b s ih _ => simp [pairCount]; omega

def encode (p : List Bool × List Bool) : List Bool :=
  (PvsNP.encodePair p).flatMap (Sum.elim (fun b => [false,b]) (fun b => [true,b]))

theorem decode_left (s w : List Bool) :
    decode (s.flatMap (fun b => [false,b])++w) = (s++(decode w).1,(decode w).2) := by
  induction s with
  | nil => simp
  | cons b s ih => simp [decode, ih]

theorem decode_right (s : List Bool) :
    decode (s.flatMap (fun b => [true,b])) = ([],s) := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [decode, ih]

theorem decode_encode (p : List Bool × List Bool) : decode (encode p) = p := by
  rcases p with ⟨s,t⟩
  simp [encode, PvsNP.encodePair, List.flatMap_append, List.flatMap_map,
    Function.comp_def, decode_left, decode_right]

theorem scan_left (v : Reg) (d : Bool) (input a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 0 v (false::d::input) a b c out)) =
    some (cfg 0 (d,false,true) input a (d::b) c out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem scan_right (v : Reg) (d : Bool) (input a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 0 v (true::d::input) a b c out)) =
    some (cfg 0 (d,true,true) input (d::a) b c out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem scan_nil (v : Reg) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 0 v [] a b c out)) =
    some (cfg 1 (false,false,false) [] a b c out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem scan_singleton (v : Reg) (d : Bool) (a b c : List Bool) (out : List (Bool ⊕ Bool)) :
    ShiTMSubroutine.run program (some (cfg 0 v [d] a b c out)) =
    some (cfg 1 (false,false,false) [] a b c out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem scan_run (s : List Bool) (a b c : List Bool) (out : List (Bool ⊕ Bool)) (v : Reg) :
    (ShiTMSubroutine.run program)^[pairCount s+1] (some (cfg 0 v s a b c out)) =
    some (cfg 1 (false,false,false) [] ((decode s).2.reverse++a) ((decode s).1.reverse++b) c out) := by
  induction s using List.twoStepInduction generalizing a b v with
  | nil => exact scan_nil v a b c out
  | singleton d => exact scan_singleton v d a b c out
  | cons_cons tag d s ih _ =>
      rw [pairCount, Function.iterate_succ_apply]
      cases tag
      · rw [scan_left]
        simpa [decode, List.reverse_cons, List.append_assoc] using ih a (d::b) (d,false,true)
      · rw [scan_right]
        simpa [decode, List.reverse_cons, List.append_assoc] using ih (d::a) b (d,true,true)
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

theorem decode_run (s : List Bool) :
    (ShiTMSubroutine.run program)^[2*pairCount s+3]
      (some (cfg 0 (false,false,false) s [] [] [] [])) =
      some (⟨none,(false,false,false),tapes [] [] [] [] (PvsNP.encodePair (decode s))⟩ : Cfg Gam Label Reg) := by
  have h1 := scan_run s [] [] [] [] (false,false,false)
  have h2 := right_run (decode s).2.reverse (decode s).1.reverse [] (false,false,false)
  have h3 := left_run [] (decode s).1.reverse ((decode s).2.map Sum.inr) (false,false,false)
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h1 h2 h3
  have h := chain _ _ _ _ _ _ (chain _ _ _ _ _ _ h1 h2) h3
  have hl := decode_length s
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

theorem initial_eq (input : List Bool) :
    initList machine input = cfg 0 (false,false,false) input [] [] [] [] := by
  apply congrArg (fun S => (⟨some 0,(false,false,false),S⟩ : Cfg Gam Label Reg))
  funext k; fin_cases k <;> rfl

theorem final_eq (out : List (Bool ⊕ Bool)) :
    (⟨none,(false,false,false),tapes [] [] [] [] out⟩ : Cfg Gam Label Reg) = haltList machine out := by
  apply congrArg (fun S => (⟨none,(false,false,false),S⟩ : Cfg Gam Label Reg))
  funext k; fin_cases k <;> rfl

def outputs (s : List Bool) :
    TM2OutputsInTime machine s (some (PvsNP.encodePair (decode s))) (2*s.length+3) := by
  refine { steps := 2*pairCount s+3
           steps_le_m := by have h := pairCount_le s; omega
           evals_in_steps := ?_ }
  change (ShiTMSubroutine.run program)^[_] (some (initList machine _)) = some (haltList machine _)
  rw [initial_eq, ← final_eq]
  exact decode_run s

theorem decode_polyTime : Nonempty (TM2ComputableInPolyTime id PvsNP.encodePair decode) := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
            outputsFun := ?_ }⟩
  intro s
  simpa only [id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl,
    List.map_id, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] using outputs s

theorem encode_polyTime : Nonempty (TM2ComputableInPolyTime PvsNP.encodePair id encode) := by
  obtain ⟨M,_⟩ := BQPChecked.reference3.1 Bool
    (Sum.elim (fun b => [false,b]) (fun b => [true,b])) 2
    (by intro c; cases c <;> simp) (List Bool) id encode (fun _ => rfl)
  exact ⟨M⟩

end BQPPairCodec
