import «BQP-closed-references»
import «AMPUNI-subroutine-lift»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace BQPUnarySplit
open Turing Turing.TM2
abbrev K := Fin 4
abbrev Label := Fin 4
abbrev Reg := Bool × Bool
abbrev Gam : K → Type
  | ⟨0,_⟩ => Bool ⊕ Bool
  | ⟨_+1,_⟩ => Bool

def readBit (a : Option (Bool ⊕ Bool)) : Reg :=
  (Sum.elim id id (a.getD (.inl false)),a.isSome)

def program (keep : Bool) : Label → Stmt Gam Label Reg
  | 0 => .peek 0 (fun _ a => (false,match a with | some (.inl _) => true | _ => false))
      (.branch (fun r => r.2)
        (.pop 0 (fun _ _ => (false,false))
          (.push 1 (fun _ => true) (.goto (fun _ => 0))))
        (.load (fun _ => (false,false)) (.goto (fun _ => 1))))
  | 1 => .peek 1 (fun _ a => (false,a.isSome))
      (.branch (fun r => r.2)
        (.pop 1 (fun _ _ => (false,false))
          (.pop 0 (fun _ a => readBit a)
            (.branch (fun r => keep && r.2)
              (.push 2 (fun r => r.1) (.goto (fun _ => 1)))
              (.goto (fun _ => 1)))))
        (.load (fun _ => (false,false)) (.goto (fun _ => 2))))
  | 2 => .pop 0 (fun _ a => readBit a)
      (.branch (fun r => r.2)
        (if keep then .goto (fun _ => 2) else
          .push 2 (fun r => r.1) (.goto (fun _ => 2)))
        (.load (fun _ => (false,false)) (.goto (fun _ => 3))))
  | _ => .peek 2 (fun _ a => (false,a.isSome))
      (.branch (fun r => r.2)
        (.pop 2 (fun _ a => (a.getD false,false))
          (.push 3 (fun r => r.1) (.goto (fun _ => 3))))
        (.load (fun _ => (false,false)) .halt))

def tapes (input : List (Bool ⊕ Bool)) (n buf out : List Bool) : ∀ k, List (Gam k)
  | ⟨0,_⟩ => input
  | ⟨1,_⟩ => n
  | ⟨2,_⟩ => buf
  | ⟨_+3,_⟩ => out

def cfg (l : Label) (v : Reg) (input : List (Bool ⊕ Bool)) (n buf out : List Bool) :
    Cfg Gam Label Reg := ⟨some l,v,tapes input n buf out⟩

@[simp] theorem tape0 (input : List (Bool ⊕ Bool)) (n buf out : List Bool) :
    tapes input n buf out 0 = input := rfl
@[simp] theorem update0 (input : List (Bool ⊕ Bool)) (n buf out : List Bool) (u : List (Bool ⊕ Bool)) :
    Function.update (tapes input n buf out) 0 u = tapes u n buf out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape1 (input : List (Bool ⊕ Bool)) (n buf out : List Bool) :
    tapes input n buf out 1 = n := rfl
@[simp] theorem update1 (input : List (Bool ⊕ Bool)) (n buf out : List Bool) (u : List Bool) :
    Function.update (tapes input n buf out) 1 u = tapes input u buf out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape2 (input : List (Bool ⊕ Bool)) (n buf out : List Bool) :
    tapes input n buf out 2 = buf := rfl
@[simp] theorem update2 (input : List (Bool ⊕ Bool)) (n buf out : List Bool) (u : List Bool) :
    Function.update (tapes input n buf out) 2 u = tapes input n u out := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

@[simp] theorem tape3 (input : List (Bool ⊕ Bool)) (n buf out : List Bool) :
    tapes input n buf out 3 = out := rfl
@[simp] theorem update3 (input : List (Bool ⊕ Bool)) (n buf out : List Bool) (u : List Bool) :
    Function.update (tapes input n buf out) 3 u = tapes input n buf u := by
  funext k; fin_cases k <;> simp [tapes, Function.update]

theorem scan_cons (keep : Bool) (v : Reg) (d : Bool) (input : List (Bool ⊕ Bool))
    (n buf out : List Bool) :
    ShiTMSubroutine.run (program keep) (some (cfg 0 v (Sum.inl d::input) n buf out)) =
    some (cfg 0 (false,false) input (true::n) buf out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem scan_end (keep : Bool) (v : Reg) (t n buf out : List Bool) :
    ShiTMSubroutine.run (program keep) (some (cfg 0 v (t.map Sum.inr) n buf out)) =
    some (cfg 1 (false,false) (t.map Sum.inr) n buf out) := by
  cases t <;> simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem scan_run (keep : Bool) (s t n buf out : List Bool) (v : Reg) :
    (ShiTMSubroutine.run (program keep))^[s.length+1]
      (some (cfg 0 v (s.map Sum.inl++t.map Sum.inr) n buf out)) =
      some (cfg 1 (false,false) (t.map Sum.inr) (List.replicate s.length true++n) buf out) := by
  induction s generalizing n v with
  | nil => exact scan_end keep v t n buf out
  | cons d s ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [List.map_cons, List.cons_append, scan_cons]
      simpa only [List.replicate_succ', List.append_assoc,
        List.cons_append, List.nil_append] using ih (true::n) (false,false)

theorem drop_cons (keep : Bool) (v : Reg) (d : Bool) (t n buf out : List Bool) :
    ShiTMSubroutine.run (program keep) (some (cfg 1 v (Sum.inr d::t.map Sum.inr) (true::n) buf out)) =
    some (cfg 1 (d,true) (t.map Sum.inr) n (if keep then d::buf else buf) out) := by
  cases keep <;> simp [ShiTMSubroutine.run, step, stepAux, program, cfg, readBit]

theorem drop_empty (keep : Bool) (v : Reg) (n buf out : List Bool) :
    ShiTMSubroutine.run (program keep) (some (cfg 1 v [] (true::n) buf out)) =
    some (cfg 1 (false,false) [] n buf out) := by
  cases keep <;> simp [ShiTMSubroutine.run, step, stepAux, program, cfg, readBit]

theorem drop_end (keep : Bool) (v : Reg) (t buf out : List Bool) :
    ShiTMSubroutine.run (program keep) (some (cfg 1 v (t.map Sum.inr) [] buf out)) =
    some (cfg 2 (false,false) (t.map Sum.inr) [] buf out) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem drop_run (keep : Bool) (n : ℕ) (t buf out : List Bool) (v : Reg) :
    (ShiTMSubroutine.run (program keep))^[n+1]
      (some (cfg 1 v (t.map Sum.inr) (List.replicate n true) buf out)) =
      some (cfg 2 (false,false) ((t.drop n).map Sum.inr) []
        (if keep then (t.take n).reverse++buf else buf) out) := by
  induction n generalizing t buf v with
  | zero => simpa using drop_end keep v t buf out
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases t with
      | nil =>
          simp only [List.map_nil, List.replicate_succ, drop_empty]
          simpa using ih [] buf (false,false)
      | cons d t =>
          simp only [List.map_cons, List.replicate_succ, drop_cons]
          have h := ih t (if keep then d::buf else buf) (d,true)
          cases keep <;> simpa [List.reverse_cons, List.append_assoc] using h

theorem copy_cons (keep : Bool) (v : Reg) (d : Bool) (t buf out : List Bool) :
    ShiTMSubroutine.run (program keep) (some (cfg 2 v (Sum.inr d::t.map Sum.inr) [] buf out)) =
    some (cfg 2 (d,true) (t.map Sum.inr) [] (if keep then buf else d::buf) out) := by
  cases keep <;> simp [ShiTMSubroutine.run, step, stepAux, program, cfg, readBit]

theorem copy_end (keep : Bool) (v : Reg) (buf out : List Bool) :
    ShiTMSubroutine.run (program keep) (some (cfg 2 v [] [] buf out)) =
    some (cfg 3 (false,false) [] [] buf out) := by
  cases keep <;> simp [ShiTMSubroutine.run, step, stepAux, program, cfg, readBit]

theorem copy_run (keep : Bool) (t buf out : List Bool) (v : Reg) :
    (ShiTMSubroutine.run (program keep))^[t.length+1]
      (some (cfg 2 v (t.map Sum.inr) [] buf out)) =
      some (cfg 3 (false,false) [] [] (if keep then buf else t.reverse++buf) out) := by
  induction t generalizing buf v with
  | nil => simpa using copy_end keep v buf out
  | cons d t ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [List.map_cons, copy_cons]
      have h := ih (if keep then buf else d::buf) (d,true)
      cases keep <;> simpa [List.reverse_cons, List.append_assoc] using h

theorem output_cons (keep : Bool) (v : Reg) (d : Bool) (buf out : List Bool) :
    ShiTMSubroutine.run (program keep) (some (cfg 3 v [] [] (d::buf) out)) =
    some (cfg 3 (d,false) [] [] buf (d::out)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem output_end (keep : Bool) (v : Reg) (out : List Bool) :
    ShiTMSubroutine.run (program keep) (some (cfg 3 v [] [] [] out)) =
    some (⟨none,(false,false),tapes [] [] [] out⟩ : Cfg Gam Label Reg) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem output_run (keep : Bool) (buf out : List Bool) (v : Reg) :
    (ShiTMSubroutine.run (program keep))^[buf.length+1] (some (cfg 3 v [] [] buf out)) =
    some (⟨none,(false,false),tapes [] [] [] (buf.reverse++out)⟩ : Cfg Gam Label Reg) := by
  induction buf generalizing out v with
  | nil => exact output_end keep v out
  | cons d buf ih =>
      rw [List.length_cons, Function.iterate_succ_apply, output_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (d::out) (d,false)

def result (keep : Bool) (n : ℕ) (t : List Bool) := if keep then t.take n else t.drop n

private theorem chain {α : Type} (f : α → α) (x y z : α) (a b : ℕ)
    (ha : f^[a] x = y) (hb : f^[b] y = z) : f^[a+b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, ha, hb]

theorem pair_run (keep : Bool) (s t : List Bool) :
    (ShiTMSubroutine.run (program keep))^[2*s.length+(t.drop s.length).length+
        (result keep s.length t).length+4]
      (some (cfg 0 (false,false) (PvsNP.encodePair (s,t)) [] [] [])) =
      some (⟨none,(false,false),tapes [] [] [] (result keep s.length t)⟩ : Cfg Gam Label Reg) := by
  have h1 := scan_run keep s t [] [] [] (false,false)
  have h2 := drop_run keep s.length t [] [] (false,false)
  have h3 := copy_run keep (t.drop s.length)
    (if keep then (t.take s.length).reverse else []) [] (false,false)
  have h4 := output_run keep (result keep s.length t).reverse [] (false,false)
  simp only [List.append_nil] at h1 h2 h3 h4
  cases keep <;> simp only [Bool.false_eq_true, ↓reduceIte, result, List.length_reverse,
    List.reverse_reverse, List.append_nil] at *
  all_goals
    have h := chain _ _ _ _ _ _ (chain _ _ _ _ _ _ (chain _ _ _ _ _ _ h1 h2) h3) h4
    convert h using 1 <;> congr 1 <;> omega

abbrev machine (keep : Bool) : FinTM2 where
  K := K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := 0
  k₁ := 3
  Γ := Gam
  Λ := Label
  main := 0
  ΛFin := inferInstance
  σ := Reg
  initialState := (false,false)
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := program keep

theorem initial_eq (keep : Bool) (s : List (Bool ⊕ Bool)) :
    initList (machine keep) s = cfg 0 (false,false) s [] [] [] := by
  apply congrArg (fun S => (⟨some 0,(false,false),S⟩ : Cfg Gam Label Reg))
  funext k; fin_cases k <;> rfl

theorem final_eq (keep : Bool) (out : List Bool) :
    (⟨none,(false,false),tapes [] [] [] out⟩ : Cfg Gam Label Reg) = haltList (machine keep) out := by
  apply congrArg (fun S => (⟨none,(false,false),S⟩ : Cfg Gam Label Reg))
  funext k; fin_cases k <;> rfl

def outputs (keep : Bool) (s t : List Bool) :
    TM2OutputsInTime (machine keep) (PvsNP.encodePair (s,t)) (some (result keep s.length t))
      (2*(s.length+t.length)+4) := by
  refine { steps := 2*s.length+(t.drop s.length).length+(result keep s.length t).length+4
           steps_le_m := by
             cases keep <;> simp [result, List.length_drop, List.length_take] <;> omega
           evals_in_steps := ?_ }
  change (ShiTMSubroutine.run (program keep))^[_] (some (initList (machine keep) _)) =
    some (haltList (machine keep) _)
  rw [initial_eq, ← final_eq]
  exact pair_run keep s t

theorem polyTime (keep : Bool) : Nonempty (TM2ComputableInPolyTime PvsNP.encodePair id
    (fun p : List Bool × List Bool => result keep p.1.length p.2)) := by
  refine ⟨{ tm := machine keep
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.C 2 * Polynomial.X + Polynomial.C 4
            outputsFun := ?_ }⟩
  rintro ⟨s,t⟩
  simpa only [id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl, List.map_id,
    PvsNP.encodePair, List.length_append, List.length_map, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] using outputs keep s t

end BQPUnarySplit
