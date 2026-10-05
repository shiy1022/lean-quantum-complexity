import «BQP-stack-embedding»
import «BQP-halt-routing-run»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPCounted
open Turing Turing.TM2
variable {K L : Type} [DecidableEq K]
abbrev Key (K : Type) := K ⊕ Unit
abbrev Label (L : Type) := Option (Option L)
abbrev Gam (K : Type) : Key K → Type := fun _ => Bool

def bodyMap : K ↪ Key K := ⟨Sum.inl, Sum.inl_injective⟩

def extend (S : K → List Bool) (count : List Bool) : Key K → List Bool
  | .inl k => S k
  | .inr _ => count

def cfg (l : Label L) (v : Bool) (S : K → List Bool) (count : List Bool) :
    Cfg (Gam K) (Label L) Bool := ⟨some l,v,extend S count⟩

@[simp] theorem at_body (S : K → List Bool) (a : List Bool) (k : K) : extend S a (.inl k) = S k := rfl
@[simp] theorem at_count (S : K → List Bool) (a : List Bool) : extend S a (.inr ()) = a := rfl
@[simp] theorem update_body (S : K → List Bool) (a : List Bool) (k : K) (t : List Bool) :
    Function.update (extend S a) (.inl k) t = extend (Function.update S k t) a := by
  funext j
  cases j with
  | inl j =>
      by_cases h : j = k
      · subst j; simp [extend]
      · have hn : (Sum.inl j : Key K) ≠ .inl k := by simpa using h
        simp [extend, h, hn]
  | inr u => simp [extend]
@[simp] theorem update_count (S : K → List Bool) (a t : List Bool) :
    Function.update (extend S a) (.inr ()) t = extend S t := by
  funext j; cases j with
  | inl j => simp [extend]
  | inr u => cases u; simp [extend]

def program (input : K) (M : L → Stmt (fun _ : K => Bool) L Bool) (main : L) :
    Label L → Stmt (Gam K) (Label L) Bool
  | none => .pop (.inl input) (fun _ a => a.getD false) (.branch id
      (.push (.inr ()) (fun _ => true) (.goto (fun _ => none)))
      (.goto (fun _ => some none)))
  | some none => .pop (.inr ()) (fun _ a => a.isSome) (.branch id
      (.goto (fun _ => some (some main))) (.load (fun _ => false) .halt))
  | some (some l) => ShiTMHaltRouting.stmt (fun l => some (some l)) (some none)
      (BQPStackEmbedding.stmt bodyMap (M l))

theorem header_cons (input : K) (M : L → Stmt (fun _ : K => Bool) L Bool) (main : L)
    (v : Bool) (S : K → List Bool) (s a : List Bool) (h : S input = true::s) :
    ShiTMSubroutine.run (program input M main) (some (cfg none v S a)) =
    some (cfg none true (Function.update S input s) (true::a)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg, h]

theorem header_end (input : K) (M : L → Stmt (fun _ : K => Bool) L Bool) (main : L)
    (v : Bool) (S : K → List Bool) (s a : List Bool) (h : S input = false::s) :
    ShiTMSubroutine.run (program input M main) (some (cfg none v S a)) =
    some (cfg (some none) false (Function.update S input s) a) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg, h]

theorem driver_cons (input : K) (M : L → Stmt (fun _ : K => Bool) L Bool) (main : L)
    (v b : Bool) (S : K → List Bool) (a : List Bool) :
    ShiTMSubroutine.run (program input M main) (some (cfg (some none) v S (b::a))) =
    some (cfg (some (some main)) true S a) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem driver_end (input : K) (M : L → Stmt (fun _ : K => Bool) L Bool) (main : L)
    (v : Bool) (S : K → List Bool) :
    ShiTMSubroutine.run (program input M main) (some (cfg (some none) v S [])) =
    some (⟨none,false,extend S []⟩ : Cfg (Gam K) (Label L) Bool) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem body_stacks (S : K → List Bool) (a : List Bool) :
    Function.extend bodyMap S (extend (fun _ => []) a) = extend S a := by
  funext j
  cases j with
  | inl j => exact bodyMap.injective.extend_apply _ _ j
  | inr u =>
      rw [Function.extend_apply' _ _ _ (by rintro ⟨i,h⟩; cases h)]
      rfl

theorem delegate (input : K) (M : L → Stmt (fun _ : K => Bool) L Bool) (main : L)
    (n : ℕ) (v w : Bool) (S T : K → List Bool) (a : List Bool)
    (h : (ShiTMSubroutine.run M)^[n] (some ⟨some main,v,S⟩) = some ⟨none,w,T⟩) :
    (ShiTMSubroutine.run (program input M main))^[n]
      (some (cfg (some (some main)) v S a)) = some (cfg (some none) w T a) := by
  have he := (BQPStackEmbedding.run_iter bodyMap (extend (fun _ => []) a)
    M n (some ⟨some main,v,S⟩)).trans
      (congrArg (Option.map (BQPStackEmbedding.cfg bodyMap (extend (fun _ => []) a))) h)
  have hr := ShiTMHaltRouting.run_to_some (BQPStackEmbedding.machine bodyMap M)
    (program input M main) (fun l => some (some l)) (some none) (fun _ => rfl) n
    (some (BQPStackEmbedding.cfg bodyMap (extend (fun _ => []) a) ⟨some main,v,S⟩))
    (BQPStackEmbedding.cfg bodyMap (extend (fun _ => []) a) ⟨none,w,T⟩) he
  simpa only [BQPStackEmbedding.cfg, ShiTMHaltRouting.cfg, Option.map_some,
    Option.elim_some, Option.elim_none, body_stacks, cfg] using hr

private theorem replicate_append_cons (n : ℕ) (bs : List Bool) :
    List.replicate n true ++ true :: bs = true :: (List.replicate n true ++ bs) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons true) ih

theorem header_run (input : K) (M : L → Stmt (fun _ : K => Bool) L Bool) (main : L)
    (n : ℕ) (v : Bool) (S : K → List Bool) (s a : List Bool) :
    (ShiTMSubroutine.run (program input M main))^[n+1]
      (some (cfg none v (Function.update S input (List.replicate n true ++ false::s)) a)) =
    some (cfg (some none) false (Function.update S input s) (List.replicate n true ++ a)) := by
  induction n generalizing v a with
  | zero =>
      have h := header_end input M main v (Function.update S input (false::s)) s a (by simp)
      simpa only [Function.update_idem, List.replicate_zero, List.nil_append, Nat.zero_add, Function.iterate_one] using h
  | succ n ih =>
      change (ShiTMSubroutine.run (program input M main))^[n+1+1] _ = _
      rw [Function.iterate_succ_apply]
      have hs := header_cons input M main v
        (Function.update S input (List.replicate (n+1) true ++ false::s))
        (List.replicate n true ++ false::s) a (by simp [List.replicate_succ])
      rw [hs]
      simp only [Function.update_idem]
      simpa only [List.replicate_succ, List.cons_append, replicate_append_cons] using ih true (true::a)

end BQPCounted
