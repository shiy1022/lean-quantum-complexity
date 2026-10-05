import «BQP-counted-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPArchive
open Turing Turing.TM2
open BQPCounted (Key Gam extend bodyMap body_stacks update_body update_count)
variable {K L : Type} [DecidableEq K]
abbrev Label (L : Type) := Option L

def cfg (l : Label L) (v : Bool) (S : K → List Bool) (a : List Bool) :
    Cfg (Gam K) (Label L) Bool := ⟨some l,v,extend S a⟩

/-- Execute a body and drain its output onto an archive before returning.
All remaining body stacks, including unread circuit input, are preserved. -/
def program (output : K) (M : L → Stmt (fun _ : K => Bool) L Bool) :
    Label L → Stmt (Gam K) (Label L) Bool
  | some l => ShiTMHaltRouting.stmt some none (BQPStackEmbedding.stmt bodyMap (M l))
  | none => .peek (.inl output) (fun _ a => a.isSome) (.branch id
      (.pop (.inl output) (fun _ a => a.getD false)
        (.push (.inr ()) id (.goto (fun _ => none))))
      (.load (fun _ => false) .halt))

theorem drain_cons (output : K) (M : L → Stmt (fun _ : K => Bool) L Bool)
    (S : K → List Bool) (s a : List Bool) (v b : Bool) :
    ShiTMSubroutine.run (program output M)
      (some (cfg none v (Function.update S output (b::s)) a)) =
    some (cfg none b (Function.update S output s) (b::a)) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem drain_nil (output : K) (M : L → Stmt (fun _ : K => Bool) L Bool)
    (S : K → List Bool) (a : List Bool) (v : Bool) :
    ShiTMSubroutine.run (program output M)
      (some (cfg none v (Function.update S output []) a)) =
    some (⟨none,false,extend (Function.update S output []) a⟩ : Cfg (Gam K) (Label L) Bool) := by
  simp [ShiTMSubroutine.run, step, stepAux, program, cfg]

theorem drain_run (output : K) (M : L → Stmt (fun _ : K => Bool) L Bool)
    (S : K → List Bool) (s a : List Bool) (v : Bool) :
    (ShiTMSubroutine.run (program output M))^[s.length+1]
      (some (cfg none v (Function.update S output s) a)) =
    some (⟨none,false,extend (Function.update S output []) (s.reverse ++ a)⟩ :
      Cfg (Gam K) (Label L) Bool) := by
  induction s generalizing v a with
  | nil => exact drain_nil output M S a v
  | cons b s ih =>
      change (ShiTMSubroutine.run (program output M))^[s.length+1+1] _ = _
      rw [Function.iterate_succ_apply, drain_cons]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (a := b::a) (v := b)

theorem delegate (output : K) (M : L → Stmt (fun _ : K => Bool) L Bool) (main : L)
    (n : ℕ) (v w : Bool) (S T : K → List Bool) (a : List Bool)
    (h : (ShiTMSubroutine.run M)^[n] (some ⟨some main,v,S⟩) = some ⟨none,w,T⟩) :
    (ShiTMSubroutine.run (program output M))^[n]
      (some (cfg (some main) v S a)) = some (cfg none w T a) := by
  have he := (BQPStackEmbedding.run_iter bodyMap (extend (fun _ => []) a)
    M n (some ⟨some main,v,S⟩)).trans
      (congrArg (Option.map (BQPStackEmbedding.cfg bodyMap (extend (fun _ => []) a))) h)
  have hr := ShiTMHaltRouting.run_to_some (BQPStackEmbedding.machine bodyMap M)
    (program output M) some none (fun _ => rfl) n
    (some (BQPStackEmbedding.cfg bodyMap (extend (fun _ => []) a) ⟨some main,v,S⟩))
    (BQPStackEmbedding.cfg bodyMap (extend (fun _ => []) a) ⟨none,w,T⟩) he
  simpa only [BQPStackEmbedding.cfg, ShiTMHaltRouting.cfg, Option.map_some,
    Option.elim_some, Option.elim_none, body_stacks, cfg] using hr

/-- Exact-clock body-plus-archive composition. Its body specification is
instantiated by the already constructed instruction machine. -/
theorem body_archive_run (output : K) (M : L → Stmt (fun _ : K => Bool) L Bool) (main : L)
    (n : ℕ) (v w : Bool) (S T : K → List Bool) (a b : List Bool)
    (h : (ShiTMSubroutine.run M)^[n] (some ⟨some main,v,S⟩) =
      some ⟨none,w,Function.update T output b⟩) :
    (ShiTMSubroutine.run (program output M))^[n+b.length+1]
      (some (cfg (some main) v S a)) =
    some (⟨none,false,extend (Function.update T output []) (b.reverse ++ a)⟩ :
      Cfg (Gam K) (Label L) Bool) := by
  rw [show n+b.length+1 = (b.length+1)+n by omega, Function.iterate_add_apply,
    delegate output M main n v w S (Function.update T output b) a h]
  exact drain_run output M T b a w

end BQPArchive
