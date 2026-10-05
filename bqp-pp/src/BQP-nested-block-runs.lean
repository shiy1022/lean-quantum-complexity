import «BQP-nested-block-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPNestedBlock
open Turing Turing.TM2 BQPOpcodeEmission

private theorem replicate_append_cons (n : ℕ) (a : Bool) (bs : List Bool) :
    List.replicate n a ++ a :: bs = a :: (List.replicate n a ++ bs) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons a) ih

theorem run0 (pre mid post : List ℕ) (a : List Bool) (v : Bool) (b c d out : List Bool) :
    (ShiTMSubroutine.run (program pre mid post))^[a.length+1]
      (some (cfg 0 v a b c d out)) =
    some (cfg 1 false [] b (List.replicate a.length true ++ c) d
      (encode pre ++ encode (List.replicate a.length 1) ++ out)) := by
  induction a generalizing v c out with
  | nil => simpa [encode] using step0_nil pre mid post v [] b c d out
  | cons x a ih =>
      change (ShiTMSubroutine.run (program pre mid post))^[a.length+1+1] _ = _
      rw [Function.iterate_succ_apply, step0_cons]
      simpa only [List.length_cons, List.replicate_succ, encode, List.append_assoc,
        List.cons_append, replicate_append_cons] using ih true (true::c) (bits 1 ++ out)

theorem run1 (pre mid post : List ℕ) (b : List Bool) (v : Bool) (a c d out : List Bool) :
    (ShiTMSubroutine.run (program pre mid post))^[b.length+1]
      (some (cfg 1 v a b c d out)) =
    some (cfg 2 false a [] c (List.replicate b.length true ++ d)
      (encode mid ++ encode (List.replicate b.length 1) ++ out)) := by
  induction b generalizing v d out with
  | nil => simpa [encode] using step1_nil pre mid post v a [] c d out
  | cons x b ih =>
      change (ShiTMSubroutine.run (program pre mid post))^[b.length+1+1] _ = _
      rw [Function.iterate_succ_apply, step1_cons]
      simpa only [List.length_cons, List.replicate_succ, encode, List.append_assoc,
        List.cons_append, replicate_append_cons] using ih true (true::d) (bits 1 ++ out)

theorem run2 (pre mid post : List ℕ) (d : List Bool) (v : Bool) (a b c out : List Bool) :
    (ShiTMSubroutine.run (program pre mid post))^[d.length+1]
      (some (cfg 2 v a b c d out)) =
    some (cfg 3 false a b c [] (encode post ++ encode (List.replicate d.length 0) ++ out)) := by
  induction d generalizing v out with
  | nil => simpa [encode] using step2_nil pre mid post v a b c [] out
  | cons x d ih =>
      change (ShiTMSubroutine.run (program pre mid post))^[d.length+1+1] _ = _
      rw [Function.iterate_succ_apply, step2_cons]
      simpa only [List.length_cons, List.replicate_succ, encode, List.append_assoc] using
        ih true (bits 0 ++ out)

theorem run3 (pre mid post : List ℕ) (c : List Bool) (v : Bool) (a b d out : List Bool) :
    (ShiTMSubroutine.run (program pre mid post))^[c.length+1]
      (some (cfg 3 v a b c d out)) =
    some (⟨none,false,tapes a b [] d (encode (List.replicate c.length 0) ++ out)⟩ : Cfg Gam Label Bool) := by
  induction c generalizing v out with
  | nil => simpa [encode] using step3_nil pre mid post v a b [] d out
  | cons x c ih =>
      change (ShiTMSubroutine.run (program pre mid post))^[c.length+1+1] _ = _
      rw [Function.iterate_succ_apply, step3_cons]
      simpa only [List.length_cons, List.replicate_succ, encode, List.append_assoc] using
        ih true (bits 0 ++ out)

private theorem chain {α : Type} (f : α → α) (x y z : α) (a b : ℕ)
    (h : f^[a] x = y) (h' : f^[b] y = z) : f^[a+b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, h, h']

def block (n d : ℕ) (pre mid post : List ℕ) : List ℕ :=
  List.replicate n 1 ++ pre ++ List.replicate d 1 ++ mid ++
    List.replicate d 0 ++ post ++ List.replicate n 0

theorem block_run (pre mid post : List ℕ) (a b out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run (program pre mid post))^[2*a.length+2*b.length+4]
      (some (cfg 0 v a b [] [] out)) =
    some (⟨none,false,tapes [] [] [] [] (encode (block a.length b.length pre mid post) ++ out)⟩ :
      Cfg Gam Label Bool) := by
  have h0 := run0 pre mid post a v b [] [] out
  simp only [List.append_nil] at h0
  have h1 := run1 pre mid post b false [] (List.replicate a.length true) []
    (encode pre ++ encode (List.replicate a.length 1) ++ out)
  simp only [List.append_nil] at h1
  have h2 := run2 pre mid post (List.replicate b.length true) false [] []
    (List.replicate a.length true)
    (encode mid ++ encode (List.replicate b.length 1) ++
      (encode pre ++ encode (List.replicate a.length 1) ++ out))
  simp only [List.length_replicate] at h2
  have h3 := run3 pre mid post (List.replicate a.length true) false [] [] []
    (encode post ++ encode (List.replicate b.length 0) ++
      (encode mid ++ encode (List.replicate b.length 1) ++
        (encode pre ++ encode (List.replicate a.length 1) ++ out)))
  simp only [List.length_replicate] at h3
  have h01 := chain _ _ _ _ _ _ h0 h1
  have h012 := chain _ _ _ _ _ _ h01 h2
  have hall := chain _ _ _ _ _ _ h012 h3
  rw [show a.length+1+(b.length+1)+(b.length+1)+(a.length+1) =
    2*a.length+2*b.length+4 by omega] at hall
  simpa only [block, encode_append, List.append_assoc] using hall

end BQPNestedBlock
