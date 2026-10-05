import «BQP-unary-block-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPUnaryBlock
open Turing Turing.TM2 BQPOpcodeEmission

private theorem replicate_append_cons (n : ℕ) (a : Bool) (bs : List Bool) :
    List.replicate n a ++ a :: bs = a :: (List.replicate n a ++ bs) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons a) ih

theorem outward_run (body : List ℕ) (xs : List Bool) (v : Bool) (buf out : List Bool) :
    (ShiTMSubroutine.run (program body))^[xs.length+1]
      (some (cfg false v xs buf out)) =
    some (cfg true false [] (List.replicate xs.length true ++ buf)
      (encode body ++ encode (List.replicate xs.length 1) ++ out)) := by
  induction xs generalizing v buf out with
  | nil => simpa [encode] using outward_nil body v buf out
  | cons a xs ih =>
      change (ShiTMSubroutine.run (program body))^[xs.length+1+1] _ = _
      rw [Function.iterate_succ_apply, outward_cons]
      have h := ih true (true::buf) (bits 1 ++ out)
      simpa only [List.length_cons, List.replicate_succ, encode,
        List.append_assoc, List.cons_append, replicate_append_cons] using h

theorem inward_run (body : List ℕ) (buf : List Bool) (v : Bool) (xs out : List Bool) :
    (ShiTMSubroutine.run (program body))^[buf.length+1]
      (some (cfg true v xs buf out)) =
    some (⟨none,false,tapes xs [] (encode (List.replicate buf.length 0) ++ out)⟩ : Cfg Gam Label State) := by
  induction buf generalizing v out with
  | nil => simpa [encode] using inward_nil body v xs out
  | cons a buf ih =>
      change (ShiTMSubroutine.run (program body))^[buf.length+1+1] _ = _
      rw [Function.iterate_succ_apply, inward_cons]
      simpa only [List.length_cons, List.replicate_succ, encode, List.append_assoc] using
        ih true (bits 0 ++ out)

/-- The rendered block moves out, executes its fixed body, and moves back.
The emitted bitstring is exactly the checker's reversed-opcode convention. -/
theorem block_run (body : List ℕ) (xs out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run (program body))^[2*xs.length+2]
      (some (cfg false v xs [] out)) =
    some (⟨none,false,tapes [] []
      (encode (List.replicate xs.length 1 ++ (body ++ List.replicate xs.length 0)) ++ out)⟩ :
      Cfg Gam Label State) := by
  have h1 := outward_run body xs v [] out
  simp only [List.append_nil] at h1
  have h2 := inward_run body (List.replicate xs.length true) false []
    (encode body ++ encode (List.replicate xs.length 1) ++ out)
  simp only [List.length_replicate] at h2
  rw [show 2*xs.length+2 = (xs.length+1)+(xs.length+1) by omega,
    Function.iterate_add_apply, h1]
  simpa only [encode_append, List.append_assoc] using h2

theorem initial_eq (body : List ℕ) (xs : List Bool) :
    initList (machine body) xs = cfg false false xs [] [] := by
  apply congrArg (fun S => (⟨some false,false,S⟩ : Cfg Gam Label State))
  funext k; change Fin 3 at k; fin_cases k <;> simp [initList, machine, tapes] <;> rfl

theorem final_eq (body : List ℕ) (out : List Bool) :
    (⟨none,false,tapes [] [] out⟩ : Cfg Gam Label State) = haltList (machine body) out := by
  apply congrArg (fun S => (⟨none,false,S⟩ : Cfg Gam Label State))
  funext k; change Fin 3 at k; fin_cases k <;> simp [haltList, machine, tapes] <;> rfl

set_option backward.isDefEq.respectTransparency false in
def outputs (body : List ℕ) (xs : List Bool) :
    TM2OutputsInTime (machine body) xs
      (some (encode (List.replicate xs.length 1 ++ (body ++ List.replicate xs.length 0))))
      (2*xs.length+2) := by
  refine { steps := 2*xs.length+2, steps_le_m := le_refl _, evals_in_steps := ?_ }
  change (ShiTMSubroutine.run (program body))^[2*xs.length+2]
    (some (initList (machine body) xs)) = some (haltList (machine body)
      (encode (List.replicate xs.length 1 ++ (body ++ List.replicate xs.length 0))))
  rw [initial_eq, ← final_eq]
  simpa only [List.append_nil] using block_run body xs [] false

end BQPUnaryBlock
