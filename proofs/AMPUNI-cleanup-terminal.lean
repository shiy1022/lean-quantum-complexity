import «AMPUNI-generic-clock-cleanup»
import «AMPUNI-subroutine-lift»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
noncomputable section

namespace ShiTMRepeatCleanup
variable {K sig : Type} [DecidableEq K] [Fintype K] {Gam : K → Type}

/-- The cleanup program counter just before its state-resetting halt. -/
def terminalPC (output : K) : ShiTMGenericCleanup.PC output :=
  ⟨(ShiTMGenericCleanup.todo output).length, by omega⟩

theorem terminal_command (output : K) :
    ShiTMGenericCleanup.commandAt output (terminalPC output) = none := by
  simp [ShiTMGenericCleanup.commandAt, terminalPC]

/-- Cleanup has an active terminal configuration before the final halt step. -/
theorem reaches_active_terminal (output : K) (initial : sig)
    (v : sig × Bool) (S : ∀ j, List (Gam j)) :
    ∃ v' : sig × Bool,
      (ShiTMGenericCleanup.run output initial)^[
        ShiTMGenericCleanup.suffixCost (ShiTMGenericCleanup.todo output) S]
        (some ⟨some (0 : ShiTMGenericCleanup.PC output), v, S⟩) =
          some ⟨some (terminalPC output), v',
            Function.update (fun _ => []) output (S output)⟩ := by
  obtain ⟨U, v', pc', hr, hp, hf⟩ :=
    ShiTMGenericCleanup.suffix_run output initial
      (ShiTMGenericCleanup.todo output) 0 v S (by simp)
      (ShiTMGenericCleanup.todo_nodup output)
  have hpc : pc' = terminalPC output := by
    apply Fin.ext
    simpa [terminalPC] using hp
  have hU : U = Function.update (fun _ => []) output (S output) := by
    funext j
    rw [hf]
    by_cases hj : j = output
    · subst j
      simp [ShiTMGenericCleanup.mem_todo]
    · simp [ShiTMGenericCleanup.mem_todo, hj]
  subst pc'
  subst U
  exact ⟨v', hr⟩

/-- Replace the final halt by an active handoff; earlier cleanup instructions are lifted. -/
def handoffMachine (output : K) (initial : sig) :
    (ShiTMGenericCleanup.PC output ⊕ Unit) →
      Stmt Gam (ShiTMGenericCleanup.PC output ⊕ Unit) (sig × Bool)
  | .inl pc =>
      if pc = terminalPC output then
        .load (fun _ => (initial, false)) (.goto (fun _ => .inr ()))
      else
        ShiTMSubroutine.stmt Sum.inl (ShiTMGenericCleanup.machine output initial pc)
  | .inr _ => .halt

theorem handoff_step (output : K) (initial : sig)
    (v : sig × Bool) (S : ∀ j, List (Gam j)) :
    (ShiTMSubroutine.run (handoffMachine output initial))^[1]
      (some ⟨some (.inl (terminalPC output)), v, S⟩) =
        some ⟨some (.inr ()), (initial, false), S⟩ := by
  simp [ShiTMSubroutine.run, handoffMachine, step, stepAux]

def runHandoff (output : K) (initial : sig) :
    Option (Cfg Gam (ShiTMGenericCleanup.PC output ⊕ Unit) (sig × Bool)) →
      Option (Cfg Gam (ShiTMGenericCleanup.PC output ⊕ Unit) (sig × Bool)) :=
  ShiTMSubroutine.run (handoffMachine output initial)

private theorem command_nonterminal (output : K)
    (pc : ShiTMGenericCleanup.PC output) (k : K)
    (hc : ShiTMGenericCleanup.commandAt output pc = some k) :
    pc ≠ terminalPC output := by
  intro h
  rw [h, terminal_command] at hc
  cases hc

/-- The modified machine clears one named stack without visiting its handoff. -/
theorem handoff_clear_run (output : K) (initial : sig)
    (pc : ShiTMGenericCleanup.PC output) (k : K)
    (xs : List (Gam k)) (v : sig × Bool) (S : ∀ j, List (Gam j))
    (hc : ShiTMGenericCleanup.commandAt output pc = some k)
    (hs : S k = xs) :
    (runHandoff output initial)^[xs.length + 1]
      (some ⟨some (.inl pc), v, S⟩) =
        some ⟨some (.inl (ShiTMGenericCleanup.nextPC output pc)),
          (v.1, false), Function.update S k []⟩ := by
  have hnon := command_nonterminal output pc k hc
  induction xs generalizing v S with
  | nil =>
      simp [runHandoff, ShiTMSubroutine.run, handoffMachine, hnon,
        ShiTMSubroutine.stmt, ShiTMGenericCleanup.machine,
        hc, step, stepAux, hs, Prod.snd]
  | cons x xs ih =>
      have hfirst :
          runHandoff output initial (some ⟨some (.inl pc), v, S⟩) =
            some ⟨some (.inl pc), (v.1, true), Function.update S k xs⟩ := by
        simp [runHandoff, ShiTMSubroutine.run, handoffMachine, hnon,
          ShiTMSubroutine.stmt, ShiTMGenericCleanup.machine,
          hc, step, stepAux, hs, Prod.snd]
      rw [List.length_cons, Function.iterate_succ_apply, hfirst]
      simpa using ih ((v.1, true)) (Function.update S k xs) (by simp)

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

private theorem active_suffix (output : K)
    (pc : ShiTMGenericCleanup.PC output) (k : K) (xs : List K)
    (hs : (ShiTMGenericCleanup.todo output).drop pc.val = k :: xs) :
    ShiTMGenericCleanup.commandAt output pc = some k ∧
      (ShiTMGenericCleanup.nextPC output pc).val = pc.val + 1 ∧
      (ShiTMGenericCleanup.todo output).drop
        (ShiTMGenericCleanup.nextPC output pc).val = xs := by
  have hlen := congrArg List.length hs
  simp only [List.length_drop, List.length_cons] at hlen
  have hn : (ShiTMGenericCleanup.nextPC output pc).val = pc.val + 1 := by
    apply Nat.mod_eq_of_lt
    omega
  refine ⟨by simp [ShiTMGenericCleanup.commandAt, hs], hn, ?_⟩
  rw [hn, ← List.drop_drop, hs]
  rfl

/-- The entire clearing prefix is preserved by the handoff controller. -/
theorem handoff_suffix_run (output : K) (initial : sig)
    (xs : List K) (pc : ShiTMGenericCleanup.PC output)
    (v : sig × Bool) (S : ∀ j, List (Gam j))
    (hs : (ShiTMGenericCleanup.todo output).drop pc.val = xs)
    (hnd : xs.Nodup) :
    ∃ (U : ∀ j, List (Gam j)) (v' : sig × Bool)
        (pc' : ShiTMGenericCleanup.PC output),
      (runHandoff output initial)^[
        ShiTMGenericCleanup.suffixCost xs S]
          (some ⟨some (.inl pc), v, S⟩) =
            some ⟨some (.inl pc'), v', U⟩ ∧
      pc'.val = pc.val + xs.length ∧
      ∀ j, U j = if j ∈ xs then [] else S j := by
  induction xs generalizing pc v S with
  | nil => exact ⟨S, v, pc, rfl, by simp, by intro j; simp⟩
  | cons k xs ih =>
      obtain ⟨hc, hn, hs'⟩ := active_suffix output pc k xs hs
      have hk : k ∉ xs := (List.nodup_cons.mp hnd).1
      let T := Function.update S k []
      have hfirst := handoff_clear_run output initial pc k (S k) v S hc rfl
      obtain ⟨U, w, pc', hrest, hp, hf⟩ :=
        ih (ShiTMGenericCleanup.nextPC output pc) (v.1, false) T
          hs' (List.nodup_cons.mp hnd).2
      have hmap : xs.map (fun j => (T j).length) =
          xs.map (fun j => (S j).length) := by
        apply List.map_congr_left
        intro j hj
        have hjk : j ≠ k := by intro he; subst j; exact hk hj
        simp [T, hjk]
      have hcost :
          (S k).length + 1 + ShiTMGenericCleanup.suffixCost xs T =
            ShiTMGenericCleanup.suffixCost (k :: xs) S := by
        simp only [ShiTMGenericCleanup.suffixCost, hmap,
          List.map_cons, List.sum_cons, List.length_cons]
        omega
      refine ⟨U, w, pc', ?_, ?_, ?_⟩
      · have h := iterTwo (runHandoff output initial) _ _ _ _ _ hfirst hrest
        simpa only [hcost] using h
      · rw [hn] at hp
        simp only [List.length_cons]
        omega
      · intro j
        rw [hf]
        by_cases hjk : j = k
        · subst j; simp [hk, T]
        · simp [hjk, T]

/-- The full cleanup pass now exits at an active handoff label. -/
theorem handoff_cleanup_run (output : K) (initial : sig)
    (v : sig × Bool) (S : ∀ j, List (Gam j)) :
    (runHandoff output initial)^[
      ShiTMGenericCleanup.suffixCost (ShiTMGenericCleanup.todo output) S + 1]
      (some ⟨some (.inl (0 : ShiTMGenericCleanup.PC output)), v, S⟩) =
        some ⟨some (.inr ()), (initial, false),
          Function.update (fun _ => []) output (S output)⟩ := by
  obtain ⟨U, v', pc', hr, hp, hf⟩ :=
    handoff_suffix_run output initial
      (ShiTMGenericCleanup.todo output) 0 v S (by simp)
      (ShiTMGenericCleanup.todo_nodup output)
  have hpc : pc' = terminalPC output := by
    apply Fin.ext
    simpa [terminalPC] using hp
  have hU : U = Function.update (fun _ => []) output (S output) := by
    funext j
    rw [hf]
    by_cases hj : j = output
    · subst j
      simp [ShiTMGenericCleanup.mem_todo]
    · simp [ShiTMGenericCleanup.mem_todo, hj]
  rw [hpc, hU] at hr
  exact iterTwo (runHandoff output initial) _ _ _ _ _ hr
    (handoff_step output initial v' _)

end ShiTMRepeatCleanup
