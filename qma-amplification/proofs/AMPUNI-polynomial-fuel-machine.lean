import «AMPUNI-fuel-run»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMPolynomialFuel
open ShiTMFuel

/-- A fixed number of multiplication stages is part of the finite program. -/
abbrev Label (d : Nat) := Unit ⊕ ((Fin (d + 1) × ShiTMFuel.Label) ⊕ (Fin (d + 1) ⊕ Unit))
abbrev init {d : Nat} : Label d := .inl ()
abbrev stage {d : Nat} (i : Fin (d + 1)) (l : ShiTMFuel.Label) : Label d :=
  .inr (.inl (i, l))
abbrev transfer {d : Nat} (i : Fin (d + 1)) : Label d := .inr (.inr (.inl i))
abbrev done {d : Nat} : Label d := .inr (.inr (.inr ()))

def previous {d : Nat} (i : Fin (d + 1)) : Fin (d + 1) :=
  ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

def pushCounter {d : Nat} : Nat → Stmt Gam (Label d) State → Stmt Gam (Label d) State
  | 0, q => q
  | k + 1, q => .push .counter (fun _ => true) (pushCounter k q)

theorem stepAux_pushCounter {d : Nat} (k : Nat) (q : Stmt Gam (Label d) State)
    (v : State) (xs tmp ctr fuel : List Bool) :
    stepAux (pushCounter k q) v (storeFn xs tmp ctr fuel) =
      stepAux q v (storeFn xs tmp (List.replicate k true ++ ctr) fuel) := by
  induction k generalizing ctr with
  | zero => rfl
  | succ k ih =>
      simp only [pushCounter, stepAux, stacks_counter, update_counter]
      rw [ih]
      congr 2
      simp only [List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append]

/-- Each stage multiplies the current unary counter by input length plus
one, using the previously checked scan-and-restore fuel routine. -/
def machine (d k : Nat) : Label d → Stmt Gam (Label d) State
  | .inl _ => pushCounter k (.goto (fun _ => stage ⟨d, Nat.lt_succ_self d⟩ .outer))
  | .inr (.inl (i, .done)) =>
      .goto (fun _ => if i.val = 0 then done else transfer i)
  | .inr (.inl (i, l)) => ShiTMSubroutine.stmt (stage i) (ShiTMFuel.machine 1 l)
  | .inr (.inr (.inl i)) =>
      .pop .fuel (fun _ x => x)
        (.branch Option.isSome
          (.push .counter (fun _ => true) (.goto (fun _ => transfer i)))
          (.goto (fun _ => stage (previous i) .outer)))
  | .inr (.inr (.inr _)) => .halt

abbrev run (d k : Nat) := ShiTMSubroutine.run (machine d k)
def cfg {d : Nat} (l : Label d) (v : State) (xs tmp ctr fuel : List Bool) :
    Cfg Gam (Label d) State := ⟨some l, v, storeFn xs tmp ctr fuel⟩

theorem init_step (d k : Nat) (xs : List Bool) :
    run d k (some (cfg init none xs [] [] [])) =
      some (cfg (stage ⟨d, Nat.lt_succ_self d⟩ .outer) none
        xs [] (List.replicate k true) []) := by
  simp [run, ShiTMSubroutine.run, cfg, init, stage, machine, step, stepAux,
    stepAux_pushCounter]

theorem stage_run (d k : Nat) (i : Fin (d + 1)) (m : Nat)
    (xs : List Bool) (v : State) :
    (run d k)^[m * (2 * xs.length + 3) + 1]
      (some (cfg (stage i .outer) v xs [] (List.replicate m true) [])) =
      some (cfg (stage i .done) none xs [] []
        (List.replicate (m * (xs.length + 1)) true)) := by
  have h := ShiTMSubroutine.run_to_terminal
    (ShiTMFuel.machine 1) (machine d k) (stage i) .done rfl
    (by intro l hl; cases l <;> first | rfl | exact (hl rfl).elim)
    (m * (2 * xs.length + 3) + 1) _ _ rfl
    (ShiTMFuel.outer_run 1 m xs [] v)
  simpa only [Nat.one_mul, List.append_nil, Option.map_some,
    ShiTMSubroutine.cfg, ShiTMFuel.cfg, cfg] using h

theorem transfer_cons (d k : Nat) (i : Fin (d + 1))
    (v : State) (b : Bool) (xs ctr fuel : List Bool) :
    run d k (some (cfg (transfer i) v xs [] ctr (b :: fuel))) =
      some (cfg (transfer i) (some b) xs [] (true :: ctr) fuel) := by
  simp [run, ShiTMSubroutine.run, cfg, transfer, machine, step, stepAux]

theorem transfer_nil (d k : Nat) (i : Fin (d + 1))
    (v : State) (xs ctr : List Bool) :
    run d k (some (cfg (transfer i) v xs [] ctr [])) =
      some (cfg (stage (previous i) .outer) none xs [] ctr []) := by
  simp [run, ShiTMSubroutine.run, cfg, transfer, machine, step, stepAux]

theorem transfer_run (d k : Nat) (i : Fin (d + 1))
    (fuel xs ctr : List Bool) (v : State) :
    (run d k)^[fuel.length + 1]
      (some (cfg (transfer i) v xs [] ctr fuel)) =
      some (cfg (stage (previous i) .outer) none xs []
        (List.replicate fuel.length true ++ ctr) []) := by
  induction fuel generalizing ctr v with
  | nil => simpa using transfer_nil d k i v xs ctr
  | cons b fuel ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        transfer_cons, ih]
      congr 2
      simp [List.replicate_succ', List.append_assoc]

end ShiTMPolynomialFuel
