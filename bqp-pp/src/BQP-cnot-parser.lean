import «BQP-cnot-runs»
import «BQP-unary-parser»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPCnotParser
open Turing Turing.TM2
abbrev K := Fin 7
abbrev Gam : K → Type := fun _ => Bool
inductive Label
  | left | right | compile (l : BQPCnot.Label)
  deriving DecidableEq

instance : Fintype Label := ⟨{.left, .right} ∪ Finset.univ.image Label.compile, by
  intro l; cases l <;> simp⟩

def leftMap : Fin 2 ↪ K where
  toFun i := ⟨i.val, by omega⟩
  inj' := by intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 7 => k.val) h

def rightMap : Fin 2 ↪ K where
  toFun i := if i = 0 then 0 else 2
  inj' := by decide

def compilerMap : Fin 6 ↪ K where
  toFun i := ⟨i.val+1, by omega⟩
  inj' := by
    intro i j h; apply Fin.ext
    have he : i.val+1 = j.val+1 := congrArg (fun k : Fin 7 => k.val) h
    omega

def program : Label → Stmt Gam Label Bool
  | .left => ShiTMHaltRouting.stmt (fun _ : Unit => .left) .right
      (BQPStackEmbedding.stmt leftMap (BQPUnaryParser.program ()))
  | .right => ShiTMHaltRouting.stmt (fun _ : Unit => .right) (.compile .compare)
      (BQPStackEmbedding.stmt rightMap (BQPUnaryParser.program ()))
  | .compile l => ShiTMSubroutine.stmt Label.compile
      (BQPStackEmbedding.stmt compilerMap (BQPCnot.program l))

def tapes (s a b c d e out : List Bool) : K → List Bool :=
  fun k => if k = 0 then s else if k = 1 then a else if k = 2 then b else
    if k = 3 then c else if k = 4 then d else if k = 5 then e else out

def cfg (l : Label) (v : Bool) (s a b c d e out : List Bool) : Cfg Gam Label Bool :=
  ⟨some l,v,tapes s a b c d e out⟩

theorem left_stacks (s a b c d e out : List Bool) :
    Function.extend leftMap (BQPUnaryParser.tapes s a) (tapes [] [] b c d e out) = tapes s a b c d e out := by
  funext k
  fin_cases k
  · change Function.extend leftMap (BQPUnaryParser.tapes s a) (tapes [] [] b c d e out) (leftMap 0) = (BQPUnaryParser.tapes s a) 0
    exact leftMap.injective.extend_apply _ _ _
  · change Function.extend leftMap (BQPUnaryParser.tapes s a) (tapes [] [] b c d e out) (leftMap 1) = (BQPUnaryParser.tapes s a) 1
    exact leftMap.injective.extend_apply _ _ _
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 2, leftMap i ≠ 2) i h)]
    rfl
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 2, leftMap i ≠ 3) i h)]
    rfl
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 2, leftMap i ≠ 4) i h)]
    rfl
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 2, leftMap i ≠ 5) i h)]
    rfl
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 2, leftMap i ≠ 6) i h)]
    rfl
theorem right_stacks (s a b c d e out : List Bool) :
    Function.extend rightMap (BQPUnaryParser.tapes s b) (tapes [] a [] c d e out) = tapes s a b c d e out := by
  funext k
  fin_cases k
  · change Function.extend rightMap (BQPUnaryParser.tapes s b) (tapes [] a [] c d e out) (rightMap 0) = (BQPUnaryParser.tapes s b) 0
    exact rightMap.injective.extend_apply _ _ _
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 2, rightMap i ≠ 1) i h)]
    rfl
  · change Function.extend rightMap (BQPUnaryParser.tapes s b) (tapes [] a [] c d e out) (rightMap 1) = (BQPUnaryParser.tapes s b) 1
    exact rightMap.injective.extend_apply _ _ _
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 2, rightMap i ≠ 3) i h)]
    rfl
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 2, rightMap i ≠ 4) i h)]
    rfl
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 2, rightMap i ≠ 5) i h)]
    rfl
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 2, rightMap i ≠ 6) i h)]
    rfl

theorem compiler_stacks (s a b c d e out : List Bool) :
    Function.extend compilerMap (BQPCnot.tapes a b c d e out) (tapes s [] [] [] [] [] []) =
      tapes s a b c d e out := by
  funext k
  fin_cases k
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩
      have he : i.val+1 = 0 := congrArg (fun k : Fin 7 => k.val) h
      omega)]
    rfl
  · change Function.extend compilerMap (BQPCnot.tapes a b c d e out) (tapes s [] [] [] [] [] []) (compilerMap 0) =
      BQPCnot.tapes a b c d e out 0
    exact compilerMap.injective.extend_apply _ _ _
  · change Function.extend compilerMap (BQPCnot.tapes a b c d e out) (tapes s [] [] [] [] [] []) (compilerMap 1) =
      BQPCnot.tapes a b c d e out 1
    exact compilerMap.injective.extend_apply _ _ _
  · change Function.extend compilerMap (BQPCnot.tapes a b c d e out) (tapes s [] [] [] [] [] []) (compilerMap 2) =
      BQPCnot.tapes a b c d e out 2
    exact compilerMap.injective.extend_apply _ _ _
  · change Function.extend compilerMap (BQPCnot.tapes a b c d e out) (tapes s [] [] [] [] [] []) (compilerMap 3) =
      BQPCnot.tapes a b c d e out 3
    exact compilerMap.injective.extend_apply _ _ _
  · change Function.extend compilerMap (BQPCnot.tapes a b c d e out) (tapes s [] [] [] [] [] []) (compilerMap 4) =
      BQPCnot.tapes a b c d e out 4
    exact compilerMap.injective.extend_apply _ _ _
  · change Function.extend compilerMap (BQPCnot.tapes a b c d e out) (tapes s [] [] [] [] [] []) (compilerMap 5) =
      BQPCnot.tapes a b c d e out 5
    exact compilerMap.injective.extend_apply _ _ _

theorem left_run (n : ℕ) (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run program)^[n+1]
      (some (cfg .left v (List.replicate n true ++ false::s) [] [] [] [] [] out)) =
    some (cfg .right false s (List.replicate n true) [] [] [] [] out) := by
  let c := BQPUnaryParser.cfg v (List.replicate n true ++ false::s) []
  let d : Cfg BQPUnaryParser.Gam Unit Bool :=
    ⟨none,false,BQPUnaryParser.tapes s (List.replicate n true)⟩
  have hp : (ShiTMSubroutine.run BQPUnaryParser.program)^[n+1] (some c) = some d := by
    simpa only [List.append_nil] using BQPUnaryParser.parse_run n v s []
  have he := (BQPStackEmbedding.run_iter leftMap (tapes [] [] [] [] [] [] out)
    BQPUnaryParser.program (n+1) (some c)).trans
      (congrArg (Option.map (BQPStackEmbedding.cfg leftMap (tapes [] [] [] [] [] [] out))) hp)
  have hr := ShiTMHaltRouting.run_to_some
    (BQPStackEmbedding.machine leftMap BQPUnaryParser.program) program
    (fun _ : Unit => Label.left) .right (fun _ => rfl) (n+1)
    (some (BQPStackEmbedding.cfg leftMap (tapes [] [] [] [] [] [] out) c))
    (BQPStackEmbedding.cfg leftMap (tapes [] [] [] [] [] [] out) d) he
  simpa only [Option.map_some, BQPStackEmbedding.cfg, ShiTMHaltRouting.cfg, c, d,
    BQPUnaryParser.cfg, left_stacks, Option.elim_some, Option.elim_none, cfg] using hr

theorem right_run (n : ℕ) (v : Bool) (s out : List Bool) (a : List Bool) :
    (ShiTMSubroutine.run program)^[n+1]
      (some (cfg .right v (List.replicate n true ++ false::s) a [] [] [] [] out)) =
    some (cfg (.compile .compare) false s a (List.replicate n true) [] [] [] out) := by
  let c := BQPUnaryParser.cfg v (List.replicate n true ++ false::s) []
  let d : Cfg BQPUnaryParser.Gam Unit Bool :=
    ⟨none,false,BQPUnaryParser.tapes s (List.replicate n true)⟩
  have hp : (ShiTMSubroutine.run BQPUnaryParser.program)^[n+1] (some c) = some d := by
    simpa only [List.append_nil] using BQPUnaryParser.parse_run n v s []
  have he := (BQPStackEmbedding.run_iter rightMap (tapes [] a [] [] [] [] out)
    BQPUnaryParser.program (n+1) (some c)).trans
      (congrArg (Option.map (BQPStackEmbedding.cfg rightMap (tapes [] a [] [] [] [] out))) hp)
  have hr := ShiTMHaltRouting.run_to_some
    (BQPStackEmbedding.machine rightMap BQPUnaryParser.program) program
    (fun _ : Unit => Label.right) (.compile .compare) (fun _ => rfl) (n+1)
    (some (BQPStackEmbedding.cfg rightMap (tapes [] a [] [] [] [] out) c))
    (BQPStackEmbedding.cfg rightMap (tapes [] a [] [] [] [] out) d) he
  simpa only [Option.map_some, BQPStackEmbedding.cfg, ShiTMHaltRouting.cfg, c, d,
    BQPUnaryParser.cfg, right_stacks, Option.elim_some, Option.elim_none, cfg] using hr

/-- Reading both terminated unary operands leaves the untouched circuit suffix. -/
theorem parse_pair (i j : ℕ) (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run program)^[i+j+2]
      (some (cfg .left v (List.replicate i true ++ false::(List.replicate j true ++ false::s))
        [] [] [] [] [] out)) =
    some (cfg (.compile .compare) false s (List.replicate i true) (List.replicate j true) [] [] [] out) := by
  rw [show i+j+2 = (j+1)+(i+1) by omega, Function.iterate_add_apply, left_run]
  exact right_run j false s out (List.replicate i true)

end BQPCnotParser
