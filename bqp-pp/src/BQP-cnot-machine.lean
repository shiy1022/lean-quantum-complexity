import «BQP-unary-compare»
import «BQP-nested-block-runs»
import «BQP-stack-embedding»
import «BQP-halt-routing-run»
import «AMPUNI-subroutine-full-lift»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPCnot
open Turing Turing.TM2
abbrev K := Fin 6
abbrev Gam : K → Type := fun _ => Bool
inductive Label
  | compare | choose | less (l : Fin 4) | greater (l : Fin 4)
  deriving DecidableEq

def compareMap : Fin 3 ↪ K where
  toFun i := ⟨i.val, by omega⟩
  inj' := by intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 6 => k.val) h

def lessMap : Fin 5 ↪ K where
  toFun i := if i = 0 then 2 else if i = 1 then 1 else if i = 2 then 3 else if i = 3 then 4 else 5
  inj' := by decide

def greaterMap : Fin 5 ↪ K where
  toFun i := if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 3 else if i = 3 then 4 else 5
  inj' := by decide

def program : Label → Stmt Gam Label Bool
  | .compare => ShiTMHaltRouting.stmt (fun _ : Unit => .compare) .choose
      (BQPStackEmbedding.stmt compareMap (BQPUnaryCompare.program ()))
  | .choose => .goto (fun v => if v then .greater 0 else .less 0)
  | .less l => ShiTMSubroutine.stmt Label.less
      (BQPStackEmbedding.stmt lessMap (BQPNestedBlock.program [6] [7] [] l))
  | .greater l => ShiTMSubroutine.stmt Label.greater
      (BQPStackEmbedding.stmt greaterMap (BQPNestedBlock.program [] [6] [7] l))

def tapes (a b c d e out : List Bool) : K → List Bool :=
  fun k => if k = 0 then a else if k = 1 then b else if k = 2 then c else
    if k = 3 then d else if k = 4 then e else out

def cfg (l : Label) (v : Bool) (a b c d e out : List Bool) : Cfg Gam Label Bool :=
  ⟨some l,v,tapes a b c d e out⟩

theorem compare_stacks (a b c d e out : List Bool) :
    Function.extend compareMap (BQPUnaryCompare.tapes a b c) (tapes [] [] [] d e out) =
      tapes a b c d e out := by
  funext k
  fin_cases k
  · change Function.extend compareMap (BQPUnaryCompare.tapes a b c) (tapes [] [] [] d e out) (compareMap 0) =
      BQPUnaryCompare.tapes a b c 0
    exact compareMap.injective.extend_apply _ _ _
  · change Function.extend compareMap (BQPUnaryCompare.tapes a b c) (tapes [] [] [] d e out) (compareMap 1) =
      BQPUnaryCompare.tapes a b c 1
    exact compareMap.injective.extend_apply _ _ _
  · change Function.extend compareMap (BQPUnaryCompare.tapes a b c) (tapes [] [] [] d e out) (compareMap 2) =
      BQPUnaryCompare.tapes a b c 2
    exact compareMap.injective.extend_apply _ _ _
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩
      have he : i.val = 3 := congrArg (fun k : Fin 6 => k.val) h
      omega)]
    rfl
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩
      have he : i.val = 4 := congrArg (fun k : Fin 6 => k.val) h
      omega)]
    rfl
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩
      have he : i.val = 5 := congrArg (fun k : Fin 6 => k.val) h
      omega)]
    rfl

theorem less_stacks (a b c d out : List Bool) :
    Function.extend lessMap (BQPNestedBlock.tapes a b c d out) (fun _ => []) =
      tapes [] b a c d out := by
  funext k
  fin_cases k
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 5, lessMap i ≠ 0) i h)]
    rfl
  · change Function.extend lessMap (BQPNestedBlock.tapes a b c d out) (fun _ => []) (lessMap 1) =
      BQPNestedBlock.tapes a b c d out 1
    exact lessMap.injective.extend_apply _ _ _
  · change Function.extend lessMap (BQPNestedBlock.tapes a b c d out) (fun _ => []) (lessMap 0) =
      BQPNestedBlock.tapes a b c d out 0
    exact lessMap.injective.extend_apply _ _ _
  · change Function.extend lessMap (BQPNestedBlock.tapes a b c d out) (fun _ => []) (lessMap 2) =
      BQPNestedBlock.tapes a b c d out 2
    exact lessMap.injective.extend_apply _ _ _
  · change Function.extend lessMap (BQPNestedBlock.tapes a b c d out) (fun _ => []) (lessMap 3) =
      BQPNestedBlock.tapes a b c d out 3
    exact lessMap.injective.extend_apply _ _ _
  · change Function.extend lessMap (BQPNestedBlock.tapes a b c d out) (fun _ => []) (lessMap 4) =
      BQPNestedBlock.tapes a b c d out 4
    exact lessMap.injective.extend_apply _ _ _

theorem greater_stacks (a b c d out : List Bool) :
    Function.extend greaterMap (BQPNestedBlock.tapes a b c d out) (fun _ => []) =
      tapes b [] a c d out := by
  funext k
  fin_cases k
  · change Function.extend greaterMap (BQPNestedBlock.tapes a b c d out) (fun _ => []) (greaterMap 1) =
      BQPNestedBlock.tapes a b c d out 1
    exact greaterMap.injective.extend_apply _ _ _
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 5, greaterMap i ≠ 1) i h)]
    rfl
  · change Function.extend greaterMap (BQPNestedBlock.tapes a b c d out) (fun _ => []) (greaterMap 0) =
      BQPNestedBlock.tapes a b c d out 0
    exact greaterMap.injective.extend_apply _ _ _
  · change Function.extend greaterMap (BQPNestedBlock.tapes a b c d out) (fun _ => []) (greaterMap 2) =
      BQPNestedBlock.tapes a b c d out 2
    exact greaterMap.injective.extend_apply _ _ _
  · change Function.extend greaterMap (BQPNestedBlock.tapes a b c d out) (fun _ => []) (greaterMap 3) =
      BQPNestedBlock.tapes a b c d out 3
    exact greaterMap.injective.extend_apply _ _ _
  · change Function.extend greaterMap (BQPNestedBlock.tapes a b c d out) (fun _ => []) (greaterMap 4) =
      BQPNestedBlock.tapes a b c d out 4
    exact greaterMap.injective.extend_apply _ _ _

theorem compare_run (i j : ℕ) (v : Bool) (out : List Bool) :
    (ShiTMSubroutine.run program)^[min i j+1]
      (some (cfg .compare v (List.replicate i true) (List.replicate j true) [] [] [] out)) =
    some (cfg .choose (decide (j < i)) (List.replicate (i-j) true) (List.replicate (j-i) true)
      (List.replicate (min i j) true) [] [] out) := by
  let c := BQPUnaryCompare.cfg v (List.replicate i true) (List.replicate j true) []
  let d : Cfg BQPUnaryCompare.Gam Unit Bool := ⟨none,decide (j < i),
    BQPUnaryCompare.tapes (List.replicate (i-j) true) (List.replicate (j-i) true)
      (List.replicate (min i j) true)⟩
  have hp : (ShiTMSubroutine.run BQPUnaryCompare.program)^[min i j+1] (some c) = some d := by
    simpa only [List.append_nil] using BQPUnaryCompare.compare_run i j v []
  have he := (BQPStackEmbedding.run_iter compareMap (tapes [] [] [] [] [] out)
    BQPUnaryCompare.program (min i j+1) (some c)).trans
      (congrArg (Option.map (BQPStackEmbedding.cfg compareMap (tapes [] [] [] [] [] out))) hp)
  have hr := ShiTMHaltRouting.run_to_some
    (BQPStackEmbedding.machine compareMap BQPUnaryCompare.program) program
    (fun _ : Unit => Label.compare) Label.choose (fun _ => rfl) (min i j+1)
    (some (BQPStackEmbedding.cfg compareMap (tapes [] [] [] [] [] out) c))
    (BQPStackEmbedding.cfg compareMap (tapes [] [] [] [] [] out) d) he
  simpa only [Option.map_some, BQPStackEmbedding.cfg, ShiTMHaltRouting.cfg, c, d,
    BQPUnaryCompare.cfg, compare_stacks, Option.elim_some, Option.elim_none, cfg] using hr

theorem less_run (a b out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run program)^[2*a.length+2*b.length+4]
      (some (cfg (.less 0) v [] b a [] [] out)) =
    some (⟨none,false,tapes [] [] [] [] []
      (BQPOpcodeEmission.encode (BQPNestedBlock.block a.length b.length [6] [7] []) ++ out)⟩ :
      Cfg Gam Label Bool) := by
  let c := BQPNestedBlock.cfg 0 v a b [] [] out
  let d : Cfg BQPNestedBlock.Gam BQPNestedBlock.Label Bool := ⟨none,false,
    BQPNestedBlock.tapes [] [] [] []
      (BQPOpcodeEmission.encode (BQPNestedBlock.block a.length b.length [6] [7] []) ++ out)⟩
  have hp : (ShiTMSubroutine.run (BQPNestedBlock.program [6] [7] []))^[2*a.length+2*b.length+4]
      (some c) = some d := BQPNestedBlock.block_run [6] [7] [] a b out v
  have he := (BQPStackEmbedding.run_iter lessMap (fun _ => [])
    (BQPNestedBlock.program [6] [7] []) (2*a.length+2*b.length+4) (some c)).trans
      (congrArg (Option.map (BQPStackEmbedding.cfg lessMap (fun _ => []))) hp)
  have hr := (ShiTMSubroutine.run_iter_lift
    (BQPStackEmbedding.machine lessMap (BQPNestedBlock.program [6] [7] [])) program
    Label.less (fun _ => rfl) (2*a.length+2*b.length+4)
    (some (BQPStackEmbedding.cfg lessMap (fun _ => []) c))).trans
      (congrArg (Option.map (ShiTMSubroutine.cfg Label.less)) he)
  simpa only [Option.map_some, BQPStackEmbedding.cfg, ShiTMSubroutine.cfg, c, d,
    BQPNestedBlock.cfg, less_stacks, Option.map_none, cfg] using hr

theorem greater_run (a b out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run program)^[2*a.length+2*b.length+4]
      (some (cfg (.greater 0) v b [] a [] [] out)) =
    some (⟨none,false,tapes [] [] [] [] []
      (BQPOpcodeEmission.encode (BQPNestedBlock.block a.length b.length [] [6] [7]) ++ out)⟩ :
      Cfg Gam Label Bool) := by
  let c := BQPNestedBlock.cfg 0 v a b [] [] out
  let d : Cfg BQPNestedBlock.Gam BQPNestedBlock.Label Bool := ⟨none,false,
    BQPNestedBlock.tapes [] [] [] []
      (BQPOpcodeEmission.encode (BQPNestedBlock.block a.length b.length [] [6] [7]) ++ out)⟩
  have hp : (ShiTMSubroutine.run (BQPNestedBlock.program [] [6] [7]))^[2*a.length+2*b.length+4]
      (some c) = some d := BQPNestedBlock.block_run [] [6] [7] a b out v
  have he := (BQPStackEmbedding.run_iter greaterMap (fun _ => [])
    (BQPNestedBlock.program [] [6] [7]) (2*a.length+2*b.length+4) (some c)).trans
      (congrArg (Option.map (BQPStackEmbedding.cfg greaterMap (fun _ => []))) hp)
  have hr := (ShiTMSubroutine.run_iter_lift
    (BQPStackEmbedding.machine greaterMap (BQPNestedBlock.program [] [6] [7])) program
    Label.greater (fun _ => rfl) (2*a.length+2*b.length+4)
    (some (BQPStackEmbedding.cfg greaterMap (fun _ => []) c))).trans
      (congrArg (Option.map (ShiTMSubroutine.cfg Label.greater)) he)
  simpa only [Option.map_some, BQPStackEmbedding.cfg, ShiTMSubroutine.cfg, c, d,
    BQPNestedBlock.cfg, greater_stacks, Option.map_none, cfg] using hr

end BQPCnot
