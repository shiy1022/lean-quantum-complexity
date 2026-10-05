import «BQP-unary-parser»
import «BQP-unary-block-runs»
import «BQP-stack-embedding»
import «BQP-halt-routing-run»
import «AMPUNI-subroutine-full-lift»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPOneGate
open Turing Turing.TM2
abbrev K := Fin 4
abbrev Gam : K → Type := fun _ => Bool
abbrev Label := Option Bool

def parserMap : Fin 2 ↪ K where
  toFun i := ⟨i.val, by omega⟩
  inj' := by intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 4 => k.val) h

def emitterMap : Fin 3 ↪ K where
  toFun i := ⟨i.val+1, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; simp only at this; omega

def program (body : List ℕ) : Label → Stmt Gam Label Bool
  | none => ShiTMHaltRouting.stmt (fun _ : Unit => none) (some false)
      (BQPStackEmbedding.stmt parserMap (BQPUnaryParser.program ()))
  | some l => ShiTMSubroutine.stmt some
      (BQPStackEmbedding.stmt emitterMap (BQPUnaryBlock.program body l))

def tapes (s a b out : List Bool) : K → List Bool :=
  fun k => if k = 0 then s else if k = 1 then a else if k = 2 then b else out

def cfg (l : Label) (v : Bool) (s a b out : List Bool) : Cfg Gam Label Bool :=
  ⟨some l,v,tapes s a b out⟩

theorem parser_stacks (s a b out : List Bool) :
    Function.extend parserMap (BQPUnaryParser.tapes s a) (tapes [] [] b out) = tapes s a b out := by
  funext k
  fin_cases k
  · change Function.extend parserMap (BQPUnaryParser.tapes s a) (tapes [] [] b out) (parserMap 0) =
      BQPUnaryParser.tapes s a 0
    exact parserMap.injective.extend_apply _ _ _
  · change Function.extend parserMap (BQPUnaryParser.tapes s a) (tapes [] [] b out) (parserMap 1) =
      BQPUnaryParser.tapes s a 1
    exact parserMap.injective.extend_apply _ _ _
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩
      have he : i.val = 2 := congrArg (fun k : Fin 4 => k.val) h
      omega)]
    rfl
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩
      have he : i.val = 3 := congrArg (fun k : Fin 4 => k.val) h
      omega)]
    rfl

theorem emitter_stacks (s a b out : List Bool) :
    Function.extend emitterMap (BQPUnaryBlock.tapes a b out) (tapes s [] [] []) = tapes s a b out := by
  funext k
  fin_cases k
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i,h⟩
      have he : i.val+1 = 0 := congrArg (fun k : Fin 4 => k.val) h
      omega)]
    rfl
  · change Function.extend emitterMap (BQPUnaryBlock.tapes a b out) (tapes s [] [] []) (emitterMap 0) =
      BQPUnaryBlock.tapes a b out 0
    exact emitterMap.injective.extend_apply _ _ _
  · change Function.extend emitterMap (BQPUnaryBlock.tapes a b out) (tapes s [] [] []) (emitterMap 1) =
      BQPUnaryBlock.tapes a b out 1
    exact emitterMap.injective.extend_apply _ _ _
  · change Function.extend emitterMap (BQPUnaryBlock.tapes a b out) (tapes s [] [] []) (emitterMap 2) =
      BQPUnaryBlock.tapes a b out 2
    exact emitterMap.injective.extend_apply _ _ _

theorem parser_run (body : List ℕ) (n : ℕ) (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run (program body))^[n+1]
      (some (cfg none v (List.replicate n true ++ false::s) [] [] out)) =
    some (cfg (some false) false s (List.replicate n true) [] out) := by
  let c := BQPUnaryParser.cfg v (List.replicate n true ++ false::s) []
  let d : Cfg BQPUnaryParser.Gam Unit Bool :=
    ⟨none,false,BQPUnaryParser.tapes s (List.replicate n true)⟩
  have hp : (ShiTMSubroutine.run BQPUnaryParser.program)^[n+1] (some c) = some d := by
    simpa only [List.append_nil] using BQPUnaryParser.parse_run n v s []
  have he := (BQPStackEmbedding.run_iter parserMap (tapes [] [] [] out)
    BQPUnaryParser.program (n+1) (some c)).trans
      (congrArg (Option.map (BQPStackEmbedding.cfg parserMap (tapes [] [] [] out))) hp)
  have hr := ShiTMHaltRouting.run_to_some
    (BQPStackEmbedding.machine parserMap BQPUnaryParser.program) (program body)
    (fun _ : Unit => none) (some false) (fun _ => rfl) (n+1)
    (some (BQPStackEmbedding.cfg parserMap (tapes [] [] [] out) c))
    (BQPStackEmbedding.cfg parserMap (tapes [] [] [] out) d) he
  simpa only [Option.map_some, BQPStackEmbedding.cfg, ShiTMHaltRouting.cfg, c, d,
    BQPUnaryParser.cfg, parser_stacks, Option.elim_some, Option.elim_none, cfg] using hr

theorem emitter_run (body : List ℕ) (a s out : List Bool) (v : Bool) :
    (ShiTMSubroutine.run (program body))^[2*a.length+2]
      (some (cfg (some false) v s a [] out)) =
    some (⟨none,false,tapes s [] []
      (BQPOpcodeEmission.encode (List.replicate a.length 1 ++
        (body ++ List.replicate a.length 0)) ++ out)⟩ : Cfg Gam Label Bool) := by
  let c := BQPUnaryBlock.cfg false v a [] out
  let d : Cfg BQPUnaryBlock.Gam Bool Bool := ⟨none,false,BQPUnaryBlock.tapes [] []
    (BQPOpcodeEmission.encode (List.replicate a.length 1 ++
      (body ++ List.replicate a.length 0)) ++ out)⟩
  have hp : (ShiTMSubroutine.run (BQPUnaryBlock.program body))^[2*a.length+2] (some c) = some d :=
    BQPUnaryBlock.block_run body a out v
  have he := (BQPStackEmbedding.run_iter emitterMap (tapes s [] [] [])
    (BQPUnaryBlock.program body) (2*a.length+2) (some c)).trans
      (congrArg (Option.map (BQPStackEmbedding.cfg emitterMap (tapes s [] [] []))) hp)
  have hr := (ShiTMSubroutine.run_iter_lift
    (BQPStackEmbedding.machine emitterMap (BQPUnaryBlock.program body)) (program body)
    some (fun _ => rfl) (2*a.length+2)
    (some (BQPStackEmbedding.cfg emitterMap (tapes s [] [] []) c))).trans
      (congrArg (Option.map (ShiTMSubroutine.cfg some)) he)
  simpa only [Option.map_some, BQPStackEmbedding.cfg, ShiTMSubroutine.cfg, c, d,
    BQPUnaryBlock.cfg, emitter_stacks, Option.map_none, cfg] using hr

/-- Parse one unary wire index and emit its fixed-body opcode block, preserving
all remaining input and the prior output. No parser/counter hypothesis remains. -/
theorem parse_emit_run (body : List ℕ) (n : ℕ) (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run (program body))^[3*n+3]
      (some (cfg none v (List.replicate n true ++ false::s) [] [] out)) =
    some (⟨none,false,tapes s [] []
      (BQPOpcodeEmission.encode (List.replicate n 1 ++ (body ++ List.replicate n 0)) ++ out)⟩ :
      Cfg Gam Label Bool) := by
  have he := emitter_run body (List.replicate n true) s out false
  simp only [List.length_replicate] at he
  rw [show 3*n+3 = (2*n+2)+(n+1) by omega,
    Function.iterate_add_apply, parser_run]
  exact he

end BQPOneGate
