import «BQP-cnot-complete-run»
import «BQP-one-gate-machine»
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPGateDispatch
open Turing Turing.TM2
abbrev K := Fin 7
abbrev Gam : K → Type := fun _ => Bool
inductive Label
  | tag (t : Fin 5)
  | one (t : Fin 4) (l : BQPOneGate.Label)
  | two (l : BQPCnotParser.Label)
  deriving DecidableEq

instance : Fintype Label := ⟨Finset.univ.image Label.tag ∪
    Finset.univ.image (fun p : Fin 4 × BQPOneGate.Label => Label.one p.1 p.2) ∪
    Finset.univ.image Label.two, by
  intro l
  cases l with
  | tag t => exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩))
  | one t l => exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(t,l),Finset.mem_univ _,rfl⟩))
  | two l => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩)⟩

/-- Each tag selects a fixed, finite opcode body. Adjoint S and T repeat their
phase instruction a fixed three or seven times. -/
def body (adj : Bool) (t : Fin 4) : List ℕ :=
  if t = 0 then [2] else if t = 1 then (if adj then [4,4,4] else [4])
  else if t = 2 then (if adj then [3,3,3,3,3,3,3] else [3]) else [5]

def oneMap : Fin 4 ↪ K where
  toFun i := if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else 6
  inj' := by decide

def entry (t : Fin 5) : Label :=
  if h : t.val < 4 then .one ⟨t.val,h⟩ none else .two .left

def program (adj : Bool) : Label → Stmt Gam Label Bool
  | .tag t => .pop 0 (fun _ a => a.getD false) (.branch id
      (if h : t.val < 4 then .goto (fun _ => .tag ⟨t.val+1,by omega⟩) else .halt)
      (.goto (fun _ => entry t)))
  | .one t l => ShiTMSubroutine.stmt (Label.one t)
      (BQPStackEmbedding.stmt oneMap (BQPOneGate.program (body adj t) l))
  | .two l => ShiTMSubroutine.stmt Label.two (BQPCnotParser.program l)

def inputStacks (s out : List Bool) : K → List Bool := BQPCnotParser.tapes s [] [] [] [] [] out

def cfg (l : Label) (v : Bool) (s out : List Bool) : Cfg Gam Label Bool :=
  ⟨some l,v,inputStacks s out⟩

@[simp] theorem input_at (s out : List Bool) : inputStacks s out 0 = s := rfl
@[simp] theorem update_input (s out r : List Bool) :
    Function.update (inputStacks s out) 0 r = inputStacks r out := by
  funext k; fin_cases k <;> simp [inputStacks, BQPCnotParser.tapes, Function.update]

/-- Tags zero through four are actually consumed by a five-state reader. -/
theorem tag_run (adj : Bool) (t : Fin 5) (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run (program adj))^[t.val+1]
      (some (cfg (.tag 0) v (List.replicate t.val true ++ false::s) out)) =
    some (cfg (entry t) false s out) := by
  fin_cases t <;>
    norm_num [Function.iterate_succ_apply, ShiTMSubroutine.run, step, stepAux,
      program, cfg, List.replicate_succ, entry]

theorem one_stacks (s a b out : List Bool) :
    Function.extend oneMap (BQPOneGate.tapes s a b out) (fun _ => []) =
      BQPCnotParser.tapes s a b [] [] [] out := by
  funext k
  fin_cases k
  · change Function.extend oneMap (BQPOneGate.tapes s a b out) (fun _ => []) (oneMap 0) = BQPOneGate.tapes s a b out 0
    exact oneMap.injective.extend_apply _ _ _
  · change Function.extend oneMap (BQPOneGate.tapes s a b out) (fun _ => []) (oneMap 1) = BQPOneGate.tapes s a b out 1
    exact oneMap.injective.extend_apply _ _ _
  · change Function.extend oneMap (BQPOneGate.tapes s a b out) (fun _ => []) (oneMap 2) = BQPOneGate.tapes s a b out 2
    exact oneMap.injective.extend_apply _ _ _
  · rw [Function.extend_apply' _ _ _ (by rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 4, oneMap i ≠ 3) i h)]; rfl
  · rw [Function.extend_apply' _ _ _ (by rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 4, oneMap i ≠ 4) i h)]; rfl
  · rw [Function.extend_apply' _ _ _ (by rintro ⟨i,h⟩; exact (by decide : ∀ i : Fin 4, oneMap i ≠ 5) i h)]; rfl
  · change Function.extend oneMap (BQPOneGate.tapes s a b out) (fun _ => []) (oneMap 3) = BQPOneGate.tapes s a b out 3
    exact oneMap.injective.extend_apply _ _ _

theorem one_run (adj : Bool) (t : Fin 4) (n : ℕ) (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run (program adj))^[3*n+3]
      (some (cfg (.one t none) v (List.replicate n true ++ false::s) out)) =
    some (⟨none,false,inputStacks s
      (BQPOpcodeEmission.encode (List.replicate n 1 ++ (body adj t ++ List.replicate n 0)) ++ out)⟩ :
      Cfg Gam Label Bool) := by
  let c := BQPOneGate.cfg none v (List.replicate n true ++ false::s) [] [] out
  let d : Cfg BQPOneGate.Gam BQPOneGate.Label Bool := ⟨none,false,BQPOneGate.tapes s [] []
    (BQPOpcodeEmission.encode (List.replicate n 1 ++ (body adj t ++ List.replicate n 0)) ++ out)⟩
  have hp : (ShiTMSubroutine.run (BQPOneGate.program (body adj t)))^[3*n+3] (some c) = some d :=
    BQPOneGate.parse_emit_run (body adj t) n v s out
  have he := (BQPStackEmbedding.run_iter oneMap (fun _ => [])
    (BQPOneGate.program (body adj t)) (3*n+3) (some c)).trans
      (congrArg (Option.map (BQPStackEmbedding.cfg oneMap (fun _ => []))) hp)
  have hr := (ShiTMSubroutine.run_iter_lift
    (BQPStackEmbedding.machine oneMap (BQPOneGate.program (body adj t))) (program adj)
    (Label.one t) (fun _ => rfl) (3*n+3)
    (some (BQPStackEmbedding.cfg oneMap (fun _ => []) c))).trans
      (congrArg (Option.map (ShiTMSubroutine.cfg (Label.one t))) he)
  simpa only [Option.map_some, BQPStackEmbedding.cfg, ShiTMSubroutine.cfg, c, d,
    BQPOneGate.cfg, one_stacks, Option.map_none, cfg, inputStacks] using hr

theorem two_run (adj : Bool) (i j : ℕ) (hne : i ≠ j) (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run (program adj))^[i+j+min i j+2*max i j+8]
      (some (cfg (.two .left) v
        (List.replicate i true ++ false::(List.replicate j true ++ false::s)) out)) =
    some (⟨none,false,inputStacks s
      (BQPOpcodeEmission.encode (BQPCnot.rendered i j) ++ out)⟩ : Cfg Gam Label Bool) := by
  have hp := BQPCnotParser.parse_emit_run i j hne v s out
  have hr := (ShiTMSubroutine.run_iter_lift BQPCnotParser.program (program adj) Label.two
    (fun _ => rfl) (i+j+min i j+2*max i j+8)
    (some (BQPCnotParser.cfg .left v
      (List.replicate i true ++ false::(List.replicate j true ++ false::s)) [] [] [] [] [] out))).trans
      (congrArg (Option.map (ShiTMSubroutine.cfg Label.two)) hp)
  simpa only [ShiTMSubroutine.cfg, BQPCnotParser.cfg, Option.map_some, Option.map_none, cfg, inputStacks] using hr

end BQPGateDispatch
