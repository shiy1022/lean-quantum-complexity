import «AMPUNI-global-depth-header»
import «AMPUNI-fanout-stage-bounds»
import «AMPUNI-subroutine-full-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMGlobalFanoutPrefix
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOuterLift

abbrev Label := Bool ⊕ ShiTMFanoutStage.Label
abbrev source : TopK := .inl ShiTMGlobalDepthHeader.source
abbrev counter : TopK := .inl ShiTMGlobalDepthHeader.counter
abbrev output : TopK := ShiTMFanoutStage.output
abbrev scratch : TopK := ShiTMFanoutPrepare.scratch

def headerMachine : Bool → Stmt TopGam Bool Sig :=
  ShiTMTopFrame.machine ShiTMGlobalDepthHeader.machine

def machine : Label → Stmt TopGam Label Sig
  | .inl true => .goto (fun _ => .inr (ShiTMFanoutStage.prepLabel false (.clear 0)))
  | .inl false => ShiTMSubroutine.stmt Sum.inl (headerMachine false)
  | .inr l => ShiTMSubroutine.stmt Sum.inr (ShiTMFanoutStage.machine l)

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := source
  k₁ := output
  Γ := TopGam
  Λ := Label
  main := .inl false
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

theorem header_run (d : Nat) (rest : List Cell) (v : Sig)
    (S : ∀ j, List (TopGam j))
    (hs : S source = (List.replicate d true ++ [false]).map bit ++ rest) :
    ∃ U : ∀ j, List (TopGam j),
      run^[d+1] (some ⟨some (.inl false), v, S⟩) =
        some ⟨some (.inl true), some Cell.delim, U⟩
      ∧ U source = rest
      ∧ U counter = List.replicate d Cell.mark ++ S counter
      ∧ U output = ((List.replicate (3*d+113) true ++ [false]).map bit).reverse ++ S output
      ∧ ∀ j, j ≠ source → j ≠ counter → j ≠ output → U j = S j := by
  let O : ∀ k, List (OuterGam k) := fun k => S (.inl k)
  let H : Fin 4 → List Cell := fun h => S (.inr h)
  have hS : topStacks O H = S := by funext j; cases j <;> rfl
  obtain ⟨V, hr, hvs, hvc, hvo, hvf⟩ := ShiTMGlobalDepthHeader.global_header_run d rest v O hs
  let U := topStacks V H
  have ht := ShiTMTopFrame.run_iter_frame ShiTMGlobalDepthHeader.machine H (d+1)
    (some ⟨some false, v, O⟩)
  change (ShiTMSubroutine.run headerMachine)^[d+1]
      (some ⟨some false, v, topStacks O H⟩) =
      (ShiTMGlobalDepthHeader.run^[d+1]
        (some ⟨some false, v, O⟩)).map (ShiTMTopFrame.cfg H) at ht
  rw [hr, hS] at ht
  have hl := ShiTMSubroutine.run_to_terminal headerMachine machine Sum.inl true rfl
    (by intro b hb; cases b <;> simp_all [machine]) (d+1)
    (some ⟨some false, v, S⟩) ⟨some true, some Cell.delim, U⟩ rfl ht
  refine ⟨U, ?_, hvs, hvc, ?_, ?_⟩
  · simpa only [run, ShiTMSubroutine.cfg, Option.map_some] using hl
  · exact hvo.trans (ShiTMGlobalDepthHeader.global_header_bytes d (O ShiTMGlobalDepthHeader.output))
  · intro j hjs hjc hjo
    cases j with
    | inl k => exact hvf k (by simpa using hjs) (by simpa using hjc) (by simpa using hjo)
    | inr h => rfl

/-- Direct output prefix: consume the old depth once, emit the amplified
header and both fanout layers, and retain the original depth counter for
entry into the first copy's layer loop. -/
theorem prefix_run (n w a d : Nat) (rest : List Cell) (v : Sig)
    (S : ∀ j, List (TopGam j)) (hret : ShiTMFanoutPrepare.Retained n w a S)
    (hs : S source = (List.replicate d true ++ [false]).map bit ++ rest)
    (ht : S scratch = []) :
    ∃ U : ∀ j, List (TopGam j),
      run^[d+2+ShiTMFanoutStage.stageCost n w a S]
        (some ⟨some (.inl false), v, S⟩) =
        some ⟨some (.inr ShiTMFanoutStage.finished), none, U⟩
      ∧ U source = rest
      ∧ U counter = List.replicate d Cell.mark ++ S counter
      ∧ U output =
        (((List.replicate (3*d+113) true ++ [false]).map bit) ++
          ShiTMFanoutStage.payload false n w a ++ ShiTMFanoutStage.payload true n w a).reverse ++ S output
      ∧ U (ShiTMFanoutPrepare.port 0) = []
      ∧ U (ShiTMFanoutPrepare.port 1) = []
      ∧ U (ShiTMFanoutPrepare.port 2) = []
      ∧ U scratch = []
      ∧ ShiTMFanoutPrepare.Retained n w a U
      ∧ ∀ j, ShiTMFanoutStage.Stable j → j ≠ source → j ≠ counter → U j = S j := by
  obtain ⟨T, hh, hts, htc, hto, htf⟩ := header_run d rest v S hs
  have hretT : ShiTMFanoutPrepare.Retained n w a T :=
    ShiTMFanoutPrepare.retained_frame hret
      (fun h => htf (ShiTMFanoutPrepare.source h) (by simp) (by simp) (by simp))
  have htT : T scratch = [] := (htf scratch (by decide) (by decide) (by decide)).trans ht
  have hhandoff : run^[1] (some ⟨some (.inl true), some Cell.delim, T⟩) =
      some ⟨some (.inr (ShiTMFanoutStage.prepLabel false (.clear 0))), some Cell.delim, T⟩ := by rfl
  obtain ⟨U, hr, h0, h1, h2, huT, huo, hretU, huf⟩ :=
    ShiTMFanoutStage.stage_run n w a (some Cell.delim) T hretT htT
  have hl := ShiTMSubroutine.run_iter_lift ShiTMFanoutStage.machine machine Sum.inr
    (by intro l; rfl) (ShiTMFanoutStage.stageCost n w a T)
    (some ⟨some (ShiTMFanoutStage.prepLabel false (.clear 0)), some Cell.delim, T⟩)
  change run^[ShiTMFanoutStage.stageCost n w a T]
      (some ⟨some (.inr (ShiTMFanoutStage.prepLabel false (.clear 0))), some Cell.delim, T⟩) =
      (ShiTMFanoutStage.run^[ShiTMFanoutStage.stageCost n w a T]
        (some ⟨some (ShiTMFanoutStage.prepLabel false (.clear 0)), some Cell.delim, T⟩)).map
          (ShiTMSubroutine.cfg Sum.inr) at hl
  rw [hr] at hl
  have hc : ShiTMFanoutStage.stageCost n w a T = ShiTMFanoutStage.stageCost n w a S := by
    simp only [ShiTMFanoutStage.stageCost, ShiTMFanoutStage.blockCost,
      ShiTMFanoutPrepare.cost, ShiTMFanoutPrepare.clearCost]
    rw [htf (ShiTMFanoutPrepare.port 0) (by decide) (by decide) (by decide),
      htf (ShiTMFanoutPrepare.port 1) (by decide) (by decide) (by decide),
      htf (ShiTMFanoutPrepare.port 2) (by decide) (by decide) (by decide)]
  simp only [Option.map_some, ShiTMSubroutine.cfg, Option.map_some, hc] at hl
  refine ⟨U, ?_, ?_, ?_, ?_, h0, h1, h2, huT, hretU, ?_⟩
  · have h1 := ShiTMFanout.iterTwo run _ _ _ _ _ hh hhandoff
    have h2 := ShiTMFanout.iterTwo run _ _ _ _ _ h1 hl
    simpa only [show d+1+1 = d+2 by omega] using h2
  · rw [huf source (by simp [ShiTMFanoutStage.Stable, ShiTMFanoutPrepare.Stable]), hts]
  · rw [huf counter (by simp [ShiTMFanoutStage.Stable, ShiTMFanoutPrepare.Stable]), htc]
  · rw [huo, hto]
    simp [List.reverse_append, List.append_assoc]
  · intro j hj hjs hjc
    rw [huf j hj, htf j hjs hjc hj.2]

end ShiTMGlobalFanoutPrefix
