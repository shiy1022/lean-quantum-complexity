import «AMPUNI-top-stack-frame»
import «AMPUNI-subroutine-lift»
import «AMPUNI-payload-normalizer»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open ShiShallow Turing Turing.TM2
namespace ShiTMRetainedPayload
open ShiTMLayoutMachine ShiTMOuterLift ShiTMRetainedTop
abbrev Label := ShiTMPayload.PayloadLabel

def machine : Label → Stmt TopGam Label Sig :=
  ShiTMTopFrame.machine ShiTMPayload.machine

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  ShiTMSubroutine.run machine

def finiteMachine : Turing.FinTM2 where
  K := TopK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := .inl (.inl (11 : Fin 14))
  k₁ := .inl (.inl (13 : Fin 14))
  Γ := TopGam
  Λ := Label
  main := none
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

/-- The payload-only parser preserves all four retained stacks, including
its original output index and archived verifier, with the same exact cost. -/
theorem typed_circuit_run_zero (ps : List (Nat × Nat)) {m : Nat}
    (hfit : m ≤ (ps.map Prod.fst).sum) (c : Layered m)
    (rest : List Cell) (pa ta pb tb : List Cell) (v : Sig)
    (S : ∀ k, List (Gam k)) (C : Fin 2 → List Cell)
    (H : Fin 4 → List Cell)
    (hSsrc : S 11 = (ShiBQP.encCirc c).map bit ++ rest)
    (hC0 : C 0 = []) (hC1 : C 1 = [])
    (hS0 : S 0 = []) (hS1 : S 1 = pieceCells Prod.fst ps)
    (hS2 : S 2 = pieceCells Prod.snd ps) (hS3 : S 3 = [])
    (hS4 : S 4 = [.delim]) (hS6 : S 6 = []) (hS7 : S 7 = [])
    (hS8 : S 8 = pa ++ .mirrorEnd :: ta)
    (hS9 : S 9 = pb ++ .mirrorEnd :: tb) (hS10 : S 10 = [])
    (hS12 : S 12 = [])
    (hpa : pa.reverse = pieceCells Prod.fst ps)
    (hpb : pb.reverse = pieceCells Prod.snd ps)
    (hpaGood : ∀ y ∈ pa, y ≠ .mirrorEnd)
    (hpbGood : ∀ y ∈ pb, y ≠ .mirrorEnd) :
    ∃ (U : ∀ k, List (Gam k)) (D : Fin 2 → List Cell),
      run^[(c.length + 1) + layerListCost pa pb
        (typedLayers ps 0 (by simpa using hfit) c)]
        (some { l := some none, var := v, stk := topStacks (liftStacks S C) H }) =
          some { l := some (some (.inr .exit)), var := none, stk := topStacks (liftStacks U D) H }
      ∧ D 0 = [] ∧ D 1 = []
      ∧ U 13 = ((((ShiTMRawLayout.mapCirc depth ps 0
            (c.map (List.map ShiTMRawLayout.ofInstr))).map
              ShiTMRawLayout.encodeLayer).flatten).map bit).reverse ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = []
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  obtain ⟨U, D, hr, hD0, hD1, hacc, h6, h7, h11, h12,
    h0, h1, h2, h3, h4, h8, h9, h10⟩ :=
    ShiTMPayload.payload_typed_circuit_run_zero ps hfit c rest pa ta pb tb v S C
      hSsrc hC0 hC1 hS0 hS1 hS2 hS3 hS4 hS6 hS7
      hS8 hS9 hS10 hS12 hpa hpb hpaGood hpbGood
  refine ⟨U, D, ?_, hD0, hD1, hacc, h6, h7, h11, h12,
    h0, h1, h2, h3, h4, h8, h9, h10⟩
  have h := ShiTMTopFrame.run_iter_frame ShiTMPayload.machine H
    ((c.length + 1) + layerListCost pa pb
      (typedLayers ps 0 (by simpa using hfit) c))
    (some ⟨some none, v, liftStacks S C⟩)
  change run^[_] _ = (ShiTMPayload.run^[_] _).map (ShiTMTopFrame.cfg H) at h
  rw [hr] at h
  exact h

end ShiTMRetainedPayload
