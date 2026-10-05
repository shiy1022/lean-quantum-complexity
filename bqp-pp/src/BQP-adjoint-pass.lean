import «BQP-archive-pass»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPAdjointPass
open Turing Turing.TM2 ShiShallow
abbrev K := BQPCounted.Key BQPArchivePass.K
abbrev Label := BQPArchive.Label BQPArchivePass.Label
abbrev Gam : K → Type := fun _ => Bool

def outputKey : BQPArchivePass.K := .inl (.inl (.inr ()))
def program : Label → Stmt Gam Label Bool := BQPArchive.program outputKey BQPArchivePass.program
def layout (s out : List Bool) : K → List Bool := BQPCounted.extend (BQPArchivePass.layout s []) out

def cost (C : BQPProgram.Checker) {n : ℕ} (c : Layered n) : ℕ :=
  BQPArchivePass.cost C c + (BQPArchivePass.emitted C c).length + 1

/-- A complete concrete adjoint pass. A forward traversal archives each adjoint
block; the final drain restores precisely the required reversed gate order. -/
theorem adjoint_run (C : BQPProgram.Checker) {n : ℕ} (c : Layered n)
    (v : Bool) (s out : List Bool) :
    (ShiTMSubroutine.run program)^[cost C c]
      (some (⟨some (some none),v,layout (ShiBQP.encCirc c ++ s) out⟩ : Cfg Gam Label Bool)) =
    some (⟨none,false,layout s (C.encode (BQPProgram.adjointBody c.flatten) ++ out)⟩ : Cfg Gam Label Bool) := by
  have hc := BQPArchivePass.circuit_run C c v s []
  simp only [List.append_nil] at hc
  have hr := BQPArchive.body_archive_run outputKey BQPArchivePass.program none
    (BQPArchivePass.cost C c) v false
    (BQPArchivePass.layout (ShiBQP.encCirc c ++ s) [])
    (BQPArchivePass.layout s []) out (BQPArchivePass.emitted C c)
    (by simpa only [outputKey, BQPArchivePass.update_archive] using hc)
  simpa only [program, cost, layout, BQPArchive.cfg, outputKey,
    BQPArchivePass.update_archive, BQPArchivePass.emitted_eq, List.reverse_reverse] using hr

theorem archive_length_le_cost (C : BQPProgram.Checker) {n : ℕ} (c : Layered n) :
    (BQPArchivePass.emitted C c).length ≤ BQPArchivePass.cost C c := by
  have hl : ∀ gs : List (Instr n), (BQPArchivePass.layerEmitted C gs).length ≤
      BQPArchivePass.layerCost C gs := by
    intro gs
    have hb : (gs.reverse.map (BQPArchiveGate.emitted C)).flatten.length ≤
        (gs.map (BQPArchiveGate.cost C)).sum := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
          have hg : (BQPArchiveGate.emitted C g).length ≤ BQPArchiveGate.cost C g := by
            simp only [BQPArchiveGate.cost]; omega
          simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
            List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
            List.length_append, List.sum_cons]
          omega
    dsimp only [BQPArchivePass.layerEmitted, BQPArchivePass.layerCost]
    omega
  have hb : (c.reverse.map (BQPArchivePass.layerEmitted C)).flatten.length ≤
      (c.map (BQPArchivePass.layerCost C)).sum := by
    induction c with
    | nil => simp
    | cons l c ih =>
        have h := hl l
        simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
          List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.length_append, List.sum_cons]
        omega
  dsimp only [BQPArchivePass.emitted, BQPArchivePass.cost]
  omega

/-- The archive and its final drain have an input-length linear clock. -/
theorem cost_le (C : BQPProgram.Checker) {n : ℕ} (c : Layered n) :
    cost C c ≤ 64*(ShiBQP.encCirc c).length+1 := by
  have hc := BQPArchivePass.cost_le C c
  have hl := archive_length_le_cost C c
  dsimp only [cost]
  omega

end BQPAdjointPass
