import ReversibleCertifiedLengthPhase
import ReversibleProgramTemplateListBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

noncomputable def lengthPhaseBodyTemplate (as : List (CertifiedLengthPhase R)) :
    CounterProgramTemplate (RawLengthPhaseRegister R) := listProgramTemplate (as.map CertifiedLengthPhase.program)

def lengthPhaseBodyPayload (as : List (CertifiedLengthPhase R)) (n : Nat) : List Bool :=
  ((as.reverse).map (fun a => a.payload n)).flatten

def lengthPhaseBodyLayers (as : List (CertifiedLengthPhase R)) (n : Nat) : Nat :=
  (as.map (fun a => a.layers n)).sum

theorem lengthPhaseBodyTemplate_embeds (as : List (CertifiedLengthPhase R)) :
    (lengthPhaseBodyTemplate as).Embeds := by
  apply listProgramTemplate_embeds
  intro p hp
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
  exact a.embeds

theorem lengthPhaseBodyTemplate_run (as : List (CertifiedLengthPhase R)) :
    (lengthPhaseBodyTemplate as).Runs := by
  apply listProgramTemplate_run
  · intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    exact a.embeds
  · intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    exact a.runs

theorem lengthPhaseBodyTemplate_shared (as : List (CertifiedLengthPhase R)) (cs : RawLengthPhaseRegister R → Nat) :
    (lengthPhaseBodyTemplate as).counters cs (.inl 0)=cs (.inl 0) ∧
      (lengthPhaseBodyTemplate as).counters cs (.inl 2)=cs (.inl 2) := by
  induction as generalizing cs with
  | nil => exact ⟨rfl,rfl⟩
  | cons a as ih =>
    have h := ih (a.program.counters cs)
    exact ⟨h.1.trans (a.length cs),h.2.trans (a.scratch cs)⟩

theorem lengthPhaseBodyTemplate_ready (as : List (CertifiedLengthPhase R)) (cs : RawLengthPhaseRegister R → Nat)
    (hs : cs (.inl 2)=0) : (lengthPhaseBodyTemplate as).ready cs := by
  induction as generalizing cs with
  | nil => trivial
  | cons a as ih =>
    exact ⟨a.ready cs hs,ih (a.program.counters cs) ((a.scratch cs).trans hs)⟩

theorem lengthPhaseBodyTemplate_bytes (as : List (CertifiedLengthPhase R)) (cs : RawLengthPhaseRegister R → Nat) :
    (lengthPhaseBodyTemplate as).bytes cs=lengthPhaseBodyPayload as (cs (.inl 0)) := by
  induction as generalizing cs with
  | nil => rfl
  | cons a as ih =>
    change (lengthPhaseBodyTemplate as).bytes (a.program.counters cs)++a.program.bytes cs=_
    rw [ih,a.length,a.bytes]
    simp [lengthPhaseBodyPayload,List.reverse_cons]

theorem lengthPhaseBodyTemplate_layers (as : List (CertifiedLengthPhase R)) (cs : RawLengthPhaseRegister R → Nat) :
    (lengthPhaseBodyTemplate as).counters cs (.inl 1)=cs (.inl 1)+lengthPhaseBodyLayers as (cs (.inl 0)) := by
  induction as generalizing cs with
  | nil => simp [lengthPhaseBodyTemplate,listProgramTemplate,identityProgramTemplate,lengthPhaseBodyLayers]
  | cons a as ih =>
    change (lengthPhaseBodyTemplate as).counters (a.program.counters cs) (.inl 1)=_
    rw [ih,a.total,a.length]
    simp only [lengthPhaseBodyLayers,List.map_cons,List.sum_cons]
    omega

theorem lengthPhaseBodyTemplate_private_zero (as : List (CertifiedLengthPhase R)) (cs : RawLengthPhaseRegister R → Nat)
    (hz : ∀ r,cs (.inr r)=0) : ∀ r,(lengthPhaseBodyTemplate as).counters cs (.inr r)=0 := by
  induction as generalizing cs with
  | nil => exact hz
  | cons a as ih => exact ih (a.program.counters cs) (a.privateZero cs hz)

theorem lengthPhaseBodyTemplate_resources (as : List (CertifiedLengthPhase R)) (bound : Polynomial Nat) :
    (lengthPhaseBodyTemplate as).CounterBound bound ∧ (lengthPhaseBodyTemplate as).PolynomiallyTimed bound := by
  apply listProgramTemplate_polynomial_certificate
  · intro p hp b
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    exact (a.resources b).2
  · intro p hp b
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    exact (a.resources b).1

end ShiReversibleGenerator
