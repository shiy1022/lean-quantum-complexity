import ReversibleFamilyHeaderProgramTemplate
import ReversibleCleanHaltProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R] [Fintype R]

/-- Emit the accumulated family header, clear every generator counter, and return to the final halt. -/
noncomputable def familySerializationProgramTemplate (body : CounterProgramTemplate R)
    (anc out depth buf tmp : R) : CounterProgramTemplate R :=
  cleanHaltProgramTemplate (sequenceProgramTemplate body (familyHeaderProgramTemplate anc out depth buf tmp))

theorem familySerializationProgramTemplate_embeds (body : CounterProgramTemplate R)
    (anc out depth buf tmp : R) (he : body.Embeds) :
    (familySerializationProgramTemplate body anc out depth buf tmp).Embeds :=
  cleanHaltProgramTemplate_embeds _ (sequenceProgramTemplate_embeds _ _ he
    (familyHeaderProgramTemplate_embeds _ _ _ _ _))

theorem familySerializationProgramTemplate_run (body : CounterProgramTemplate R)
    (anc out depth buf tmp : R) (he : body.Embeds) (hr : body.Runs)
    (ha : anc ≠ buf ∧ anc ≠ tmp) (ho : out ≠ buf ∧ out ≠ tmp)
    (hd : depth ≠ buf ∧ depth ≠ tmp) (hbt : buf ≠ tmp) :
    (familySerializationProgramTemplate body anc out depth buf tmp).Runs :=
  cleanHaltProgramTemplate_run _ (sequenceProgramTemplate_embeds _ _ he
    (familyHeaderProgramTemplate_embeds _ _ _ _ _))
    (sequenceProgramTemplate_run _ _ he hr (familyHeaderProgramTemplate_run _ _ _ _ _ ha ho hd hbt))

theorem familySerializationProgramTemplate_resources (body : CounterProgramTemplate R)
    (anc out depth buf tmp : R) (bound : Polynomial Nat)
    (hb : body.CounterBound bound) (ht : body.PolynomiallyTimed bound) :
    (familySerializationProgramTemplate body anc out depth buf tmp).CounterBound bound ∧
    (familySerializationProgramTemplate body anc out depth buf tmp).PolynomiallyTimed bound := by
  obtain ⟨middle,hm⟩ := hb
  apply cleanHaltProgramTemplate_resources
  · exact ⟨middle,fun n cs hc q => hm n cs hc q⟩
  · exact sequenceProgramTemplate_polynomial _ _ bound middle ht (fun n cs hc _ => hm n cs hc)
      (familyHeaderProgramTemplate_resources anc out depth buf tmp middle).2

/-- From a checked body certificate, the fixed finite graph prints the unchanged family encoding and actually halts cleanly. -/
theorem familySerializationProgramTemplate_certificate (F : ShiClass.Family)
    (body : CounterProgramTemplate R) (anc out depth buf tmp : R)
    (he : body.Embeds) (hr : body.Runs)
    (ha : anc ≠ buf ∧ anc ≠ tmp) (ho : out ≠ buf ∧ out ≠ tmp)
    (hd : depth ≠ buf ∧ depth ≠ tmp) (hbt : buf ≠ tmp)
    (initial : Nat → R → Nat) (bound : Polynomial Nat)
    (hi : ∀ n q,initial n q ≤ bound.eval n)
    (hb : body.CounterBound bound) (ht : body.PolynomiallyTimed bound)
    (hready : ∀ n,body.ready (initial n))
    (hmetadata : ∀ n,body.counters (initial n) anc=F.anc n ∧
      body.counters (initial n) out=(F.out n).val ∧
      body.counters (initial n) depth=(F.circ n).length ∧
      body.counters (initial n) buf=0 ∧ body.counters (initial n) tmp=0)
    (hpayload : ∀ n,body.bytes (initial n)=((F.circ n).map ShiBQP.encLayer).flatten) :
    ∃ clock : Polynomial Nat,∀ n,
      let p := familySerializationProgramTemplate body anc out depth buf tmp
      CounterRun (p.code (fun _ : Unit => .halt) ()) ⟨some (p.entry ()),initial n,[]⟩
        (p.steps (initial n)+1) ⟨none,fun _ => 0,ShiBQP.encFamilyAt F n⟩ ∧
      p.steps (initial n)+1 ≤ clock.eval n := by
  let header := familyHeaderProgramTemplate anc out depth buf tmp
  let combined := sequenceProgramTemplate body header
  have hec := sequenceProgramTemplate_embeds body header he (familyHeaderProgramTemplate_embeds _ _ _ _ _)
  have hrc := sequenceProgramTemplate_run body header he hr (familyHeaderProgramTemplate_run _ _ _ _ _ ha ho hd hbt)
  obtain ⟨clock,hclock⟩ := (familySerializationProgramTemplate_resources body anc out depth buf tmp bound hb ht).2
  refine ⟨clock+Polynomial.C 1,?_⟩
  intro n
  rcases hmetadata n with ⟨hanc,hout,hdepth,hbuf,htmp⟩
  have hc : combined.ready (initial n) := ⟨hready n,hbuf,htmp⟩
  have hbytes : combined.bytes (initial n)=ShiBQP.encFamilyAt F n := by
    change header.bytes (body.counters (initial n))++body.bytes (initial n)=_
    rw [familyHeaderProgramTemplate_bytes,hanc,hout,hdepth,hpayload]
    exact familyHeader_encoding F n
  have h := cleanHaltProgramTemplate_halted_run combined hec hrc (initial n) [] hc
  rw [hbytes,List.append_nil] at h
  refine ⟨h,?_⟩
  have ht := hclock n (initial n) (hi n) ((cleanHaltProgramTemplate_ready combined _).2 hc)
  simpa only [Polynomial.eval_add,Polynomial.eval_C] using Nat.add_le_add_right ht 1

end ShiReversibleGenerator
