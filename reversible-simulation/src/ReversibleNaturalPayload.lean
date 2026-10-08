import ReversibleFixedNodePrinter

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

def payloadRegisters (a b c : Nat) : Fin 3 → Nat :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else c

/-- A natural-address payload, independent of the generator's register names. -/
def assignmentPayload (kind : AssignmentEmissionKind) (a b c : Nat) : List Bool :=
  emissionBytes (assignmentAtoms kind (0 : Fin 3) 1 2) (payloadRegisters a b c)

theorem assignmentAtoms_payload (kind : AssignmentEmissionKind) (p q r : R) (cs : R → Nat) :
    emissionBytes (assignmentAtoms kind p q r) cs = assignmentPayload kind (cs p) (cs q) (cs r) := by
  cases kind <;> simp [assignmentPayload, assignmentAtoms, xAtoms, cxAtoms, toffoliEmissionAtoms,
    emissionBytes, EmissionAtom.bytes, payloadRegisters]

theorem assignmentPayload_encoding {m : Nat} (kind : AssignmentEmissionKind) (i j k : Fin m)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    assignmentPayload kind i.val j.val k.val =
      ((assignmentLayers kind i j k hij hik hjk).map ShiBQP.encLayer).flatten := by
  exact assignmentAtoms_bytes kind (0 : Fin 3) 1 2 i j k hij hik hjk
    (payloadRegisters i.val j.val k.val) (by simp [payloadRegisters])
    (by simp [payloadRegisters]) (by simp [payloadRegisters])

def FixedNodeTemplate.payload (t : FixedNodeTemplate R) (cs : R → Nat) : List Bool :=
  assignmentPayload t.kind (t.x.eval cs) (t.y.eval cs) (t.z.eval cs)

def FixedNodeTemplate.StableSources (t : FixedNodeTemplate R) (r : NodePrinterRegisters R) : Prop :=
  (t.x.source ≠ r.p ∧ t.x.source ≠ r.q ∧ t.x.source ≠ r.r ∧ t.x.source ≠ r.count) ∧
  (t.y.source ≠ r.p ∧ t.y.source ≠ r.q ∧ t.y.source ≠ r.r ∧ t.y.source ≠ r.count) ∧
  (t.z.source ≠ r.p ∧ t.z.source ≠ r.q ∧ t.z.source ≠ r.r ∧ t.z.source ≠ r.count)

theorem FixedNodeTemplate.bytes_payload (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hs : t.StableSources r) (cs : R → Nat) : t.bytes r cs = t.payload cs := by
  rcases hs with ⟨⟨hxp, hxq, hxr, hxc⟩, ⟨hyp, hyq, hyr, hyc⟩, ⟨hzp, hzq, hzr, hzc⟩⟩
  rw [FixedNodeTemplate.bytes, assignmentAtoms_payload]
  change assignmentPayload t.kind
    (nodeFieldResult t.x t.y t.z r.p r.q r.r cs r.p)
    (nodeFieldResult t.x t.y t.z r.p r.q r.r cs r.q)
    (nodeFieldResult t.x t.y t.z r.p r.q r.r cs r.r) = _
  rw [nodeFieldResult_eval t.x t.y t.z r.p r.q r.r hpq hpr hqr
    ⟨hxp, hxq, hxr⟩ ⟨hyp, hyq, hyr⟩ ⟨hzp, hzq, hzr⟩]
  simp [payload, hpq, hpr, hqr, Ne.symm hpq, Ne.symm hpr, Ne.symm hqr]

theorem FixedNodeTemplate.counters_other (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (s : R) (hp : s ≠ r.p) (hq : s ≠ r.q) (hr : s ≠ r.r) (hc : s ≠ r.count) (cs : R → Nat) :
    t.counters r cs s = cs s := by
  simp [counters, fields, hc, nodeFieldResult_other, hp, hq, hr]

theorem FixedNodeTemplate.payload_preserved (t u : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (hu : u.StableSources r) (cs : R → Nat) : u.payload (t.counters r cs) = u.payload cs := by
  rcases hu with ⟨⟨hxp, hxq, hxr, hxc⟩, ⟨hyp, hyq, hyr, hyc⟩, ⟨hzp, hzq, hzr, hzc⟩⟩
  simp [payload, SymbolicWire.eval, t.counters_other r u.x.source hxp hxq hxr hxc,
    t.counters_other r u.y.source hyp hyq hyr hyc, t.counters_other r u.z.source hzp hzq hzr hzc]

theorem fixedNodeBytes_payloads (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hs : ∀ t ∈ ts, t.StableSources r) (cs : R → Nat) :
    fixedNodeBytes r ts cs = (ts.reverse.map (fun t => t.payload cs)).flatten := by
  induction ts generalizing cs with
  | nil => rfl
  | cons t ts ih =>
      rw [fixedNodeBytes, ih (fun u hu => hs u (by simp [hu])),
        t.bytes_payload r hpq hpr hqr (hs t (by simp))]
      have hm : ts.reverse.map (fun u => u.payload (t.counters r cs)) = ts.reverse.map (fun u => u.payload cs) := by
        apply List.map_congr_left
        intro u hu
        exact t.payload_preserved u r (hs u (by simp only [List.mem_reverse] at hu; simp [hu])) cs
      rw [hm]
      simp [List.reverse_cons, List.map_append, List.flatten_append]

end ShiReversibleGenerator
