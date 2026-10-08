import ReversibleEmissionSequence

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

/-- Execute in reverse field order because the output stack prepends each field. -/
def familyHeaderAtoms (anc out depth : R) : List (EmissionAtom R) :=
  [.natural depth, .natural out, .natural anc]

theorem familyHeader_valid (anc out depth buf tmp : R)
    (ha : anc ≠ buf ∧ anc ≠ tmp) (ho : out ≠ buf ∧ out ≠ tmp)
    (hd : depth ≠ buf ∧ depth ≠ tmp) :
    ∀ a ∈ familyHeaderAtoms anc out depth, a.Valid buf tmp := by
  simp [familyHeaderAtoms, EmissionAtom.Valid, ha, ho, hd]

theorem familyHeader_bytes (anc out depth : R) (cs : R → Nat) :
    emissionBytes (familyHeaderAtoms anc out depth) cs =
      ShiBQP.encNat (cs anc) ++ ShiBQP.encNat (cs out) ++ ShiBQP.encNat (cs depth) := by
  simp [familyHeaderAtoms, emissionBytes, EmissionAtom.bytes, List.append_assoc]

/-- Actual finite header program, retaining the already emitted layer payload. -/
theorem familyHeader_run (caller : L → CounterInstr R L) (anc out depth buf tmp : R) (stop : L)
    (ha : anc ≠ buf ∧ anc ≠ tmp) (ho : out ≠ buf ∧ out ≠ tmp)
    (hd : depth ≠ buf ∧ depth ≠ tmp) (hbt : buf ≠ tmp)
    (cs : R → Nat) (hb : cs buf = 0) (ht : cs tmp = 0) (payload : List Bool) :
    CounterRun (emissionCode (familyHeaderAtoms anc out depth) caller buf tmp stop)
      ⟨some (emissionEntry (familyHeaderAtoms anc out depth) stop), cs, payload⟩
      (emissionSteps (familyHeaderAtoms anc out depth) cs)
      ⟨some (emissionExit (familyHeaderAtoms anc out depth) stop), cs,
        (ShiBQP.encNat (cs anc) ++ ShiBQP.encNat (cs out) ++ ShiBQP.encNat (cs depth)) ++ payload⟩ := by
  simpa only [familyHeader_bytes] using emissionCode_run (familyHeaderAtoms anc out depth)
    caller buf tmp stop (familyHeader_valid anc out depth buf tmp ha ho hd) hbt cs hb ht payload

theorem familyHeader_clock_polynomial (anc out depth : R) (sizes : R → Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      emissionSteps (familyHeaderAtoms anc out depth) (fun r => (sizes r).eval n) = p.eval n := by
  exact ⟨emissionClock (familyHeaderAtoms anc out depth) sizes,
    fun n => (emissionClock_eval _ _ n).symm⟩

/-- Relate the emitted header to the unchanged established family serialization. -/
theorem familyHeader_encoding (F : ShiClass.Family) (n : Nat) :
    (ShiBQP.encNat (F.anc n) ++ ShiBQP.encNat ((F.out n : Nat)) ++
      ShiBQP.encNat (F.circ n).length) ++ ((F.circ n).map ShiBQP.encLayer).flatten =
      ShiBQP.encFamilyAt F n := by
  simp [ShiBQP.encFamilyAt, ShiBQP.encCirc, ShiBQP.encStr, List.append_assoc]

end ShiReversibleGenerator
