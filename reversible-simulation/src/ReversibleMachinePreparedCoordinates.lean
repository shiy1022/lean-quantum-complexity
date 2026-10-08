import ReversibleMachineSerializationPolytime
import ReversiblePaddedFinishedCopyAgreement
import ReversibleRawProgramConcatenation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The semantic initializer's padded roots have exactly the raw generator's first-history stride. -/
theorem machineInitialRead_strided (tm : Turing.FinTM2) (capacity n : Nat) :
    (fun i : Fin (configurationWidth tm capacity) => paddedForestResult n 17 i.val)=
      (fun i => n+17+18*i.val) := by
  funext i
  simp only [paddedForestResult]
  ring

/-- After a positive number of actual time slices, semantic prepared reads have exactly the extraction printer's raw coordinates. -/
theorem machinePreparedRead_strided (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool)
    (capacity n budget : Nat) (ht : 0<budget) :
    paddedPreparedRead (initialForest tm e₀ capacity n) (tickForest tm capacity)
      (tickForest_length tm capacity) 17 (tickSizeBound tm) budget=
      (fun i => (n+18*configurationWidth tm capacity+
        budget*(configurationWidth tm capacity*(tickSizeBound tm+1)))-
          configurationWidth tm capacity*(tickSizeBound tm+1)+tickSizeBound tm+
            (tickSizeBound tm+1)*i.val) := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  funext i
  rw [paddedPreparedRead,paddedIterationRead_succ]
  simp only [initialForest_length]
  have h : n+18*configurationWidth tm capacity+
      (t+1)*(configurationWidth tm capacity*(tickSizeBound tm+1))=
      n+18*configurationWidth tm capacity+t*(configurationWidth tm capacity*(tickSizeBound tm+1))+
        configurationWidth tm capacity*(tickSizeBound tm+1) := by ring
  rw [h,Nat.add_sub_cancel]
  ring

end ShiReversibleGenerator
