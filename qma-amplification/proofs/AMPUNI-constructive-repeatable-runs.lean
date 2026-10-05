import «AMPUNI-constructive-concrete-machine»
import «AMPUNI-variable-repeatable-runs»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
noncomputable section
namespace ShiTMConstructiveConcrete
open ShiClassQMA ShiClassQMAU ShiClassQMAAmpX
  ShiQMAVariableRounds

/-- The source machine that implements one amplification step works at
either value of the parity bit retained by the logarithmic loader. -/
theorem lifted_repeatable_round_runs :
    ∃ k C : Nat, ∀ (F : QMAFamily) (n r : Nat) (b : Bool),
      let xs := ShiBQP.encNat n ++ encQMAFamilyAt (iter F r) n
      let ys := encQMAFamilyAt (ampFamilyX (iter F r)) n
      ∃ t : Nat,
        (ShiTMSubroutine.run (liftedSource (source k).m))^[t]
          (some (liftedCfg b (Turing.initList (source k) xs))) =
          some (liftedCfg b
            (ShiTMRepeatFueled.activeFinish
              ShiTMNormalizedEntry.booleanMachine
              (Equiv.refl Bool) k ys)) ∧
        t ≤ C * (xs.length + 1) ^ 2 := by
  obtain ⟨k, C, hk⟩ :=
    ShiQMAVariableRounds.concrete_repeatable_round_runs
  refine ⟨k, C, ?_⟩
  intro F n r b
  obtain ⟨t, hr, ht⟩ := hk F n r
  refine ⟨t, ?_, ht⟩
  have hframe := liftedSource_run_iter
    (source k).m b t
    (some (Turing.initList (source k)
      (ShiBQP.encNat n ++ encQMAFamilyAt (iter F r) n)))
  have hr' :
      (ShiTMSubroutine.run (source k).m)^[t]
        (some (Turing.initList (source k)
          (ShiBQP.encNat n ++ encQMAFamilyAt (iter F r) n))) =
      some (ShiTMRepeatFueled.activeFinish
        ShiTMNormalizedEntry.booleanMachine
        (Equiv.refl Bool) k
        (encQMAFamilyAt (ampFamilyX (iter F r)) n)) := hr
  exact hframe.trans (congrArg (Option.map (liftedCfg b)) hr')

end ShiTMConstructiveConcrete
