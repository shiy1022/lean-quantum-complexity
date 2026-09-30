import «AMPUNI-replay-restore-run»
import Theorems.Thm_ShiTM_initList_haltList_laws

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMReplayPreface

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOutputEntry

/-- The concrete finite machine archives its input from the ordinary `initList`
configuration, with no preloaded scratch or archive stack. -/
theorem archive_from_initList (s : List Cell) :
    ∃ U : ∀ k, List (TopGam k),
      run^[2 * (s.length + 1)] (some (Turing.initList finiteMachine s)) =
        some { l := some (oldLabel startLabel), var := none, stk := U }
      ∧ U source = s
      ∧ U scratch = []
      ∧ U archive = Cell.mirrorEnd :: s.reverse
      ∧ ∀ j : TopK, j ≠ source → j ≠ scratch →
          j ≠ archive → U j = [] := by
  let S₀ : ∀ k : TopK, List (TopGam k) :=
    (Turing.initList finiteMachine s).stk
  have hinit := ShiTM.initList_haltList_laws finiteMachine s []
  have hsource : S₀ source = s := by
    simpa [S₀, finiteMachine, source] using hinit.2.2.1
  have hscratch : S₀ scratch = [] := by
    exact hinit.2.2.2.1 scratch (by simp [finiteMachine, scratch])
  have harchive : S₀ archive = [] := by
    exact hinit.2.2.2.1 archive (by simp [finiteMachine, archive])
  obtain ⟨U, hrun, hUsource, hUscratch, hUarchive, hframe⟩ :=
    archive_input_run s none S₀ hsource hscratch harchive
  refine ⟨U, ?_, hUsource, hUscratch, hUarchive, ?_⟩
  · change run^[2 * (s.length + 1)]
      (some { l := some copyLabel, var := none, stk := S₀ }) = _
    exact hrun
  · intro j hj0 hj1 hj2
    rw [hframe j hj0 hj1 hj2]
    exact hinit.2.2.2.1 j (by simpa [finiteMachine, source] using hj0)

end ShiTMReplayPreface
