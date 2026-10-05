import «AMPUNI-output-header-work-restore»
import «AMPUNI-output-header-dispatch»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOutputHeader

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceEntry

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

theorem work_field_run (pc : PC) (atom : Atom) (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsource : S (.inr (source atom)) = List.replicate n Cell.mark)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)),
      run^[2 * n + 3]
        (some { l := some (.work pc atom .copy), var := v, stk := S }) =
          some { l := some (.dispatch (nextPC pc)), var := none, stk := U }
      ∧ U (.inr (source atom)) = List.replicate n Cell.mark
      ∧ U (.inl (.inl (13 : Fin 14))) =
          List.replicate n Cell.mark ++ S (.inl (.inl (13 : Fin 14)))
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, j ≠ .inr (source atom) →
          j ≠ .inl (.inl (13 : Fin 14)) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  obtain ⟨C, hcopy, hCsource, hCdest, hCscratch, hCframe⟩ :=
    work_copy_marks_run pc atom n v S hsource
  have hCscratch' : C (.inl (.inl (3 : Fin 14))) =
      List.replicate n Cell.mark := by
    simpa [hscratch] using hCscratch
  obtain ⟨U, hrestore, hUscratch, hUsource, hUframe⟩ :=
    work_restore_marks_run pc atom n none C hCscratch'
  refine ⟨U, ?_, ?_, ?_, hUscratch, ?_⟩
  · have hfirst := iterTwo run (n + 1) (n + 1) _ _ _ hcopy hrestore
    have hlast := work_done_step pc atom none U
    have hall := iterTwo run ((n + 1) + (n + 1)) 1 _ _ _ hfirst hlast
    have hcost : ((n + 1) + (n + 1)) + 1 = 2 * n + 3 := by omega
    simpa only [hcost] using hall
  · rw [hUsource, hCsource]
    simp
  · have hd : (.inl (.inl (13 : Fin 14)) : TopK) ≠
        .inl (.inl (3 : Fin 14)) := by decide
    rw [hUframe (.inl (.inl (13 : Fin 14))) (by simp) hd, hCdest]
  · intro j hj0 hjd hj3
    rw [hUframe j hj0 hj3, hCframe j hj0 hjd hj3]

theorem dispatch_field_run (pc : PC) (atom : Atom) (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hcommand : commandAt program pc.val = some (.add atom))
    (hone : atom ≠ .one)
    (hsource : S (.inr (source atom)) = List.replicate n Cell.mark)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)),
      run^[2 * n + 4]
        (some { l := some (.dispatch pc), var := v, stk := S }) =
          some { l := some (.dispatch (nextPC pc)), var := none, stk := U }
      ∧ U (.inr (source atom)) = List.replicate n Cell.mark
      ∧ U (.inl (.inl (13 : Fin 14))) =
          List.replicate n Cell.mark ++ S (.inl (.inl (13 : Fin 14)))
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, j ≠ .inr (source atom) →
          j ≠ .inl (.inl (13 : Fin 14)) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  obtain ⟨U, hrun, hsrc, hdest, hscratch', hframe⟩ :=
    work_field_run pc atom n v S hsource hscratch
  refine ⟨U, ?_, hsrc, hdest, hscratch', hframe⟩
  have hfirst := dispatch_field_step pc atom v S hcommand hone
  have hall := iterTwo run 1 (2 * n + 3) _ _ _ hfirst hrun
  have hcost : 1 + (2 * n + 3) = 2 * n + 4 := by omega
  simpa only [hcost] using hall

end ShiTMOutputHeader
