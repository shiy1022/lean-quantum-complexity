import QIP.Uniform.Bridge

/-! Fresh-import audit for Q34 (TM2 composition, structured machines, the `PT` closure
combinators and the bridge to `PvsNP.PolyTimeComputable`): statement types, then transitive
axioms. -/

open ShiQIP.Uniform

#check (ShiQIP.TMComp.polyTime_comp : ∀ {f g : PvsNP.Str → PvsNP.Str}, PvsNP.PolyTimeComputable f →
  PvsNP.PolyTimeComputable g → PvsNP.PolyTimeComputable (g ∘ f))
#check (polyTimeComputable_of_PT : ∀ {F : List Bool → List Bool}, PT F → PvsNP.PolyTimeComputable F)
#check (@PT.comp : ∀ {α β γ : Type} [Rep α] [Rep β] [Rep γ] {f : α → β} {g : β → γ}, PT f → PT g →
  PT (g ∘ f))
#check (@PT.pair : ∀ {α β γ : Type} [Rep α] [Rep β] [Rep γ] {f : α → β} {g : α → γ}, PT f → PT g →
  PT fun a => (f a, g a))
#check (@PT.ite : ∀ {α β : Type} [Rep α] [Rep β] {c : α → Bool} {f g : α → β}, PT c → PT f → PT g →
  PT fun a => if c a then f a else g a)
#check (@PT.foldl : ∀ {α β : Type} [Rep α] [Rep β] {step : β × α → β}, PT step →
  (∃ B : Polynomial ℕ, ∀ (s : β) (xs : List α) (k : ℕ),
    (enc (foldS step s (xs.take k))).length ≤ B.eval (enc (s, xs)).length) →
  PT fun p : β × List α => foldS step p.1 p.2)

#print axioms ShiQIP.TMComp.CK
#print axioms ShiQIP.TMComp.CΓ
#print axioms ShiQIP.TMComp.CΛ
#print axioms ShiQIP.TMComp.Cσ
#print axioms ShiQIP.TMComp.joinStk
#print axioms ShiQIP.TMComp.joinStk_inl
#print axioms ShiQIP.TMComp.joinStk_inr
#print axioms ShiQIP.TMComp.joinStk_aux
#print axioms ShiQIP.TMComp.update_joinStk_inl
#print axioms ShiQIP.TMComp.update_joinStk_inr
#print axioms ShiQIP.TMComp.update_joinStk_aux
#print axioms ShiQIP.TMComp.lift₁
#print axioms ShiQIP.TMComp.lift₂
#print axioms ShiQIP.TMComp.move₁
#print axioms ShiQIP.TMComp.move₂
#print axioms ShiQIP.TMComp.compM
#print axioms ShiQIP.TMComp.compTM
#print axioms ShiQIP.TMComp.lab₁
#print axioms ShiQIP.TMComp.stepAux_lift₁
#print axioms ShiQIP.TMComp.stepAux_lift₂
#print axioms ShiQIP.TMComp.initList_stk_self
#print axioms ShiQIP.TMComp.initList_stk_ne
#print axioms ShiQIP.TMComp.haltList_stk_self
#print axioms ShiQIP.TMComp.haltList_stk_ne
#print axioms ShiQIP.TMComp.emb₁
#print axioms ShiQIP.TMComp.emb₂
#print axioms ShiQIP.TMComp.step_emb₁
#print axioms ShiQIP.TMComp.step_emb₂
#print axioms ShiQIP.TMComp.iterate_none
#print axioms ShiQIP.TMComp.iterate_sim
#print axioms ShiQIP.TMComp.move₁_cons
#print axioms ShiQIP.TMComp.move₁_nil
#print axioms ShiQIP.TMComp.move₂_cons
#print axioms ShiQIP.TMComp.move₂_nil
#print axioms ShiQIP.TMComp.iterate_succ_some
#print axioms ShiQIP.TMComp.move₁_loop
#print axioms ShiQIP.TMComp.move₂_loop
#print axioms ShiQIP.TMComp.initList_comp
#print axioms ShiQIP.TMComp.haltList_comp
#print axioms ShiQIP.TMComp.transfer
#print axioms ShiQIP.TMComp.comp_run
#print axioms ShiQIP.TMComp.pushes
#print axioms ShiQIP.TMComp.stkSize
#print axioms ShiQIP.TMComp.stkSize_update
#print axioms ShiQIP.TMComp.stkSize_stepAux
#print axioms ShiQIP.TMComp.kFinInst
#print axioms ShiQIP.TMComp.ΛFinInst
#print axioms ShiQIP.TMComp.stepGrowth
#print axioms ShiQIP.TMComp.stkSize_step
#print axioms ShiQIP.TMComp.stkSize_iterate
#print axioms ShiQIP.TMComp.stkSize_initList
#print axioms ShiQIP.TMComp.length_le_stkSize_haltList
#print axioms ShiQIP.TMComp.output_length_le
#print axioms ShiQIP.TMComp.eval_mono
#print axioms ShiQIP.TMComp.comp_inPolyTime
#print axioms ShiQIP.TMComp.polyTime_comp
#print axioms ShiQIP.Uniform.BS
#print axioms ShiQIP.Uniform.Runs
#print axioms ShiQIP.Uniform.Runs.of_eq
#print axioms ShiQIP.Uniform.Runs.of_eq₀
#print axioms ShiQIP.Uniform.rl
#print axioms ShiQIP.Uniform.rlLab
#print axioms ShiQIP.Uniform.stepAux_rl
#print axioms ShiQIP.Uniform.iterate_embed
#print axioms ShiQIP.Uniform.basic
#print axioms ShiQIP.Uniform.seq
#print axioms ShiQIP.Uniform.loop
#print axioms ShiQIP.Uniform.ite
#print axioms ShiQIP.Uniform.runs_basic
#print axioms ShiQIP.Uniform.runs_seq
#print axioms ShiQIP.Uniform.runs_loop_false
#print axioms ShiQIP.Uniform.runs_loop_true
#print axioms ShiQIP.Uniform.runs_ite_true
#print axioms ShiQIP.Uniform.runs_ite_false
#print axioms ShiQIP.Uniform.sR
#print axioms ShiQIP.Uniform.sL
#print axioms ShiQIP.Uniform.vR
#print axioms ShiQIP.Uniform.vL
#print axioms ShiQIP.Uniform.stepAux_sR
#print axioms ShiQIP.Uniform.stepAux_sL
#print axioms ShiQIP.Uniform.stepAux_vR
#print axioms ShiQIP.Uniform.stepAux_vL
#print axioms ShiQIP.Uniform.Mach.sR
#print axioms ShiQIP.Uniform.Mach.sL
#print axioms ShiQIP.Uniform.Mach.vR
#print axioms ShiQIP.Uniform.Mach.vL
#print axioms ShiQIP.Uniform.runs_sR
#print axioms ShiQIP.Uniform.runs_sL
#print axioms ShiQIP.Uniform.runs_vR
#print axioms ShiQIP.Uniform.runs_vL
#print axioms ShiQIP.Uniform.V.code
#print axioms ShiQIP.Uniform.popTo
#print axioms ShiQIP.Uniform.moveBody
#print axioms ShiQIP.Uniform.moveBody2
#print axioms ShiQIP.Uniform.moveAll
#print axioms ShiQIP.Uniform.moveAll2
#print axioms ShiQIP.Uniform.discard
#print axioms ShiQIP.Uniform.runs_moveLoop
#print axioms ShiQIP.Uniform.runs_moveAll
#print axioms ShiQIP.Uniform.runs_moveLoop2
#print axioms ShiQIP.Uniform.runs_moveAll2
#print axioms ShiQIP.Uniform.runs_discardLoop
#print axioms ShiQIP.Uniform.runs_discard
#print axioms ShiQIP.Uniform.parseBody
#print axioms ShiQIP.Uniform.parseV
#print axioms ShiQIP.Uniform.parseBody_l
#print axioms ShiQIP.Uniform.runs_parseLoop
#print axioms ShiQIP.Uniform.runs_parseV
#print axioms ShiQIP.Uniform.enc
#print axioms ShiQIP.Uniform.natV
#print axioms ShiQIP.Uniform.listV
#print axioms ShiQIP.Uniform.enc_pair
#print axioms ShiQIP.Uniform.enc_nil
#print axioms ShiQIP.Uniform.enc_cons
#print axioms ShiQIP.Uniform.enc_zero
#print axioms ShiQIP.Uniform.enc_succ
#print axioms ShiQIP.Uniform.enc_false
#print axioms ShiQIP.Uniform.enc_true
#print axioms ShiQIP.Uniform.length_enc_pos
#print axioms ShiQIP.Uniform.one
#print axioms ShiQIP.Uniform.BM.Computes
#print axioms ShiQIP.Uniform.PT
#print axioms ShiQIP.Uniform.one_inl
#print axioms ShiQIP.Uniform.one_inr
#print axioms ShiQIP.Uniform.castM
#print axioms ShiQIP.Uniform.castM_computes
#print axioms ShiQIP.Uniform.PT.ofEnc
#print axioms ShiQIP.Uniform.PT.id
#print axioms ShiQIP.Uniform.lift1
#print axioms ShiQIP.Uniform.lift2
#print axioms ShiQIP.Uniform.runs_lift1
#print axioms ShiQIP.Uniform.runs_lift2
#print axioms ShiQIP.Uniform.compB
#print axioms ShiQIP.Uniform.compB_stk₁
#print axioms ShiQIP.Uniform.compB_stk₂
#print axioms ShiQIP.Uniform.compB_computes
#print axioms ShiQIP.Uniform.PT.comp
#print axioms ShiQIP.Uniform.PT.comp'
#print axioms ShiQIP.Uniform.slot3
#print axioms ShiQIP.Uniform.pairB
#print axioms ShiQIP.Uniform.pairB_computes
#print axioms ShiQIP.Uniform.PT.pair
#print axioms ShiQIP.Uniform.reg4
#print axioms ShiQIP.Uniform.regB
#print axioms ShiQIP.Uniform.regB_computes
#print axioms ShiQIP.Uniform.pop2
#print axioms ShiQIP.Uniform.fstM
#print axioms ShiQIP.Uniform.fstM_runs
#print axioms ShiQIP.Uniform.sndM
#print axioms ShiQIP.Uniform.sndM_runs
#print axioms ShiQIP.Uniform.pushL
#print axioms ShiQIP.Uniform.stepAux_pushL
#print axioms ShiQIP.Uniform.constM
#print axioms ShiQIP.Uniform.constM_runs
#print axioms ShiQIP.Uniform.selM
#print axioms ShiQIP.Uniform.selM_runs_true
#print axioms ShiQIP.Uniform.selM_runs_false
#print axioms ShiQIP.Uniform.PT.fst
#print axioms ShiQIP.Uniform.PT.snd
#print axioms ShiQIP.Uniform.PT.const
#print axioms ShiQIP.Uniform.sel
#print axioms ShiQIP.Uniform.PT.sel
#print axioms ShiQIP.Uniform.PT.ite
#print axioms ShiQIP.Uniform.peekA
#print axioms ShiQIP.Uniform.subM
#print axioms ShiQIP.Uniform.foldBody
#print axioms ShiQIP.Uniform.foldLoop
#print axioms ShiQIP.Uniform.foldB
#print axioms ShiQIP.Uniform.runs_subM
#print axioms ShiQIP.Uniform.foldBody_runs
#print axioms ShiQIP.Uniform.FoldOK
#print axioms ShiQIP.Uniform.foldS
#print axioms ShiQIP.Uniform.foldLoop_runs
#print axioms ShiQIP.Uniform.foldOK_of
#print axioms ShiQIP.Uniform.length_lt_enc_list
#print axioms ShiQIP.Uniform.enc_get_lt
#print axioms ShiQIP.Uniform.foldB_computes
#print axioms ShiQIP.Uniform.foldS_take_succ
#print axioms ShiQIP.Uniform.PT.foldl
#print axioms ShiQIP.Uniform.BM.toFinTM2
#print axioms ShiQIP.Uniform.BM.initList_eq
#print axioms ShiQIP.Uniform.BM.haltList_eq
#print axioms ShiQIP.Uniform.inPolyTime_of_computes
#print axioms ShiQIP.Uniform.PT.inPolyTime
#print axioms ShiQIP.Uniform.itemT
#print axioms ShiQIP.Uniform.enc_list_bool
#print axioms ShiQIP.Uniform.popA
#print axioms ShiQIP.Uniform.bodyIn
#print axioms ShiQIP.Uniform.runs_loopIn
#print axioms ShiQIP.Uniform.rawInM
#print axioms ShiQIP.Uniform.rawInM_runs
#print axioms ShiQIP.Uniform.bodyOut
#print axioms ShiQIP.Uniform.runs_loopOut
#print axioms ShiQIP.Uniform.rawOutM
#print axioms ShiQIP.Uniform.rawOutM_runs
#print axioms ShiQIP.Uniform.polyTimeComputable_of_PT
