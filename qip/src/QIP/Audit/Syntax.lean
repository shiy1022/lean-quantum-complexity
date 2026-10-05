import QIP.Decode

/-! Fresh-import audit for Q13 and Q14: exact statement types, then transitive axioms. -/

open ShiQIP

#check (Desc.serialSize_le : ∀ {d : Desc}, d.Valid →
  d.serialSize ≤ (d.gateCount + d.numMsgs + 3) * (2 * d.totalWires + 8))
#check (Desc.numMsgs_of_hasSchedule : ∀ {d : Desc} {k : ℕ}, d.HasSchedule k → d.numMsgs = k)
#check (stdSchedule_three : stdSchedule 3 = [Dir.toVerifier, Dir.toProver, Dir.toVerifier])
#check (encode_length : ∀ d : Desc, (encode d).length = d.serialSize)
#check (decDesc_encode : ∀ (d : Desc) (r : Str), decDesc (encode d ++ r) = some (d, r))
#check (decode_encode : ∀ d : Desc, decode (encode d) = some d)
#check (encode_injective : Function.Injective encode)
#check (decode_eq_some_iff : ∀ {s : Str} {d : Desc}, decode s = some d ↔ s = encode d)
#check (decodeChecked_eq_some_iff : ∀ {s : Str} {d : Desc},
  decodeChecked s = some d ↔ s = encode d ∧ d.Valid)
#check (decode_proper_prefix : ∀ {s t : Str} {d : Desc}, s ++ t = encode d → t ≠ [] →
  decode s = none)
#check (Gate.toInstr?_isSome_iff : ∀ (n : ℕ) (g : Gate),
  (g.toInstr? n).isSome ↔ g.okBool (fun w => decide (w < n)) = true)

#print axioms ShiQIP.Gate.toInstr?_isSome_iff
#print axioms ShiQIP.Desc.numMsgs_of_hasSchedule
#print axioms ShiQIP.msgHeld_lt
#print axioms ShiQIP.Desc.held_lt
#print axioms ShiQIP.Gate.encLen_le
#print axioms ShiQIP.Desc.blocksOkFrom_encLen
#print axioms ShiQIP.Desc.Valid.out_lt
#print axioms ShiQIP.Desc.Valid.alternates
#print axioms ShiQIP.Desc.Valid.blocks_length
#print axioms ShiQIP.Desc.Valid.blocksOk
#print axioms ShiQIP.Desc.serialSize_le
#print axioms ShiQIP.encode_length
#print axioms ShiQIP.encode_length_le
#print axioms ShiQIP.decNat_encNat
#print axioms ShiQIP.decGate_encGate
#print axioms ShiQIP.decList_encList
#print axioms ShiQIP.decDesc_encode
#print axioms ShiQIP.decode_encode
#print axioms ShiQIP.encode_injective
#print axioms ShiQIP.decodeChecked_encode
#print axioms ShiQIP.decNat_sound
#print axioms ShiQIP.decGate_sound
#print axioms ShiQIP.decList_sound
#print axioms ShiQIP.decDesc_sound
#print axioms ShiQIP.decode_eq_some_iff
#print axioms ShiQIP.decodeChecked_eq_some_iff
#print axioms ShiQIP.decNat_replicate_true
#print axioms ShiQIP.decGate_bad_tag
#print axioms ShiQIP.decode_encode_append
#print axioms ShiQIP.decode_proper_prefix
