import QIP.ThreeMessage
import QIP.SDP.Product
import QIP.SDP.ConicDuality
import QIP.UnitaryProver
import QIP.Gen.Cut
import Quantum.UhlmannAttained
import Quantum.FidelityTwoTargets

/-! Q41 — final audit of the endpoint and the main certificates of the theorem graph.

The endpoint is checked with its exact type. The other entries record the statements the proof
rests on (strategy/operational equivalence, Uhlmann, duality, the product bound, halving,
compression, the pipeline, the printer and its polynomial-time certificate), then their
transitive axioms. -/

open ShiQIP ShiQIP.Uniform ShiQIP.Arith ShiQuantum

#check (qip_eq_qip3 : ShiQIP.QIP = ShiQIP.QIPm 3)
#check (QIP : Set PromiseProblem)
#check (QIPm : ℕ → Set PromiseProblem)
#check @Decides
#check @VerifierFamily
#check @accept_eq_pairing
#check @value_eq_sdpVal
#check @sdpVal_prod
#check @conic_approx_duality
#check @exists_unitary_overlap_eq_fidelity
#check @fidelity_two_targets
#check @accept_dilateU
#check @gAcc_le_value
#check @cut_bound
#check @value_halve_le
#check @compressR_spec
#check @value_parRepeat
#check @threeDesc_spec
#check @hsize_threeDesc_le
#check @printer_encode
#check @printer_polyTime
#check @TMComp.polyTime_comp
#check @polyTimeComputable_of_PT
#check @VerifierFamily.three_decides

#print axioms ShiQIP.qip_eq_qip3
#print axioms ShiQIP.qip_subset_qip3
#print axioms ShiQIP.qipm_subset_qip
#print axioms ShiQIP.accept_eq_pairing
#print axioms ShiQIP.value_eq_sdpVal
#print axioms ShiQIP.sdpVal_prod
#print axioms ShiQuantum.conic_approx_duality
#print axioms ShiQuantum.exists_unitary_overlap_eq_fidelity
#print axioms ShiQuantum.fidelity_two_targets
#print axioms ShiQIP.accept_dilateU
#print axioms ShiQIP.gAcc_le_value
#print axioms ShiQIP.cut_bound
#print axioms ShiQIP.value_halve_le
#print axioms ShiQIP.compressR_spec
#print axioms ShiQIP.value_parRepeat
#print axioms ShiQIP.threeDesc_spec
#print axioms ShiQIP.hsize_threeDesc_le
#print axioms ShiQIP.Uniform.printer_encode
#print axioms ShiQIP.Uniform.printer_polyTime
#print axioms ShiQIP.TMComp.polyTime_comp
#print axioms ShiQIP.Uniform.polyTimeComputable_of_PT
#print axioms ShiQIP.VerifierFamily.three_decides
