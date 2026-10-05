# QIP = QIP(3) progress ledger

Evidence kind: **local check** means `python scripts/audit.py` on the Windows workstation. That
run uses Lean 4.33.1 and the pinned Mathlib `0df444a3` build shared from `bqp-pp`. It builds the
whole `ShiQIP` library with `LEAN_NUM_THREADS=1`, then elaborates each `src/QIP/Audit/*.lean`
file freshly and requires exactly one allowed axiom report per request. Each run is paired with
`python scripts/manifest.py --check`. The plan requires Sherlock, but Sherlock login needs
Duo/Kerberos, which the agent cannot complete. The user therefore authorised local
single-thread builds on 2026-10-05. **No row below is Sherlock clean-build evidence.**

Status vocabulary (plan §8): `not_started → statement_checked → proof_in_progress →
focused_verified → integrated_verified → clean_verified`. `integrated_verified (local)` means
the module compiled inside the full `ShiQIP` build and passed the fresh-import audit locally.
`clean_verified` is reserved for a source-matched Sherlock clean build.

Every report in `verification/audit.json` uses only `propext`, `Classical.choice` and
`Quot.sound`. No `sorry`, `admit`, `axiom` or `proof_wanted` occurs in `src/`. The last run
took 226 s and produced 225 reports across 8 audit files (27 sources), from `git_head`
13e55b6 plus the Q06 changes. Source hashes are in `source-manifest.json` and `verification/audit.json`.

| Task | Status | Declarations / files | Evidence | Remaining gap |
|---|---|---|---|---|
| Q00 | integrated_verified (local) | `lakefile.toml`, `lake-manifest.json`, `scripts/manifest.py`, `scripts/audit.py`, `verification/baseline.json`, `verification/reuse-map.md`, `QIP.Smoke` | audit and manifest self-tests reject missing, duplicate, forbidden and unrequested reports and tampered manifests. bqp-pp (306 hashes) and bqp-pspace manifests re-verified. `Audit/Smoke.lean`: 1 report | acceptance asks for the smoke audit **on Sherlock** — not done |
| Q01 | integrated_verified (local) | `Quantum.MathlibImports`, `verification/mathlib-api.md` | 64 `#check`s and 6 examples compile; `CFC.sqrt`, the factorization `A = Bᴴ B`, the L2 operator norm and the CP-map type are instantiated on complex matrices | none for this task; absences routed to Q03–Q11 and Q22–Q23 |
| Q02 | integrated_verified (local) | `Quantum.Registers`, `Quantum.Reindex`: `qubitsAppend`, `regAssoc`/`regSwap`/`regUnitRight`, `permMat`, `reindexState`, `permMat_conj`, `kron_regAssoc`, `kron_regSwap`, `reindex_regSwap_twice`, `kron_regUnitRight`, `qubitsAppend_zero_right_eq` | `Audit/Registers.lean`: 29 reports | — |
| Q03 | integrated_verified (local) | `Quantum.Positive`, `Quantum.HilbertBridge`: `posSemidef_iff_exists_mul_conjTranspose`, `psdSqrt` (= `CFC.sqrt`) with `psdSqrt_posSemidef`/`_mul_self`/`_unique`, `trace_reindex`, `trace_conj_unitary`, `psd_trace_mul_nonneg`, `trace_mono`, `trace_mul_mono`, `conj_mono`, `kronecker_mono_left/right`, `trace_rankOne`, `trace_mul_rankOne`; `toE`, `inner_toE`, `norm_toE_sq`, `norm_mulVec_le` (L2 operator norm), `norm_toE_unitary`, `inner_toE_mulVec_eq_trace`, `supNorm_lt_norm_toE` | `Audit/Positive.lean`: 36 reports. Non-diagonal complex test matrix `testMat = !![2, I; -I, 2]` (PSD, `trace = 4`, square root, `trace (testMat · v v†) = 6`) | — |
| Q04 | integrated_verified (local) | `Quantum.State`, `Quantum.Measurement`: `IsDensity` (PSD ∧ trace 1, both hypotheses), `Density`, `IsDensity.mix`, `pureState`, `isDensity_pure_iff` (↔ `∑ ‖v i‖² = 1`), `isDensity_pure_iff_norm`, `maxMixed`, `isDensity_maxMixed`, `isDensity_unique_iff` (one-dimensional registers); `IsEffect` (`0 ≤ E ≤ 1`), `prob E ρ = Re tr(Eρ)`, `prob_mem_Icc`, `prob_compl`, `prob_mix`, `prob_mono`, `prob_pureState`, `basisEffect`, `prob_basisEffect_pureState` | `Audit/State.lean`: 29 reports. `|+⟩` is normalized and gives outcome 1 with probability exactly `1/2`; zero-qubit maximally mixed state | identification with `ShiShallow.acceptProb` on circuits is Q16 |
| Q05 | integrated_verified (local) | `Quantum.PartialTrace`: `traceRight` (`[a,b] = ∑ i, M (a,i) (b,i)`, kept factor may be rectangular), `traceLeft`, `trace_traceRight`/`Left`, `traceRight_eq_sum_slice` (Kraus-type form), `posSemidef_traceRight`/`Left`, `IsDensity.traceRight`/`Left`/`kronecker`, `traceRight_kronecker`, `traceRight_local`, `traceRight_conj_unitary` (unitary on the traced factor is invisible), `trace_mul_traceRight` (duality with `A ⊗ 1`), `traceLeft_eq_traceRight_swap`, `traceRight_prod`, `traceRight_reindex_left/right`, `traceRight_unique`, `traceRight_unitRight` | `Audit/PartialTrace.lean`: 30 reports. Bell marginal is `maxMixed Bool` and provably not pure; product marginals are the factors; one-dimensional/zero-qubit traced registers are deleted | marginal invariance under an arbitrary channel on the other register belongs to Q06 (plan step 3) |
| Q06 | integrated_verified (local) | `Quantum.Channel`, `Quantum.ChannelTensor`, `Quantum.ChannelMathlib`: `MatMap`, `liftR` (`id_k ⊗ Φ`), `IsPositiveMap`, `IsCP` (ampliation positive for every finite `k : Type`), `IsTP`, `IsChannel`; `IsCP.isPositiveMap`, `IsChannel.map_density`; identity, composition, sums, `conjMap`, `krausMap`, `isChannel_unitary`, `isChannel_discardMap` (its ampliation is the partial trace), `isChannel_prepMap`, `isChannel_dephase`, `IsInstrument` with `prob_nonneg`/`sum_prob`, `isInstrument_basis`; `reindexMap`, `liftR_liftR`, `IsChannel.liftR`/`liftL`/`tensor`, `tensorMap_kronecker`, **`traceRight_liftR` (no-signalling)**, `traceRight_liftL`; bridge `cstar_nonneg_iff_flat`, `IsCP.toCPMap`, **`isCP_iff_cpMap`** (both directions vs Mathlib `CompletelyPositiveMap`) | `Audit/Channel.lean`: 46 reports. `not_isCP_transposeMap`: the transpose is positive but not CP (Bell witness, expectation `-2`) | plan's hard review gate after Q06 is pending (see below) |
| Q13 | integrated_verified (local) | `QIP.Syntax`, `QIP.Resources`: `Desc`, `Gate`, `Message`, `Desc.held`, `Desc.check`/`Valid`, `stdSchedule`, `HasSchedule`, `gateCount`, `totalWires`, `communication`, `serialSize`, `Desc.serialSize_le`, `Gate.toInstr?` | `Audit/Syntax.lean`. 1-, 2-, 3- (zero-width middle message) and 5-message examples are valid by `decide`. Negative examples cover use-after-send, use-before-receive, `cnot i i`, an output outside the private register, a zero-width private register, non-alternation and a verifier-first schedule | gate *semantics* bridge is Q16 |
| Q14 | integrated_verified (local) | `QIP.Encoding`, `QIP.Decode`: `encode`, `decode`, `decodeChecked`, `decode_encode`, `encode_injective`, `decode_eq_some_iff`, `encode_length` (= `serialSize`), `encode_length_le`, `decode_proper_prefix`, `decode_encode_append`, `decNat_replicate_true`, `decGate_bad_tag` | `Audit/Syntax.lean` (30 reports with Q13) | — |
| Q33 | integrated_verified (local) | `QIP.Arithmetic.Gap`, `.Padding`, `.Repetition`: `halving_gap`, `halving_iterate`, `padCount_le`, `halfCount_iterate_padM`, `four_pow_le_padM_sq`, `one_sub_pow_le_inv`, `repetition_bound`, `repK_le_poly`, `soundness_schedule` | `Audit/Arithmetic.lean`: 24 reports | — |
| Q07–Q12, Q15–Q32, Q34–Q41 | not_started | — | — | — |

## Design decisions recorded for later tasks

- **Wire layout (Q13).** Private wires come first (`0 … priv-1`, output `out < priv`). Each
  message then gets a fresh register of its own width, in order. Block `j` runs before message
  `j`. During block `j` the verifier holds every received prover→verifier register `k < j` and
  every unsent verifier→prover register `k ≥ j` (initially `|0⟩`). Q15's execution semantics and
  Q29's fixed-register normal form must follow this convention.
- **Schedules.** `QIPm k` should use `HasSchedule k`: exactly `k` alternating messages, the last
  to the verifier. `stdSchedule 3 = [P→V, V→P, P→V]`.
- **Encoding.** Unary naturals and gate tags 0–4 follow `ShiBQP.encNat`/`encInstr`, so the
  Q34 printers can reuse the proved unary parsers. `encode_length` makes the serialized size an
  exact, closed-form resource.
- **Constants (Q33).** Bell-test soundness is `35/36 = 1 - 1/36`. Padding goes to
  `padCount m ≤ 2m + 3`, of the form `2^(r+1)+1`. With `δ = 1/(36 M²)` and `K = 72 M²`,
  `soundness_schedule` composes these with `r` halvings.
- The baseline `bqp-pp/src/Theorems/*` files are all `sorry` stubs; reuse must come from the
  proved top-level `BQP-*` and `AMPUNI-*` modules.

## Next ready tasks

Q07 (Choi/Kraus; Q06 is done), Q09 (purification; Q05 and Q03 are done) and Q34 (printer
primitives; Q14 is done). Conventions fixed by Q03: positivity is Mathlib's `Matrix.PosSemidef` with `ComplexOrder`
and `MatrixOrder`; every Hilbert norm or inner product on coordinate vectors goes through
`toE` (`EuclideanSpace`), never the sup norm on `n → ℂ`.

## Review gate after Q06 (pending human review)

The plan asks for a review of norm, order, channel and protected-register conventions here.
These are the conventions to check:

- **Order and positivity:** Mathlib `Matrix.PosSemidef`, scopes `ComplexOrder` and `MatrixOrder`
  (Q03).
- **Norms and inner products:** only through `toE` and `EuclideanSpace`, with the operator norm
  from `Matrix.Norms.L2Operator` (Q03).
- **Complete positivity:** `IsCP Φ` quantifies over every finite ancilla `k : Type` (universe 0;
  all registers in this development live in `Type`). It is proved equivalent to Mathlib's
  `CompletelyPositiveMap` condition (`isCP_iff_cpMap`). The transpose map separates positivity
  from complete positivity.
- **Trace preservation:** `IsTP Φ` is `trace (Φ X) = trace X` for **all** `X`, not only density
  operators. It is a predicate on the same linear map.
- **Protected registers:** in `liftR k Φ` the left register `k` is untouched. `traceRight_liftR`
  shows a trace-preserving `Φ` cannot change the `k` marginal. Q15 must model prover actions as
  `liftR` with verifier-private registers on the left, after the appropriate `reindexMap`.
