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
took 126 s and produced 120 reports across 5 audit files (18 sources), from `git_head`
4c72114 plus the Q03 changes. Source hashes are in `source-manifest.json` and `verification/audit.json`.

| Task | Status | Declarations / files | Evidence | Remaining gap |
|---|---|---|---|---|
| Q00 | integrated_verified (local) | `lakefile.toml`, `lake-manifest.json`, `scripts/manifest.py`, `scripts/audit.py`, `verification/baseline.json`, `verification/reuse-map.md`, `QIP.Smoke` | audit and manifest self-tests reject missing, duplicate, forbidden and unrequested reports and tampered manifests. bqp-pp (306 hashes) and bqp-pspace manifests re-verified. `Audit/Smoke.lean`: 1 report | acceptance asks for the smoke audit **on Sherlock** — not done |
| Q01 | integrated_verified (local) | `Quantum.MathlibImports`, `verification/mathlib-api.md` | 64 `#check`s and 6 examples compile; `CFC.sqrt`, the factorization `A = Bᴴ B`, the L2 operator norm and the CP-map type are instantiated on complex matrices | none for this task; absences routed to Q03–Q11 and Q22–Q23 |
| Q02 | integrated_verified (local) | `Quantum.Registers`, `Quantum.Reindex`: `qubitsAppend`, `regAssoc`/`regSwap`/`regUnitRight`, `permMat`, `reindexState`, `permMat_conj`, `kron_regAssoc`, `kron_regSwap`, `reindex_regSwap_twice`, `kron_regUnitRight`, `qubitsAppend_zero_right_eq` | `Audit/Registers.lean`: 29 reports | — |
| Q03 | integrated_verified (local) | `Quantum.Positive`, `Quantum.HilbertBridge`: `posSemidef_iff_exists_mul_conjTranspose`, `psdSqrt` (= `CFC.sqrt`) with `psdSqrt_posSemidef`/`_mul_self`/`_unique`, `trace_reindex`, `trace_conj_unitary`, `psd_trace_mul_nonneg`, `trace_mono`, `trace_mul_mono`, `conj_mono`, `kronecker_mono_left/right`, `trace_rankOne`, `trace_mul_rankOne`; `toE`, `inner_toE`, `norm_toE_sq`, `norm_mulVec_le` (L2 operator norm), `norm_toE_unitary`, `inner_toE_mulVec_eq_trace`, `supNorm_lt_norm_toE` | `Audit/Positive.lean`: 36 reports. Non-diagonal complex test matrix `testMat = !![2, I; -I, 2]` (PSD, `trace = 4`, square root, `trace (testMat · v v†) = 6`) | — |
| Q13 | integrated_verified (local) | `QIP.Syntax`, `QIP.Resources`: `Desc`, `Gate`, `Message`, `Desc.held`, `Desc.check`/`Valid`, `stdSchedule`, `HasSchedule`, `gateCount`, `totalWires`, `communication`, `serialSize`, `Desc.serialSize_le`, `Gate.toInstr?` | `Audit/Syntax.lean`. 1-, 2-, 3- (zero-width middle message) and 5-message examples are valid by `decide`. Negative examples cover use-after-send, use-before-receive, `cnot i i`, an output outside the private register, a zero-width private register, non-alternation and a verifier-first schedule | gate *semantics* bridge is Q16 |
| Q14 | integrated_verified (local) | `QIP.Encoding`, `QIP.Decode`: `encode`, `decode`, `decodeChecked`, `decode_encode`, `encode_injective`, `decode_eq_some_iff`, `encode_length` (= `serialSize`), `encode_length_le`, `decode_proper_prefix`, `decode_encode_append`, `decNat_replicate_true`, `decGate_bad_tag` | `Audit/Syntax.lean` (30 reports with Q13) | — |
| Q33 | integrated_verified (local) | `QIP.Arithmetic.Gap`, `.Padding`, `.Repetition`: `halving_gap`, `halving_iterate`, `padCount_le`, `halfCount_iterate_padM`, `four_pow_le_padM_sq`, `one_sub_pow_le_inv`, `repetition_bound`, `repK_le_poly`, `soundness_schedule` | `Audit/Arithmetic.lean`: 24 reports | — |
| Q04–Q12, Q15–Q32, Q34–Q41 | not_started | — | — | — |

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

Q04 (density operators and effects; Q03 is done) and Q34 (printer primitives; Q14 is done).
Q04 → Q05 → Q06 continues the quantum foundations lane, with the plan's hard review gate after
Q06. Conventions fixed by Q03: positivity is Mathlib's `Matrix.PosSemidef` with `ComplexOrder`
and `MatrixOrder`; every Hilbert norm or inner product on coordinate vectors goes through
`toE` (`EuclideanSpace`), never the sup norm on `n → ℂ`.
