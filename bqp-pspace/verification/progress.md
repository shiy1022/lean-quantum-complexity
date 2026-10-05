# PP ⊆ PSPACE progress ledger

Evidence kind: **local check** = `python scripts/audit.py` on the Windows workstation
(Lean 4.33.1, pinned Mathlib cache, `lake build ShiSpace` + fresh-import axiom audits).
Per the user's 2026-10-05 instruction, compilation runs locally rather than on Sherlock; no row
below is Sherlock clean-build evidence. Status vocabulary: not started / in progress /
verified (locally) / blocked.

| Task | Status | Paths | Source sha256 (prefix) | Evidence | Next obligation |
|---|---|---|---|---|---|
| S00 | verified (locally) | `verification/reuse-map.md`, `lakefile.toml`, `scripts/audit.py` | — | baseline `Baseline` lib builds via Lake; audit self-test passes | — |
| S01 | verified (locally) | `src/Space/Model.lean`, `src/Audit/Space.lean` | `b80b11082fcd` | 9 axiom reports ⊆ {propext, Classical.choice, Quot.sound}; exact-type unfolding of `PolySpaceDecider` in audit | — |
| S02 | not started | `src/Space/Run.lean`, `Frame.lean`, `PeakComposition.lean` | | | run-prefix API |
| S03 | not started | | | | |
| S04 | not started | | | | |
| S05 | not started | | | | |
| S06 | not started | | | | |
| S07 | not started | | | | |
| S08 | not started | | | | |
| S09 | not started | | | | |
| S10 | not started | | | | |
| S11 | not started | | | | |
| S12 | not started | | | | |
| S13 | not started | | | | |
| S14 | not started | | | | |
| S15 | not started | | | | |
| S16 | not started | | | | |
