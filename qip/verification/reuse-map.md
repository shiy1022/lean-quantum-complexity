# Reuse map (Q00)

Baseline: repository commit `512c976` (plan commit; all sources identical to `1a076aa`).
Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Baseline paths are under
`bqp-pp/src/` and consumed read-only through the `Baseline` library in `qip/lakefile.toml`.
Only the Lake roots listed there are built for qip; `scripts/manifest.py` checks that each root is
a published bqp-pp module and that its hash is unchanged.

Status: **used** = imported by a qip module; **candidate** = to be inspected when the named task
starts (statement and source closure not yet audited for qip); **not used** = deliberately avoided.

| Declaration / file | Source | Status | Use |
|---|---|---|---|
| `ShiShallow.Instr`, `Instr.apply`, `hMat`, `sMat`, `tMat`, `xMat`, `cnotState`, `runLayered` | `Definitions/Def_ShiShallow_Core.lean` | used (definitions only) | gate meanings; `ShiQIP.Gate.toInstr?` maps descriptions to `Instr n` without new semantics; Q16 bridge |
| `PvsNP.Str`, `PvsNP.PolyTimeComputable` | `Definitions/Def_PvsNP.lean` | Lake root, not yet imported | Q15 generator uniformity, Q34 printers. `ShiQIP.Str` is the same type `List Bool` |
| `ShiBQP.encNat` (`replicate k true ++ [false]`), `encInstr` tags 0–4 | `Definitions/Def_ShiBQP_Core.lean` | convention mirrored, not imported | `ShiQIP.encNat` and gate tags use the same convention so that Q34 can reuse the unary parsers; the equality `ShiQIP.encNat = ShiBQP.encNat` is `rfl` and will be stated when Q34 imports that file |
| `ShiBQP.encStr` | same | not used | not injective (documented in its source); qip's `encList` relies on a proved self-delimiting decoder instead |
| `ShiClassQMA.QMA` folded witness/ancilla encoding | `qma-amplification` | not used | plan §3.3; qip descriptions store every register size separately |
| unary parser / pair codec / general polytime transducers (`BQP-unary-parser`, `BQP-pair-codec`, `BQP-general-polytime`, `BQP-typed-polytime`) | `bqp-pp/src` | candidate | Q34 primitives |
| machine run, frame and peak lemmas (`Space/Run.lean`, `Frame.lean`, `PeakComposition.lean`) | `bqp-pspace/src` | candidate | Q34 clocked loops. Importing them would add the bqp-pspace root; decide in Q34, keeping one definition per module name |
| QMA selector / readout circuits (`AMPUNI-selector-circuit`, `AMPUNI-readout-schedule`) | `qma-amplification` | candidate | Q28 control templates, only after exporting and auditing the exact source closure |
| reversible simulation (RV01) | external, unfinished | not used | only optional O02 may depend on it |

Mathlib API inventory (Q01) is in [mathlib-api.md](mathlib-api.md).
