# Quantum complexity in Lean

Lean 4 formalizations of quantum complexity, currently covering **BQP ⊆ PP** and **copy-based QMA amplification**. This repository continues the history of `qma-amplification-lean`.

| Project | Main result | Verification status |
|---|---|---|
| [BQP ⊆ PP](bqp-pp/) | `ShiBQP.bqp_subset_pp : ShiBQP.BQP ⊆ ShiClassPP.PP` | Clean Sherlock rebuild: 306 project modules, zero reused project outputs, 275 selected axiom reports |
| [QMA amplification](qma-amplification/) | `ShiQMAGeneralGap.QMAWith_general_threshold_amplification` | Copy-based endpoint checked and axiom-audited in its source workspace; publication details in the project README |

The QMA construction uses polynomially many witness copies. Its separate witness-preserving Marriott–Watrous mission remains open; the mission statements are explicitly marked as unfinished.

## Layout

- `bqp-pp/src/`: the exact verified source graph for the BQP inclusion, including its reference dependencies and shared machinery.
- `bqp-pp/verification/`: portable source/build evidence and axiom reports from the completed clean rebuild.
- `qma-amplification/`: the existing QMA project, including proofs, platform submissions, provenance, and the open mission draft.

Each project has its own Lean build environment. Both pin **Lean 4.33.1** and **Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`**. Keeping their source roots separate preserves their verified imports where reference module names overlap. Source headers and QMA Git history are preserved.

## Verification and building

See each project's README for commands and the scope of its verification. For this workspace, **run all Lean compilation on Sherlock**, inside a Slurm compute allocation. Source-manifest checks use Python and do not invoke Lean.

The BQP endpoint's transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`; there are no extra compiler, runtime, or checker hypotheses. Some imported reference statement files and the separate QMA mission drafts contain `sorry`. The endpoint axiom audits distinguish proved results from those statements; the repository does not claim every theorem stub is proved.

Code is distributed under [Apache 2.0](LICENSE). Individual source files retain their authorship headers.
