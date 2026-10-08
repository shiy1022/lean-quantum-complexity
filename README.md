# Quantum complexity in Lean

Lean 4 formalizations of quantum complexity, currently covering **BQP ⊆ PP**, **BQP ⊆ PSPACE** (in a corrected finite-multistack space model), **copy-based QMA amplification**, **QIP = QIP(3)**, and **efficient reversible simulation**. This repository continues the history of `qma-amplification-lean`.

| Project | Main result | Verification status |
|---|---|---|
| [BQP ⊆ PP](bqp-pp/) | `ShiBQP.bqp_subset_pp : ShiBQP.BQP ⊆ ShiClassPP.PP` | Clean Sherlock rebuild: 306 project modules, zero reused project outputs, 275 selected axiom reports |
| [BQP ⊆ PSPACE](bqp-pspace/) | `ShiBQP.bqp_subset_pspace : ShiBQP.BQP ⊆ ShiSpace.PSPACE` (via `ShiSpace.pp_subset_pspace`) | Checked locally on a Windows workstation (not Sherlock): 28 modules, 102 axiom reports, corrected finite-multistack PSPACE |
| [QIP = QIP(3)](qip/) | `ShiQIP.qip_eq_qip3 : ShiQIP.QIP = ShiQIP.QIPm 3` | Checked by a from-scratch local build on a Windows workstation (not Sherlock): 154 sources, 43 audit files, 2439 axiom reports, only `propext`/`Classical.choice`/`Quot.sound` |
| [QMA amplification](qma-amplification/) | `ShiQMAGeneralGap.QMAWith_general_threshold_amplification` | Copy-based endpoint checked and axiom-audited in its source workspace; publication details in the project README |
| [Efficient reversible simulation](reversible-simulation/) | `ShiReversibleGenerator.efficient_reversible_simulation` | Clean Sherlock build: 885 modules, 2724 axiom checks, 1770 verified source/object hashes |

The QMA construction uses polynomially many witness copies. Its separate witness-preserving Marriott–Watrous mission remains open; the mission statements are explicitly marked as unfinished.

## Layout

- `bqp-pp/src/`: the exact verified source graph for the BQP inclusion, including its reference dependencies and shared machinery.
- `bqp-pp/verification/`: portable source/build evidence and axiom reports from the completed clean rebuild.
- `bqp-pspace/`: the corrected PSPACE model, the PP ⊆ PSPACE enumerator, and the BQP ⊆ PSPACE composition. It consumes `bqp-pp/src` read-only.
- `qip/`: quantum interactive proofs with polynomially many messages, parallelized to three messages (Kitaev–Watrous), with concrete polynomial-time TM2 printers for the transformed verifiers. It consumes `bqp-pp/src` read-only; see [the plan](plans/QIP_THREE_MESSAGE_PLAN.md).
- `reversible-simulation/`: exact clean polynomial-time-uniform simulation of polynomial-time classical TM2 computations, with a self-contained verified source graph and audit evidence.
- `qma-amplification/`: the existing QMA project, including proofs, platform submissions, provenance, and the open mission draft.

Each project has its own Lean build environment. These projects pin **Lean 4.33.1** and **Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`**. Keeping their source roots separate preserves their verified imports where reference module names overlap. Source headers and QMA Git history are preserved.

## BQP ⊆ PSPACE

[`bqp-pspace/`](bqp-pspace/) carries out the [execution plan](plans/BQP_PSPACE_PLAN.md). It defines a corrected polynomial-space class: a total machine with a polynomial bound on the stacks of every reachable configuration, and no time bound. It proves PP ⊆ PSPACE by a concrete enumerator that reuses its workspace, and composes the published BQP ⊆ PP theorem unchanged. The class is a finite-multistack model; no equivalence with other PSPACE formulations is claimed. This result has been checked locally, not yet on Sherlock.

## Verification and building

See each project's README for commands and the scope of its verification. For this workspace, **run all Lean compilation on Sherlock**, inside a Slurm compute allocation. Source-manifest checks use Python and do not invoke Lean.

The BQP endpoint's transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`; there are no extra compiler, runtime, or checker hypotheses. Some imported reference statement files and the separate QMA mission drafts contain `sorry`. The endpoint axiom audits distinguish proved results from those statements; the repository does not claim every theorem stub is proved.

Code is distributed under [Apache 2.0](LICENSE). Individual source files retain their authorship headers.
