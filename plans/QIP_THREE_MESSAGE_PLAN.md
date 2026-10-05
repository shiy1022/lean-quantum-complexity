# QIP = QIP(3): implementation plan and execution contract

Prepared 2026-10-05 for an executor that needs small tasks, explicit dependencies and verifiable stopping points. **Status: planning only. No QIP theorem has been implemented or compiled by this planning pass.** Suggested module/declaration names below are design contracts, not claims that the declarations already exist or that schematic signatures compile.

The companion [task manifest](QIP_THREE_MESSAGE_TASKS.json) contains 42 required tasks and two optional compatibility tasks. This document is the authoritative mathematical/design specification. The manifest supplies scheduling information; it does not certify a theorem.

## 1. Fixed objective, scope and current evidence

Required public endpoint, after defining the classes independently:

```lean
-- Proposed endpoint, over the same newly defined type of promise problems.
theorem ShiQIP.qip_eq_qip3 : ShiQIP.QIP = ShiQIP.QIPm 3
```

`QIPm 3` means exactly three directed messages, in the order prover → verifier → prover → verifier. It does not mean three exchanges, three verifier gates, or three alternating circuit layers. `QIP` permits polynomially many messages. Both classes use a polynomial-time classical generator for an explicit verifier circuit description and thresholds 2/3 and 1/3.

The target is a proved transformation of quantum interactive verifiers over the established H/S/T/X/CNOT gate semantics, plus the class equality. The proof must work against arbitrary finite-dimensional private prover memory and arbitrary prover channels. It must construct the transformed verifier and its actual polynomial-time generator. No compiler, uniformity, perfect-completeness, purification, causal-realization, SDP-duality or parallel-repetition premise may remain in the endpoint.

This is a gate-set-specific formal class equality. Do not additionally claim equivalence with every textbook gate model, arbitrary efficiently approximable gate descriptions, or all quantum machine models without proving the relevant model-equivalence theorem.

### 1.1 GitHub baseline actually inspected

Repository: [shiy1022/lean-quantum-complexity](https://github.com/shiy1022/lean-quantum-complexity).

`origin/main` was fetched and the clean local checkout fast-forwarded to **`1a076aa72e73b0766baebbf9503faa3f87751306`**. GitHub showed one branch (`main`) and no open PRs at inspection time. Recheck this at execution start; this is a snapshot, not a lock on other work.

| Existing work | Exact evidence at this baseline | Use in this plan |
|---|---|---|
| BQP ⊆ PP | `bqp-pp/src/BQP-final-inclusion.lean`; 306-module clean Sherlock build, 275 axiom reports | Preserve definitions/circuit semantics; reuse small proved encoding/transducer machinery |
| PP ⊆ PSPACE | `bqp-pspace/src/PPToPSPACE.lean`: `ShiSpace.pp_subset_pspace` | Proved; not a lemma needed for QIP parallelization |
| BQP ⊆ PSPACE | `bqp-pspace/src/BQPToPSPACE.lean`: `ShiBQP.bqp_subset_pspace` | Proved containment, not BQP = PSPACE and not QIP = PSPACE |
| Space infrastructure | `Space/Run.lean`, `Space/Frame.lean`, `Space/PeakComposition.lean`, `Space/ReachableAlphabet.lean`, `Space/TimeToSpace.lean` | Optional reusable actual-machine run, frame and resource lemmas for classical printers |
| BQP–PSPACE audit | `bqp-pspace/verification/local-clean-build.json` and `local-audit.json`: 306 baseline + 28 new modules, zero reused project outputs, 102 reports, 845 seconds | Existing verification was on a Windows workstation, **not Sherlock**; do not relabel it |
| Copy-based QMA amplification | `qma-amplification/proofs/AMPUNI-arithmetic-front.lean`: `ShiQMAGeneralGap.QMAWith_general_threshold_amplification` | Reuse applicable lemmas only; not an interactive parallel-repetition theorem |
| Corrected QMA uniformity | `qma-amplification/Definitions/Def_ShiClassQMAU.lean` | Important encoding precedent: witness size and ancilla size are separate fields |

The new space class is `ShiSpace.PSPACE`, defined by a total finite-multistack decider and a polynomial bound on **every reachable configuration**, without a time bound. The project explicitly does not assert equivalence with a traditional single-tape/read-only-input PSPACE model. Preserve that documented scope.

The planning pass ran only lightweight source checks:

```text
python3 bqp-pp/scripts/verify.py
  Verified 306 source hashes and dependency closure
python3 bqp-pspace/scripts/manifest.py --check
  Manifest verified
```

No new compilation was performed. The toolchain remains Lean **4.33.1**, Mathlib **`0df444a360eaa60ab8c11dca51a86af692955474`**.

### 1.2 Reversible simulation is an external, unfinished development

It is not present as a completed theorem in the inspected GitHub tree. The separate local `quantum-theorem-backlog/reversible-simulation/` project and its `REVERSIBLE_SIMULATION_PLAN.md` were inspected read-only.

Its accepted report says **r67: 85 modules, 421 audited declarations**, with `full_machine_uniform_simulation_proved = false`. It certifies semantic clean simulation and polynomial circuit resources. Its concrete full polynomial-time circuit generator remains open. Later focused/draft work, including prepared r69 and arithmetic-composition work, is not a substitute for an accepted full endpoint. Recheck the actual accepted report before reusing any of it; do not resume or change that task merely to execute this plan.

Distinguish three different operations:

1. **Reverse a known quantum circuit:** reverse its gate list and replace each gate with its adjoint. This is a small exact transformation, Q28. It does not need general reversible Turing-machine simulation.
2. **Print a transformed verifier description classically:** prove an ordinary TM2 polynomial-time string transducer. This is Q34–Q39 and can be built from existing machine primitives without an unconditional reversible compiler.
3. **Run an input-dependent classical generator coherently inside a unary-length-uniform quantum family:** this can benefit from the future reversible theorem, but also needs a proved universal evaluator. This is optional O02, not a prerequisite of the primary QIP equality.

**No required Q00–Q41 task depends on the unfinished reversible theorem.** Accepted small gate/cleanup lemmas may be reused only after their exact source closure is exported and audited; otherwise prove the fixed finite gate templates independently. Do not add a `ReversibleSimulation` hypothesis to the final class equality.

## 2. Chosen proof route and concrete parameters

Use three proved protocol transformations:

```text
bounded-error protocol
    → perfect-complete protocol
    → padded protocol, repeatedly halved to three messages
    → batched all-pass repetition, still three messages
```

The classic target is due to Kitaev–Watrous. For implementation, use the iterative midpoint construction described by Vidick–Watrous, originating in Kempe–Kobayashi–Matsumoto–Vidick, rather than reconstructing every historical proof route. Use strategy operators/dual certificates for the product bound, giving the project useful infrastructure in its own right. References and their roles are listed in Section 9.

### 2.1 Fix the constants instead of solving unnecessary generalizations

The starting thresholds are `c=2/3`, `s=1/3`. Use the **fixed half-threshold Bell-test** perfect-completeness construction. Its Bell measurement uses exact H/CNOT operations. A prover-controlled reject option permits an honest success probability exactly 1/2; the unrestricted prover supplies the necessary state. The verifier does not compute that probability or implement its real-valued rotation.

Accept the conservative intermediate bound:

- after perfect completeness: completeness 1, soundness at most `35/36`, and two extra messages;
- after padding to `M = 2^(r+1)+1` and `r` halvings: exactly three messages and soundness at most `1 - 1/(36*M^2)`;
- choose `K = 72*M^2` parallel copies with AND acceptance.

These constants are a proposed conservative instantiation to prove, not assumed compiler specifications. Q27, Q31, Q32 and Q33 must establish them for the actual constructions.

The scalar endgame uses

\[
\delta=\frac{1}{36M^2},\qquad K=72M^2,\qquad
(1-\delta)^K\le\frac{1}{1+K\delta}=\frac13.
\]

Perfect completeness is preserved by AND repetition. The repeated protocol batches each directed message, so the total remains three. Soundness must be proved against an arbitrary joint prover strategy across all copies.

If `p(n)` bounds the original message count, adding two turns and then choosing the first suitable power-of-two-plus-one gives a conservative polynomial bound such as `M ≤ 2*(p(n)+2)+1`, after the parity/base-case normalization is proved. Therefore `K` has a fixed polynomial upper bound. Use offsets so the proof includes inputs of length zero and one. Track **padded M** throughout; tighter constants are not required.

### 2.2 Avoid premature stronger targets

The required result does not need:

- arbitrary completeness/soundness functions or exact synthesis for arbitrary dyadic target states;
- exponentially small final error, variable-threshold majority repetition, or an OR repetition theorem;
- a numerical SDP algorithm, matrix multiplicative weights, QIP = PSPACE or IP = PSPACE;
- witness-preserving QMA amplification;
- exact optimizer formulas when an upper inequality closes the argument;
- a bridge to every equivalent uniformity or gate model.

The general strategy representation theorem remains on the main route because it supplies operational meaning, a bounded-memory realization, compact optimization and the dual product proof. Prove the three-message product case first if that avoids a general theorem with extra indexing complexity.

## 3. Representation decisions the executor must preserve

### 3.1 Linear algebra and registers

Use finite complex matrices with Mathlib's PSD/Loewner order. Use finite nonempty basis types for generic quantum states and `Bits n`/an equivalent finite type for qubits. A zero-qubit register has dimension one. Matrix coordinates, Euclidean inner products and operator norms must be connected explicitly; the default norm on a raw function space may be the wrong norm.

Define density operators as PSD matrices with trace one and acceptance as the real part of a trace pairing. Keep a single documented root-fidelity convention. Include tensor-factor order in all channel, Choi, partial-trace and tester definitions; prove reindexing rather than relying on textual resemblance.

Prefer reusable finite-dimensional lemmas. Do not build infinite-dimensional quantum theory unless a concrete required result cannot be specialized from existing Mathlib.

### 3.2 Verifier and prover models

A verifier is given by finite gate descriptions with explicit ownership and message boundaries. The core may use unitary blocks with all private ancillas allocated initially and one final measured accept bit. Prove the normal-form translations for any additional preparation/discard/classical-control syntax that is offered. Do not allow an arbitrary dense channel matrix to masquerade as an efficient verifier instruction.

A prover may use arbitrary finite private memory and arbitrary channels. Completeness quantifies existentially over an honest prover for each yes input. Soundness quantifies universally over all provers for each no input. No circuit complexity bound is placed on the prover, and its private dimension is not fixed by the definition of QIP. A dimension bound may only be used after a realization theorem proves it without changing the optimum.

Input-dependent verifier descriptions are generated by an actual `PvsNP.PolyTimeComputable` function on `x`. Any required classical input state is prepared by explicit gates in that description. This is the primary uniformity convention for this project; it does not require running a classical generator coherently on a superposition.

The challenge used in halving must be generated **after** the initial midpoint message. Retain a verifier-private record. Sending a public copy is allowed, but a returned prover-controlled bit cannot replace the protected branch choice. A coherent implementation must be proved equivalent to the required classical mixture for acceptance, even against a malicious prover.

### 3.3 New class definitions, with compatibility theorems kept separate

Define a disjoint yes/no `PromiseProblem`. Define the message-bounded and polynomial-message classes separately from their operational witnesses; the desired equality must not be part of either definition. Provide an embedding of existing total languages as `(L, complement L)`.

Specify exactly which finite gate model and generator convention are used. The old repository's `ShiClassQMA.QMA` has folded witness/ancilla uniformity; `ShiClassQMAU.QMAU` corrects it. Do not infer a formal equality with the new one-message class from the textbook identity alone. O01/O02 separate the semantic and uniformity issues.

### 3.4 Classically executable transformations

There are two distinct proofs for each transformation:

1. the mathematical output protocol has the stated acceptance behavior;
2. a **concrete finite machine** prints exactly its encoding in polynomial time.

A polynomial-size noncomputable circuit family is insufficient. A recursively defined Lean function is insufficient. An arbitrary polynomial-space generator is insufficient. The exact byte equality must connect the machine output to the same verifier used in the soundness theorem.

All printers must be total on arbitrary input strings, with specified malformed-input behavior. Their finite control may depend on a fixed transformation or source machine, never on input length. The protocol decoder must expose every register boundary; in particular, do not lose witness/message dimensions by storing only total width.

For iterated compression, track primitive gate count `G`, live/allocated width `W`, messages and encoded size separately. After fixed-size control macros, prove recurrences with fixed multiplicative constants. If a recurrence is `G' ≤ C*G + C*W + C*M`, choose a fixed integer `d` with `C+constant ≤ 2^d`, and use `(2^d)^r = (2^r)^d` together with the padded message count. An arbitrary polynomial-size transformation iterated logarithmically often is not automatically polynomial-size. Unary wire indices also need an explicit encoding-length bound.

## 4. Concrete reuse map

Inventory these **existing paths**, rather than assuming all suggested APIs are present:

| Area | Candidate sources | Required caution |
|---|---|---|
| PSD order and square roots | Mathlib `Analysis/Matrix/Order.lean`, `Analysis/Matrix/PosDef.lean`, `Analysis/Matrix/HermitianFunctionalCalculus.lean` | Order is scoped; show every square-root argument is PSD |
| Spectrum and trace | Mathlib `Analysis/Matrix/Spectrum.lean`, `LinearAlgebra/Matrix/Trace.lean` | Confirm real/complex trace and Hilbert norm conventions |
| CP maps | Mathlib `Analysis/CStarAlgebra/CompletelyPositiveMap.lean` | Already exists; bridge its CStarMatrix API to the chosen finite matrix API |
| Tensor/reindexing | Mathlib finite tensor and Kronecker APIs; project `Def_ShiTensor_Core` | Fix tensor order; avoid importing duplicate modules from two project roots |
| Gate semantics | `bqp-pp/src/Definitions/Def_ShiShallow_Core.lean` and `Def_ShiBQP_Core.lean` | Preserve gate meanings; declaration comments can be historical, so verify actual theorem contracts |
| Circuit and family encoding | Existing `ShiBQP.encNat`, `encInstr`, `encLayer`, `encCirc`; accepted reversible parser work if exported | `encStr` alone is not an injective arbitrary nested-list codec |
| Small transducers | `bqp-pp/src/BQP-general-polytime.lean`, `BQP-pair-codec.lean`, `BQP-pair-generation.lean` and selected AMPUNI machine modules | Reuse actual certificate statements and their source closures, not amplification-specific assumptions |
| Machine runs and frames | New `bqp-pspace/src/Space/Run.lean`, `Frame.lean`, `PeakComposition.lean` | Space bounds do not by themselves supply the polynomial runtime required for uniformity |
| Exact control gates | Selected QMA `AMPUNI-selector-circuit`, `AMPUNI-readout-schedule`, recovered reference closures; accepted reversible gate modules | Some proofs are reconstructed by metaprograms; audit the produced declaration and export the full source closure |

At planning time, partial trace/purification/Uhlmann/strategy APIs were not established in this repository. This is an inventory conclusion, not a claim that every relevant Mathlib lemma is absent. Q01 resolves exact reuse before new definitions are committed.

Keep generic mathematical modules under `qip/src/Quantum/` and protocol/complexity modules under `qip/src/QIP/`. This makes later extraction into a shared library possible without making a repository-wide reorganization a prerequisite.

## 5. Dependency order, cheap work and hard review gates

The required dependency DAG is in [QIP_THREE_MESSAGE_TASKS.json](QIP_THREE_MESSAGE_TASKS.json). Dependencies denote accepted contracts, not merely the existence of files.

| Lane | Work that can start early | What eventually blocks it |
|---|---|---|
| Build/provenance | Q00 then Q01 | Access to Sherlock for real checks |
| Registers/syntax | Q02 → Q13 → Q14 | None of the hard quantum theorems |
| Scalar estimates | Q33 immediately after Q00 | No quantum dependency; use the constants fixed in Section 2 |
| Basic states | Q03 → Q04 → Q05 → Q06 | Mathlib representation bridges |
| Classical printers | Q34 after Q14 | Exact semantic descriptions for final specialized printers |
| Quantum foundations | Q07–Q12 | Dilation, purification and Uhlmann are substantial proofs |
| Strategy optimization | Q18–Q24 | Realization and duality; do not replace them with assumptions |
| Compression | Q26–Q32 | Perfect completeness, cut stitching and adversarial soundness |
| Final uniform family | Q35–Q40 | Semantic contracts plus actual printer/runtime proofs |

A useful first execution packet is **Q00, Q01, Q02, Q13, Q14 and Q33**. Complete these small interfaces and standalone inequalities before attempting several hard theories at once. Q34 can then progress while the mathematics is being developed.

Recommended hard review checkpoints:

- After Q06: verify norm/order/channel conventions and protected-register semantics.
- After Q11: review the exact purification dimensions and root-fidelity convention.
- After Q19: review both directions of operational/causal equivalence and the memory bound.
- After Q23: review the actual strong-duality argument and strict-feasibility witness.
- After Q27: verify the honest reject-flag strategy and the 35/36 bound with no arbitrary verifier rotation.
- After Q31: review quantifier order, challenge timing and the cut-state stitching proof.
- After Q37: review the real finite printer, byte equality and polynomial recurrence.
- Before Q41: unfold class definitions and audit the exact endpoint type.

These are mathematical review points. They do not authorize assuming a missing lemma. A less capable executor may handle many small tasks, but this plan cannot turn Uhlmann, realization, duality or compression soundness into routine `simp` work. If a hard task stalls, report the smallest missing statement and move to another task with satisfied dependencies. Do not silently weaken the target.

## 6. Task cards

Every file named below is a proposed new file under `qip/`. Split a task into focused files when needed, retaining the same external contract. A task is accepted only after source-matched compilation and its required audits; a lemma ending in `sorry` never satisfies a dependency.

### Q00 — Freeze the baseline and establish the audit harness

Dependencies: none. Difficulty: **small**.

Files: `qip/verification/baseline.json`, `qip/verification/reuse-map.md`, `qip/scripts/manifest.py`, `qip/scripts/audit.py`.

**Contract:** Create qip/ as an independent pinned Lean project; preserve the existing projects byte-for-byte. Record the actual Git SHA, toolchain, imports and accepted evidence.

1. Read this plan and current Git status; do not overwrite concurrent edits.
2. Use module prefixes Quantum.* and QIP.* to avoid existing Space.*, Machine.* and Audit.* collisions. Import one selected baseline closure, never two different definitions with the same module name.
3. Reuse manifest/audit patterns from bqp-pspace, but change the compilation entry point to require a Sherlock allocation. Separate source-only checks from anything invoking Lean.
4. Create an audit parser self-test that rejects missing, duplicate and forbidden axiom reports.

**Acceptance:** Source manifests for both existing projects still pass; a tiny Mathlib-import module and its fresh audit pass on Sherlock.

**Do not:** Do not install a new toolchain, run local Lean, rewrite earlier class definitions, or count an imported theorem statement as a proved lemma.

### Q01 — Inventory the pinned Mathlib and proved quantum APIs

Dependencies: Q00. Difficulty: **small**.

Files: `qip/verification/mathlib-api.md`, `qip/src/Quantum/MathlibImports.lean`.

**Contract:** List exact available declarations and missing bridges for matrix order, square roots, tensor products, CP maps, compactness and separation.

1. Inspect the pinned files listed in Section 4, then use focused #check files on Sherlock.
2. Record the matrix norm and inner-product conventions, not just matching names.
3. For each reused project theorem record exact statement, source hash, and transitive axiom report.

**Acceptance:** The inventory distinguishes already proved, definition-only, stub, proposed and external-pending items.

**Do not:** Do not invent Mathlib lemma names or decide an entire theory is absent from one failed keyword search.

### Q02 — Finite registers and tensor reindexing

Dependencies: Q00. Difficulty: **small**.

Files: `qip/src/Quantum/Registers.lean`, `qip/src/Quantum/Reindex.lean`.

**Contract:** Explicit equivalences for ordered register products, associativity, swap, empty registers and qubit blocks.

1. Use finite nonempty basis types; zero qubits have a one-element basis.
2. Define reindexing matrices and state maps, and prove inverse, adjoint and composition laws.
3. Fix one tensor-factor order and prove named equivalences for every other view.

**Acceptance:** Associativity, swap twice, and adding/removing a zero-qubit register are exact identities.

**Do not:** Do not identify differently ordered tensors by informal notation or treat a zero-qubit space as dimension zero.

### Q03 — Positive matrices and finite-dimensional analytic bridges

Dependencies: Q01, Q02. Difficulty: **medium**.

Files: `qip/src/Quantum/Positive.lean`, `qip/src/Quantum/HilbertBridge.lean`.

**Contract:** Use Mathlib PSD/order and functional calculus to obtain factorization, positive square roots, trace positivity, and the correct Hilbert-space operator norm.

1. Bridge coordinate functions to EuclideanSpace rather than using the default Pi sup norm.
2. Prove the needed trace cyclicity, adjoint, conjugation and tensor positivity lemmas.
3. Factor a PSD matrix as A * Aᴴ; establish the rank-one trace and inner-product identities.

**Acceptance:** All later order/norm claims resolve to explicit Mathlib structures; tests include non-diagonal complex matrices.

**Do not:** Do not create a competing PSD definition or assume positivity is entrywise.

### Q04 — Density operators and effects

Dependencies: Q03. Difficulty: **small**.

Files: `qip/src/Quantum/State.lean`, `qip/src/Quantum/Measurement.lean`.

**Contract:** Density operators are PSD matrices with trace one; effects satisfy 0 ≤ E ≤ I; probability is Re(trace(Eρ)).

1. Prove probability lies in [0,1], complement probabilities sum to one, and affine mixtures preserve states.
2. Define rank-one pure states and prove normalization equivalence with squared-amplitude sums.
3. Define the maximally mixed state, including the one-dimensional case.

**Acceptance:** Pure-state measurement agrees with a direct sum of squared amplitudes.

**Do not:** Do not hide normalization, positivity or an acceptance bound in an unproved structure field.

### Q05 — Partial trace and locality

Dependencies: Q04. Difficulty: **medium**.

Files: `qip/src/Quantum/PartialTrace.lean`.

**Contract:** Partial trace preserves PSD/trace; tensor and local-operation identities are proved with explicit register order.

1. Start from partialTrace(M)[a,b] = sum_i M[(a,i),(b,i)].
2. Prove trace, tensor, reindexing and conjugation identities.
3. Derive marginal invariance under a trace-preserving operation on the other register once Q06 is available; place that corollary in Q06 to avoid an import cycle.

**Acceptance:** Check a Bell-state marginal, product states and tracing a zero-qubit register.

**Do not:** Do not claim a prover can change the verifier-only marginal without a message exchange.

### Q06 — Channels and their compositional API

Dependencies: Q05, Q01. Difficulty: **medium**.

Files: `qip/src/Quantum/Channel.lean`, `qip/src/Quantum/ChannelTensor.lean`.

**Contract:** A finite-dimensional channel is a linear completely positive trace-preserving map; composition, identity, tensor and local application are channels.

1. Bridge Mathlib CompletelyPositiveMap on CStarMatrix to the chosen finite matrix representation.
2. Keep trace preservation as a predicate of that same linear map.
3. Prove state preservation and no-signalling/local marginal invariance, and represent instruments with outcome-indexed CP maps.

**Acceptance:** Unitary conjugation, discard, preparation and dephasing are concrete channels.

**Do not:** Do not equate positivity with complete positivity or reset verifier-private memory when the prover acts.

### Q07 — Choi representation and Kraus realization

Dependencies: Q06. Difficulty: **hard**.

Files: `qip/src/Quantum/Choi.lean`, `qip/src/Quantum/Kraus.lean`.

**Contract:** Prove Choi/map inverse identities, CP iff Choi PSD, and TP iff the output partial trace is the input identity.

1. Freeze input/output order and matrix-unit conventions.
2. Prove the forward implication using the unnormalized maximally entangled vector.
3. Factor a PSD Choi matrix and reshape each factor column into a Kraus operator.
4. Prove the resulting Kraus sum is the original map and the normalization condition is exact.

**Acceptance:** Both directions are kernel checked, with input/output dimensions allowed to differ.

**Do not:** Do not define CP to mean Choi PSD and omit its equivalence with the channel API; do not normalize the Choi matrix as a density operator.

### Q08 — Finite-dimensional dilation

Dependencies: Q07. Difficulty: **hard**.

Files: `qip/src/Quantum/Dilation.lean`.

**Contract:** Every finite-dimensional channel has an isometric realization with an explicit finite environment; prove unitary extension after padding.

1. Stack the proved Kraus operators into an isometry.
2. Prove discarding its environment recovers the channel.
3. Bound environment dimension and extend the isometry to a unitary only on compatible padded spaces.

**Acceptance:** The realization works with entangled reference inputs, not just pure inputs of the acted-on system.

**Do not:** Do not infer an efficient verifier circuit from existence of an arbitrary channel dilation.

### Q09 — Purification and same-marginal isometries

Dependencies: Q05, Q03. Difficulty: **hard**.

Files: `qip/src/Quantum/Purification.lean`.

**Contract:** Every density operator has a finite purification; purifications of the same marginal are related on a sufficiently large private register.

1. Use the PSD square root to construct a canonical purification.
2. Prove its reduced state and normalization.
3. Prove the equal-marginal isometry/unitary lemma with explicit ancilla dimensions and rank-deficient cases.

**Acceptance:** Pure, mixed and rank-deficient states are covered; no full-rank assumption leaks out.

**Do not:** Do not import Uhlmann as an axiom or use a same-size unitary when the purifying dimensions differ.

### Q10 — Root fidelity and elementary laws

Dependencies: Q09. Difficulty: **medium**.

Files: `qip/src/Quantum/Fidelity.lean`.

**Contract:** Use one documented convention: root fidelity F(ρ,σ) = trace(sqrt(sqrt(ρ) σ sqrt(ρ))), a real number in [0,1].

1. Relate the square-root formula to the trace norm of sqrt(ρ)sqrt(σ).
2. Prove symmetry, pure-state overlap, diagonal specialization and tensor multiplicativity using finite matrix lemmas.
3. Keep every occurrence of F and F² distinct in theorem names/statements.

**Acceptance:** The pure-state formula is absolute inner product, while pure-state acceptance is its square.

**Do not:** Do not mix squared fidelity with root fidelity.

### Q11 — Uhlmann theorem with attained optimization

Dependencies: Q10, Q09. Difficulty: **hard**.

Files: `qip/src/Quantum/Uhlmann.lean`.

**Contract:** Maximum overlap over purifications equals root fidelity, with a sufficiently large common environment and an actual maximizing isometry.

1. Isolate the matrix polar/trace-optimization lemma first.
2. Prove its upper bound and optimizer construction, including zero singular values.
3. Translate through vectorization and Q09 to the purification statement; derive monotonicity under partial trace.

**Acceptance:** The theorem can supply a witness, not merely a supremum inequality.

**Do not:** Do not use a supremum as though it were attained or assume a polar factor is invertible.

### Q12 — Two-target fidelity inequality

Dependencies: Q11. Difficulty: **medium**.

Files: `qip/src/Quantum/FidelityTwoTargets.lean`.

**Contract:** For density operators ρ,σ,τ: F(ρ,σ)^2 + F(ρ,τ)^2 ≤ 1 + F(σ,τ). Only this upper bound is mandatory.

1. Prove the norm bound for the sum of two rank-one projections on unit vectors.
2. Choose Uhlmann purifications relative to a fixed purification of ρ.
3. Bound the mutual overlap of those purifications by F(σ,τ).

**Acceptance:** The inequality has no optimizer or protocol hypotheses and passes its own axiom audit.

**Do not:** Do not spend time proving the exact maximum identity unless the upper bound genuinely fails to close Q31.

### Q13 — Protocol syntax and resource accounting

Dependencies: Q02. Difficulty: **small**.

Files: `qip/src/QIP/Syntax.lean`, `qip/src/QIP/Resources.lean`.

**Contract:** Finite verifier descriptions explicitly store every private/message register size, alternation schedule, circuit block and output wire. Require a valid designated output qubit even when individual message or private auxiliary registers have zero qubits.

1. Count a message as one directed transfer; a three-message protocol is P→V, V→P, P→V.
2. Represent zero-length messages explicitly; all verifier gates use the established H/S/T/X/CNOT semantics.
3. Define gate count, total wires, communication and serialized-size targets before adding transformations.

**Acceptance:** Instantiate one-, two-, three- and five-message descriptions; size fields cannot conceal arbitrary functions.

**Do not:** Do not call an exchange of two messages one message or omit private/message register boundaries from the description.

### Q14 — Protocol encoding and strict decoder

Dependencies: Q13. Difficulty: **medium**.

Files: `qip/src/QIP/Encoding.lean`, `qip/src/QIP/Decode.lean`.

**Contract:** A self-delimiting Boolean encoding with decode(encode V) = some V, injectivity and a polynomial encoded-length bound.

1. Use tagged constructors with explicit arity and bounded wire checks.
2. Prove parsers retain arbitrary suffixes and reject malformed framing.
3. Encode all register sizes and each message boundary separately.

**Acceptance:** Round trip and malformed-input behavior cover empty lists and zero-qubit registers.

**Do not:** Do not assume a nested length-prefix/flatten operation is injective; do not reuse the older folded QMA witness/ancilla encoding.

### Q15 — Operational interaction and class definitions

Dependencies: Q06, Q13, Q14. Difficulty: **medium**.

Files: `qip/src/QIP/Execution.lean`, `qip/src/QIP/VerifierFamily.lean`, `qip/src/QIP/Classes.lean`.

**Contract:** Define actual interaction, completeness/soundness and independently defined QIP and QIPm. Quantify over all finite private prover memories and legal channels.

1. A verifier description is generated from x by a total PolyTimeComputable function; prepare any classical x register explicitly.
2. Keep prover initial memory uncorrelated with verifier-private initialized registers.
3. Use disjoint yes/no promise sets, with a language embedding (L, complement L).
4. Bound messages, wire counts, circuit sizes and generator runtime by natural-coefficient polynomials with room for n=0,1.
5. Define QIPm k by exactly k messages; QIP uses a polynomial bound on the generated message count.

**Acceptance:** Acceptance is in [0,1]; a dishonest prover has no action on private verifier registers; QIPm 3 ⊆ QIP is proved without compression.

**Do not:** Do not define QIP via QIPm 3, via an SDP, or via existence of the desired transformation. Do not bound prover circuit complexity.

### Q16 — Bridge existing circuit semantics

Dependencies: Q15. Difficulty: **medium**.

Files: `qip/src/QIP/CircuitSemantics.lean`, `qip/src/Quantum/ShiShallowBridge.lean`.

**Contract:** The density-channel action of each allowed circuit agrees with ShiShallow.runLayered on pure states and preserves the same gate meanings.

1. Prove each primitive gate identity, then circuit composition and register embedding.
2. Relate the designated output effect to existing amplitude-sum acceptance.
3. Prove that an untouched reference register is preserved in the channel statement.

**Acceptance:** A concrete existing BQP/QMA verifier has identical acceptance in the new semantics.

**Do not:** Do not silently change the gate set, layer order or output convention.

### Q17 — Purified strategies and verifier normal forms

Dependencies: Q08, Q09, Q16, Q28. Difficulty: **hard**.

Files: `qip/src/QIP/Purified.lean`, `qip/src/QIP/NormalForm.lean`.

**Contract:** Operational strategies admit pure/isometric private-memory implementations with identical behavior; circuit-described verifiers admit an efficient reversible form.

1. Separate arbitrary prover dilation from efficient verifier normalization.
2. For verifier measurements/dephasing, retain coherent outcome copies privately; prove equivalence against arbitrary adversaries.
3. Allocate needed verifier ancillas at the start and preserve their ownership; pad to a fixed total unitary workspace.

**Acceptance:** Every normalization direction used later is proved, with unchanged message count or a stated explicit change.

**Do not:** Do not let the prover receive purification registers or invoke the unfinished general reversible compiler.

### Q18 — Causal strategy operators

Dependencies: Q07, Q13. Difficulty: **medium**.

Files: `qip/src/QIP/StrategyOperator.lean`.

**Contract:** Define PSD strategy operators with recursive causal partial-trace equations, including the trivial-input first prover action.

1. Fix register order and define each prefix operator.
2. Use Q0=1 and Tr_output Qk = Q(k-1) ⊗ I_input, after proved reindexing.
3. Derive trace normalization and prefix uniqueness; a strategy operator is generally not trace one.

**Acceptance:** The one-turn case matches Choi channels, and initial state preparation appears as input dimension one.

**Do not:** Do not confuse the number of prover turns with the number of exchanged messages.

### Q19 — Strategy representation in both directions

Dependencies: Q18, Q08, Q09, Q15. Difficulty: **hard**.

Files: `qip/src/QIP/StrategyRealization.lean`.

**Contract:** An operator satisfies the causal constraints iff it is induced by an operational finite-memory strategy; prove a memory-dimension bound.

1. Forward direction: compose the actual strategy and trace private memory.
2. Reverse direction: induct on turns using positive factorizations and equal-marginal isometries.
3. Handle singular prefixes without inserting an inverse unless supported on the correct range.
4. Show the bounded-memory realization reproduces behavior against every compatible verifier.

**Acceptance:** This is the first major independently useful theorem; both implications and memory bounds receive fresh audits.

**Do not:** Do not assume causal realization or restrict the original prover to the constructed memory bound before proving equivalence.

### Q20 — Verifier testers and interaction pairing

Dependencies: Q19. Difficulty: **hard**.

Files: `qip/src/QIP/Tester.lean`.

**Contract:** Construct a PSD accepting tester from the actual verifier; prove operational acceptance equals its trace pairing with the prover strategy operator.

1. Derive the pairing from vectorization/contraction identities.
2. Resolve all transpose/conjugation conventions in the definitions.
3. Prove tester normalization over every legal strategy and compatibility with tensor products.

**Acceptance:** The formula covers every operational strategy, including those with retained entangled private memory.

**Do not:** Do not assume that a partial transpose preserves positivity or write a pairing formula without proving its convention.

### Q21 — Compactness and attained game value

Dependencies: Q20. Difficulty: **medium**.

Files: `qip/src/QIP/Value.lean`.

**Contract:** The operational supremum equals a maximum over the compact strategy-operator set; 0 ≤ value V ≤ 1.

1. Prove nonempty, closed and bounded causal feasible sets using their fixed trace.
2. Apply finite-dimensional compactness and continuity of the tester pairing.
3. Use Q19 to return an actual maximizing strategy and reconcile existential completeness with a value inequality.

**Acceptance:** All appearances of value=1 later yield a legal perfect prover; no finite-memory bound is assumed externally.

**Do not:** Do not replace an existential perfect prover by a bare sSup equation before this theorem.

### Q22 — Tailored strategy SDP and weak duality

Dependencies: Q18, Q20. Difficulty: **medium**.

Files: `qip/src/QIP/SDP/Primal.lean`, `qip/src/QIP/SDP/WeakDuality.lean`.

**Contract:** Express the strategy constraints as a finite real-linear map on Hermitian matrices; derive its dual and prove weak duality.

1. Write the adjoint of every partial-trace constraint explicitly.
2. Derive the dual from the selected convention, rather than copying incompatible tensor order.
3. Prove positivity of trace products and the telescoping primal/dual objective bound.

**Acceptance:** A concrete feasible dual certificate bounds every operational prover through Q19/Q20.

**Do not:** Do not run a numerical SDP solver or assume its answer certifies a bound.

### Q23 — Tailored strong duality / approximate certificates

Dependencies: Q22, Q21. Difficulty: **hard**.

Files: `qip/src/QIP/SDP/StrongDuality.lean`.

**Contract:** For every η>0, obtain a feasible dual bound ≤ value V + η. Exact dual attainment is optional unless actually required.

1. First locate a proved finite-dimensional separation/Slater theorem in pinned Mathlib; instantiate every hypothesis.
2. If absent, prove the needed finite-dimensional separation argument in a separate file.
3. Exhibit a strictly feasible causal operator using depolarizing channels and explicitly prove positive definiteness.
4. Ensure all complex Hermitian variables are treated as a real vector space.

**Acceptance:** No duality hypothesis survives in the final certificate theorem; strict-feasibility witnesses are actual matrices.

**Do not:** Do not assert Slater, strong duality or a solver theorem as an axiom. This is a hard review gate, not a routine automation task.

### Q24 — Product bound against entangled strategies

Dependencies: Q23. Difficulty: **hard**.

Files: `qip/src/QIP/SDP/Product.lean`.

**Contract:** Prove value(V⊗W) = value V * value W for all-pass parallel composition; initially the three-message case suffices.

1. Lower bound: product of actual optimal strategies.
2. Upper bound: tensor feasible dual certificates and prove each recursive inequality using PSD order.
3. If certificates are approximate, take η→0 with a proved limiting inequality.

**Acceptance:** The upper bound quantifies over arbitrary joint strategies, not product strategies.

**Do not:** Do not generalize this result to OR acceptance or arbitrary threshold repetition; do not assume independent cheating behavior.

### Q25 — Operational all-pass repetition

Dependencies: Q24, Q16, Q28. Difficulty: **medium**.

Files: `qip/src/QIP/ParallelRepeat.lean`.

**Contract:** Build k parallel copies with batched messages and all-pass acceptance; preserve three messages and prove value(repeat V k)=value(V)^k for k≥1.

1. Define the reordered product message registers and batched prover strategy space.
2. Compile the conjunction of accept bits using proved reversible gate templates.
3. Prove tensor semantics and induct Q24; record wire/gate/communication counts.

**Acceptance:** The result applies after perfect completeness and admits a polynomial-time printer in Q38.

**Do not:** Do not substitute the existing QMA copy-amplification theorem for this adversarial interactive theorem.

### Q26 — Reject flag and exact half-acceptance witness

Dependencies: Q17, Q21, Q28. Difficulty: **medium**.

Files: `qip/src/QIP/RejectFlag.lean`.

**Contract:** Add a prover-controlled reject option without increasing the number of messages; preserve soundness and permit honest acceptance exactly 1/2 whenever original acceptance is ≥2/3.

1. Place the flag in an existing prover-to-verifier message; keep the old computation independent of it.
2. For soundness, trace the flag to obtain an original strategy and use accept_new ≤ accept_old.
3. For completeness, prepare an independent flag with acceptance weight 1/(2p) for an honest success probability p≥2/3. The prover is unrestricted, so this need not be a finite-gate verifier rotation.

**Acceptance:** Arbitrary entanglement of a cheating flag is covered; the honest normalization and p>0 proof are explicit.

**Do not:** Do not require the verifier to know p or synthesize an arbitrary real rotation.

### Q27 — Bell-test perfect completeness

Dependencies: Q26, Q11, Q28. Difficulty: **hard**.

Files: `qip/src/QIP/PerfectCompleteness.lean`.

**Contract:** A concrete m+2-message transformation has completeness 1 and soundness ≤35/36 from thresholds 2/3 and 1/3.

1. Implement the Bell-test construction from the reference using the fixed threshold 1/2 and exact H/CNOT gates.
2. Use Q26 to produce the half-acceptance honest strategy and Q09/unitary extension for its final response.
3. For soundness, use the unchanged verifier-only marginal and the diagonal fidelity bound; weaken the bound to 1-(1/2-1/3)^2=35/36.
4. Return actual verifier syntax plus semantic and resource theorems.

**Acceptance:** Both claims concern this constructed verifier; no arbitrary exact verifier rotations or extra perfect-completeness premise remain.

**Do not:** Do not claim the result for variable thresholds without proving their encoding/computation and exact gate realization.

### Q28 — Exact gate adjoints and control macros

Dependencies: Q16. Difficulty: **medium**.

Files: `qip/src/QIP/Circuit/Adjoint.lean`, `qip/src/QIP/Circuit/Control.lean`, `qip/src/QIP/Circuit/Predicates.lean`.

**Contract:** Executable gate-list operations implement adjoints, swaps, controlled branch blocks and zero/all-pass tests in H/S/T/X/CNOT.

1. Use H⁻¹=H, X⁻¹=X, CNOT⁻¹=CNOT, S⁻¹=S³ and T⁻¹=T⁷. Reverse circuit order as well.
2. Extract a proved constant Toffoli/controlled-gate template with provenance, or prove its finite matrix identity directly.
3. Prove exact phase-sensitive action, ancilla cleanup, wire distinctness and per-gate expansion bounds.

**Acceptance:** Each macro has both semantic equality and a concrete finite encoding; protected control bits cannot be overwritten by returned messages.

**Do not:** Do not treat reversing a quantum circuit as requiring the unfinished classical-machine reversible simulation theorem; do not ignore relative phases under control.

### Q29 — Message padding and fixed-register normal form

Dependencies: Q17, Q28. Difficulty: **medium**.

Files: `qip/src/QIP/PadMessages.lean`, `qip/src/QIP/FixedRegisters.lean`.

**Contract:** Normalize to prover-first odd schedules and uniform message widths; pad to a suitable power-of-two-plus-one message count with identical value.

1. Use zero-length dummy messages with prescribed ownership transfers.
2. Initialize, retain and ignore padding in a way that never exposes verifier-private ancillas.
3. Prove both strategy translations, including dishonest use of all padding qubits.

**Acceptance:** Message counts 1,2,3,4,5 and empty input are handled; no soundness proof assumes the prover leaves padding zero.

**Do not:** Do not use mere register-dimension arithmetic as a proof of operational equivalence.

### Q30 — Cut-state characterization and stitching

Dependencies: Q29, Q11, Q21. Difficulty: **hard**.

Files: `qip/src/QIP/Cut.lean`, `qip/src/QIP/Stitch.lean`.

**Contract:** Relate reachable-prefix and accepting-suffix verifier marginals at a fixed cut to legal strategies; derive the fidelity bound needed for halving.

1. Define the two cut-state sets using actual operational prefixes/suffixes.
2. Prove purification-based strategy stitching with explicit private-memory enlargement.
3. Prove branch acceptance is bounded by squared fidelity with an appropriate cut state.
4. Handle empty feasible sets, zero branch probability, and the final accept projector explicitly; a max over an empty set is not a prover.

**Acceptance:** Every state used in the soundness argument is related to a legal strategy, and every claimed witness is constructed.

**Do not:** Do not replace this step by an abstract cut-consistency hypothesis or postselection available to the prover.

### Q31 — One halving transformation

Dependencies: Q30, Q12, Q28. Difficulty: **hard**.

Files: `qip/src/QIP/Halve.lean`.

**Contract:** For r≥1, transform 2^(r+1)+1 messages into 2^r+1; preserve perfect completeness and prove value(Halve V) ≤(1+sqrt(value V))/2.

1. Construct the midpoint-state request and forward/backward verifier from the reference, with a private retained challenge bit and a public copy.
2. For honesty, send the genuine midpoint and use purified prover actions or their inverses.
3. For soundness, apply Q30 branch bounds and Q12 to the same midpoint marginal chosen before the challenge.
4. Use only the upper inequality; an exact value identity is not required.

**Acceptance:** The five-to-three case is proved first, then the indexed general case; challenge timing is present in the operational execution.

**Do not:** Do not let the prover choose different midpoint states for the two challenge outcomes or apply the transform recursively below three messages.

### Q32 — Iterated semantic compression

Dependencies: Q31, Q29. Difficulty: **medium**.

Files: `qip/src/QIP/Compress.lean`.

**Contract:** After padding to M=2^(r+1)+1, r halvings give exactly three messages, completeness 1 and soundness ≤1-ε/M² from soundness ≤1-ε.

1. Induct on r using the one-step gap loss of at most a factor four.
2. Track the padded M rather than silently reusing the original unpadded message count.
3. Record an explicit size recurrence for transformed descriptions to be discharged in Q37/Q39.

**Acceptance:** r=0 returns a three-message verifier without another halving; every coercion from naturals to reals is explicit.

**Do not:** Do not claim polynomial size merely because the iteration count is logarithmic.

### Q33 — Scalar gap bounds and concrete repetition schedule

Dependencies: Q00. Difficulty: **small**.

Files: `qip/src/QIP/Arithmetic/Gap.lean`, `qip/src/QIP/Arithmetic/Padding.lean`, `qip/src/QIP/Arithmetic/Repetition.lean`.

**Contract:** Prove the scalar inequalities and an integer schedule K=72*M² for M≥3, δ=1/(36*M²): (1-δ)^K≤1/3.

1. Prove (1+sqrt(1-ε))/2≤1-ε/4 for 0≤ε≤1.
2. Prove 4^r≤(2^(r+1)+1)^2 and elementary power-of-two padding bounds.
3. Prove (1-δ)^k≤1/(1+k*δ) for 0≤δ≤1, by induction or a proved Bernoulli inequality.
4. Derive K*δ=2 and K polynomially bounded from a polynomial bound on M.

**Acceptance:** These lemmas are protocol-independent and compile now, before quantum foundations are complete.

**Do not:** Do not introduce numerical approximations, logarithm rounding assumptions or an unproved amplification hypothesis.

### Q34 — Concrete classical description-transformer primitives

Dependencies: Q14, Q00. Difficulty: **medium**.

Files: `qip/src/QIP/Uniform/Primitives.lean`, `qip/src/QIP/Uniform/ClockedLoop.lean`.

**Contract:** Actual TM2 polynomial-time certificates for parsing, list traversal, wire-index arithmetic, copying, concatenation and bounded iteration over encoded protocols.

1. Reuse small audited transducer/subroutine lemmas, recording their exact input/output encodings.
2. Return a fixed rejection/default output on malformed input so the generator is total on every Boolean string.
3. Build a general bounded-loop machine whose finite control does not depend on input length; prove exact output and actual runtime.

**Acceptance:** Every primitive is a concrete executable machine certificate; clocks include glue, cleanup and output writing.

**Do not:** Do not claim Lean recursion is polynomial time, use input-dependent finite label types, or enumerate 2^q amplitudes to print a q-qubit circuit.

### Q35 — Perfect-completeness printer

Dependencies: Q27, Q34. Difficulty: **medium**.

Files: `qip/src/QIP/Uniform/PerfectCompleteness.lean`.

**Contract:** A concrete polynomial-time transducer emits exactly the encoding of Q27, including reject-flag layout and the two new messages.

1. Compose only certified primitives and fixed gate templates.
2. Prove an exact byte-level output equation, polynomial clock and output-size bound.

**Acceptance:** Uniformity of the actual Q27 verifier follows from composition with the original generator.

**Do not:** Do not prove uniformity of a different verifier with merely the same asymptotic size.

### Q36 — Halving and padding printers

Dependencies: Q31, Q29, Q34. Difficulty: **medium**.

Files: `qip/src/QIP/Uniform/Halve.lean`, `qip/src/QIP/Uniform/Pad.lean`.

**Contract:** Certified transducers for message padding, midpoint layout, reverse/adjoint blocks and challenge routing.

1. Parse full register metadata; calculate offsets with the proved arithmetic primitives.
2. Print branch circuits with bounded control macros and retain a protected challenge record.
3. Prove exact encoding agreement and per-transformation size/time inequalities.

**Acceptance:** The printer handles all valid parity/base cases and returns a specified result for invalid encodings.

**Do not:** Do not assume the unfinished reversible-machine generator provides this description transformer.

### Q37 — Uniform iterated compression

Dependencies: Q36, Q32, Q33. Difficulty: **hard**.

Files: `qip/src/QIP/Uniform/Compress.lean`.

**Contract:** A total polynomial-time machine pads once and repeatedly halves until exactly three messages; its bytes equal Q32.

1. Implement bounded doubling to select the padded count, then a counted halving loop.
2. Prove the loop invariant relating the current bytes, message count and semantic transform.
3. Solve the actual description-size recurrence, including wire-address encodings and branch-control growth.
4. Prove a polynomial bound in the original encoded length, not in Hilbert-space dimension.

**Acceptance:** No uniformity or loop-runtime premise remains; constant-factor-per-stage growth is justified for the selected representation.

**Do not:** Do not reparse/synthesize exponential matrices or assume an arbitrary polynomial factor repeated log times is polynomial.

### Q38 — Uniform parallel repetition

Dependencies: Q25, Q34, Q33. Difficulty: **medium**.

Files: `qip/src/QIP/Uniform/Repeat.lean`.

**Contract:** A concrete polynomial-time printer emits K batched copies with AND acceptance and exactly three messages.

1. Compute K from the padded message count using a fixed polynomial arithmetic program.
2. Relabel disjoint copies, batch each round and append the proved all-pass circuit.
3. Prove exact encoded output and polynomial overhead in K and original description size.

**Acceptance:** The actual resulting verifier has the product semantics established in Q25.

**Do not:** Do not use sequential repetition, which would increase message count.

### Q39 — Compose family resources and uniformity

Dependencies: Q35, Q37, Q38. Difficulty: **medium**.

Files: `qip/src/QIP/FamilyConstruction.lean`.

**Contract:** Assemble one transformed family with a real TM2 generator and explicit natural-coefficient polynomial bounds on every resource.

1. Compose the exact printer equations in the same order as the semantic transforms.
2. Derive padded M and K bounds from the original family bounds.
3. Include input length zero/one, width, gate count, all message widths and total encoded output length.

**Acceptance:** The family can be inserted into QIPm 3 directly without supplying compiler/runtime/gap hypotheses.

**Do not:** Do not substitute a polynomial-space generator for a polynomial-time generator.

### Q40 — Public class equality

Dependencies: Q39, Q33, Q21. Difficulty: **small**.

Files: `qip/src/QIP/ThreeMessage.lean`.

**Contract:** Prove ShiQIP.qip_eq_qip3 : ShiQIP.QIP = ShiQIP.QIPm 3, for the independently fixed classes.

1. Forward: instantiate the perfect-complete, padded/compressed, all-pass-repeated family.
2. Use δ=1/(36*M²), K=72*M² and Q33 to finish soundness; perfect completeness implies the required 2/3.
3. Reverse: use the constant polynomial message bound for a three-message family.
4. Derive the language-level statement by the promise embedding, rather than redefining existing BQP/PP/PSPACE.

**Acceptance:** An independent example has exactly the equality type; no helper assumptions or uninstantiated typeclass law fields remain.

**Do not:** Do not cite QIP=PSPACE, IP=PSPACE, BQP⊆PSPACE or the desired equality to prove this theorem.

### Q41 — Final clean build and semantic audit

Dependencies: Q40. Difficulty: **medium**.

Files: `qip/src/QIP/Audit/Final.lean`, `qip/verification/clean-build.json`, `qip/verification/axioms.json`, `qip/README.md`.

**Contract:** A source-matched clean Sherlock build and exact-type/transitive-axiom audit certify the complete theorem graph.

1. Build all project dependencies without reused project objects against pinned Mathlib libraries.
2. Audit the endpoint, operational/strategy equivalence, Uhlmann, duality, product bound, compression and all printer certificates.
3. Review definitions and quantifiers independently of axioms: adversarial memory, uniformity, dimensions, message count and class thresholds.
4. Save sources, hashes, logs, objects and allocation metadata before releasing node scratch.

**Acceptance:** All reports present; allowed axioms only propext/Classical.choice/Quot.sound; zero sorryAx; zero reused project objects in the final build.

**Do not:** Do not describe an incremental/local check as a clean Sherlock build or equate axiom cleanliness with correctness of the class definitions.

### O01 — One-message compatibility with the existing QMA semantics

Dependencies: Q16, Q21. Difficulty: **medium**.

Files: `qip/src/QIP/Compatibility/QMA.lean`.

**Contract:** At a fixed input, identify one-message verification with optimization over a witness state; connect the corrected QMAU semantics where encodings permit.

1. Read Def_ShiClassQMAU and distinguish it from the older folded-uniformity class.
2. Prove pure-vs-mixed witness equivalence by linearity/spectral decomposition.
3. Prove only the class inclusions for which a real uniform generator translation is available.

**Acceptance:** Exact names/types state whether the result is semantic, a class inclusion, or a full class equality.

**Do not:** Do not claim ShiClassQMA.QMA equals the new QIPm 1 merely because textbook QMA=QIP(1).

### O02 — Input-uniformity model bridge using future reversible simulation

Dependencies: O01, RV01. Difficulty: **hard**.

Files: `qip/src/QIP/Compatibility/UniformModels.lean`.

**Contract:** Optional bridge between input-dependent verifier generators and unary-length uniform circuits that process x internally.

1. Wait for an audited, exported unconditional reversible simulation theorem.
2. Prove a uniform universal evaluator for the bounded encoded verifier circuits, including controlled gate templates.
3. Compose coherent description generation, evaluation and cleanup, with separate proof of all size/uniformity bounds.

**Acceptance:** This is an additional compatibility theorem; the primary equality Q40 must not wait on it.

**Do not:** Do not assume reversible simulation alone also supplies a universal circuit or this model equivalence.

## 7. Mandatory verification and execution discipline

### 7.1 Before every implementation session

1. Read the repository instructions, this plan, the task manifest and current progress ledger. Inspect `git status`; do not overwrite another task's edits.
2. Read the exact prerequisites for the selected task. Check accepted theorem names/types rather than relying on a previous narrative summary.
3. Pick one bounded contract. Write its statement and mathematical proof outline before trying a large tactic script.
4. Use a small fresh-import audit file for the declarations being added. Proposed signatures in this plan are not already checked Lean code.
5. After acceptance, record actual source hashes, theorem names, audit results and the next unblocked tasks.

### 7.2 Only compile on Sherlock

The user reported that local Lean checking overloaded their computer. **Do not run local Lean or Lake compilation**, even for a quick test, without a later explicit user instruction changing that restriction. Lightweight text, JSON and source-hash checks are permitted locally. Other projects' historical local verification does not authorize it here.

Read Sherlock's current `/etc/agents/AGENTS.md` and relevant topic files before remote work. Compile only in an allocated compute job. Size independent one-thread Lean workers to both allocated cores and measured memory; 32 or more workers are allowed when the allocation and dependency graph support them, but they are not mandatory. Prior runs used three workers in 16 GB; do not extrapolate that budget blindly to new matrix-heavy modules.

Build ready DAG nodes concurrently, respecting imports. Do not let two workers write the same object. Bundle small checks into appropriately sized jobs, preserve node-local results before exit, follow the cluster's polling interval, and never submit duplicate jobs just because one is queued. If authentication is unavailable, preserve unverified source and report the blocker; do not fall back to local compilation automatically.

### 7.3 Acceptance for a task

Record separately:

- source statement and the mathematical claim actually proved;
- compiler success under the pinned environment;
- fresh-import exact-type check;
- transitive axioms, allowing only `propext`, `Classical.choice`, `Quot.sound`;
- source/object hashes and whether any artifacts were reused;
- resource/encoding proof status for computational constructions;
- unresolved dependencies, with no claim of completion.

Selected axiom reports must all be present exactly as expected; reject forbidden and duplicate reports. Axiom cleanliness does not prove the class definition is faithful, nor does it discharge hypotheses in a conditional theorem. Review the final theorem with full printed type, including implicit arguments and instance parameters.

### 7.4 Required edge cases and adversarial checks

Use mathematical examples/counterexample-oriented checks where they validate a real contract, not implementation-mirroring tests:

- zero-qubit register versus zero-dimensional space;
- rank-deficient density matrices and non-square channel spaces;
- inconsistent register order, output-wire ownership or message parity;
- a prover that entangles message padding with private memory;
- an adversary acting jointly across repetition copies;
- input lengths zero and one;
- original protocols with one, two, three and five messages;
- false/malformed encodings, out-of-range wires and truncated fields;
- zero conditional branch probability in a normalized-state argument;
- empty cut-state sets and final effects without an eigenvalue-one subspace;
- an attempted replacement of a protected challenge with a returned qubit;
- `sSup=1` without attained maximum;
- a printer whose finite label type accidentally depends on the input;
- an exponentially large semantic matrix used as executable circuit-generation data.

The halving proof must use a purified projective final test and prove any needed nonemptiness/normal-form property. A statement about arbitrary effects cannot assume a perfectly accepting suffix exists.

## 8. Progress reporting, hard-task escalation and handoff prompt

Suggested task statuses:

```text
not_started → statement_checked → proof_in_progress → focused_verified
            → integrated_verified → clean_verified
```

Only `integrated_verified` or stronger discharges a dependency. For unverified drafts use `proof_in_progress`; a file count is not progress toward the theorem. Record `blocked_on` explicitly without changing the theorem to remove the obstacle. Tasks O01/O02 are optional and must not obscure completion of Q00–Q41.

A progress entry should contain:

```text
Task ID:
Contract and exact declarations:
Source files and hashes:
Prerequisites actually used:
What changed:
Sherlock job / toolchain / worker count:
Compiler result:
Exact-type and axiom-audit result:
Resource / encoding / uniformity status:
Smallest remaining gap:
Next ready task:
```

Use the following prompt when handing the project to another model:

> Work in `lean-quantum-complexity`. Read `plans/QIP_THREE_MESSAGE_PLAN.md` and `plans/QIP_THREE_MESSAGE_TASKS.json` before editing. The target is a premise-free proof of `ShiQIP.QIP = ShiQIP.QIPm 3` for explicitly defined finite-gate, polynomial-time-uniform quantum interactive verifiers. Start with the earliest task whose accepted prerequisites exist; initially execute Q00 and then the first execution packet. Preserve existing BQP, PP, PSPACE and QMA definitions and proofs. Do not assume Uhlmann, causal realization, duality, parallel repetition, uniformity or the ongoing reversible simulation theorem. Do not start local Lean/Lake compilation: use Sherlock compute allocations only. Keep tasks small, verify exact types and allowed axioms, and update a task ledger with evidence. If a hard proof stalls, isolate the precise missing lemma and work on another ready task; never replace the obligation by an axiom, a `sorry`, a new class field, or a weakened endpoint. Proposed names in the plan are not pre-existing APIs. Do not publish or push new implementation changes unless the user authorizes that action.

For a hard review, supply one page of concrete material: exact statement, relevant definitions, a minimal failing proof, mathematical derivation, and the first unresolved inference. Do not send an entire directory and ask another model to guess the problem.

Completion means the operational class equality, its concrete generator and all required semantic/resource theorems pass the source-matched clean audit. It does not require the optional uniform-model bridge, QIP = PSPACE, publication of unrelated drafts, or completion of the separate reversible-simulation project.

## 9. Mathematical references and provenance

These are proof references, not imported assumptions. The task contracts and file organization above are an implementation proposal; every cited mathematical ingredient used in Lean must be proved from the pinned Mathlib and accepted project lemmas.

- Kitaev and Watrous, [Parallelization, amplification, and exponential time simulation of quantum interactive proof systems](https://cs.uwaterloo.ca/~watrous/Papers/QuantumInteractiveProofs.pdf), STOC 2000: original three-message parallelization, perfect-completeness and repetition results.
- Vidick and Watrous, [Quantum Proofs](https://arxiv.org/abs/1610.01664), Chapter 4, especially Sections 4.1.4, 4.2.1–4.2.2 and 4.3: readable presentation of purification, the half-threshold construction, iterative compression and strategy optimization. Use the PDF's displayed mathematics to resolve OCR errors; do not mechanically copy an apparent reversed completeness/soundness inequality.
- Kempe, Kobayashi, Matsumoto and Vidick, [Using Entanglement in Quantum Multi-Prover Interactive Proofs](https://arxiv.org/abs/0711.3715): source of the iterative compression approach; this project needs the single-prover specialization, not its entire multi-prover theory.
- Gutoski and Watrous, [Toward a General Theory of Quantum Games](https://arxiv.org/abs/quant-ph/0611234), especially representation and maximum-output-probability results: operational meaning and optimization of finite-round strategies.
- Jain, Ji, Upadhyay and Watrous, [QIP = PSPACE](https://arxiv.org/abs/0907.4737): later application/direction only. It is not a shortcut or an assumption in this plan.

The BQP–PSPACE GitHub evidence is pinned to the commit in Section 1.1. The reversible progress is a separately inspected local status report, not a GitHub claim and not an available unconditional theorem. Re-read both when implementation begins.
