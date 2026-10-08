# Efficient reversible simulation

Every polynomial-time classical Boolean-string computation, represented by Mathlib's `TM2ComputableInPolyTime`, admits an exact, clean, polynomial-time-uniform family of polynomial-size quantum circuits.

The endpoint is [`ShiReversibleGenerator.efficient_reversible_simulation`](src/ReversibleEfficientSimulationTheorem.lean). Its only hypothesis is the actual polynomial-time computation certificate. It constructs a family in the established H/S/T/X/CNOT semantics and proves:

- Polynomial-time uniformity in the existing `ShiBQP.Uniform` definition, witnessed by a concrete finite TM2 serializer.
- Well-formedness and polynomial bounds on elementary gates, depth, and ancillary wires.
- Exact full-string output, with the original input preserved and every quantum workspace wire returned to zero.
- Correct decoding of a separate, fixed-width output register.

The clean action has the form `|x,0,0⟩ ↦ |x,0,enc(f(x))⟩`, with no input-dependent phase. The source model is Mathlib's finite multistack TM2; this publication does not assert a separately proved equivalence with other Turing-machine models.

## Proof route

The construction encodes bounded machine configurations, compiles initialization and padded time steps into Boolean assignments, and implements those assignments reversibly. Compute–copy–uncompute yields the clean output. A concrete generator prints the exact resulting quantum circuit and its header, with a proved polynomial clock and cleaned generator counters. A shifted-power clock majorant handles every original polynomial-time certificate.

Useful entry points:

- [Final theorem](src/ReversibleEfficientSimulationTheorem.lean)
- [Uniformity](src/ReversibleMachineUniformFamily.lean)
- [Actual polynomial-time serializer](src/ReversibleMachineSerializationPolytime.lean)
- [Clean quantum action](src/ReversibleMachineUniformFamilyClean.lean)
- [Explicit gate bound](src/ReversibleEfficientSimulationSize.lean)
- [Declaration audit](src/ReversibleAudit.lean)

## Verified publication

Sherlock job **46916049**, snapshot **r99**, completed a fresh source-only build in **1:43:27**, using four compiler workers with one Lean thread each. All **885 modules** passed, along with **2724 ordered unique declaration audits** and **1770 source/object hash comparisons**. The permitted transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

All published Lean sources are byte-for-byte copies of that accepted build. The self-contained source graph imports only pinned Mathlib modules externally. [manifest.json](manifest.json) records source hashes and dependencies; [verification/report.json](verification/report.json), [verification/clean-build.json](verification/clean-build.json), and [verification/axioms.json](verification/axioms.json) preserve the verification evidence. Compiled objects and Mathlib caches are not included. The build driver is the one used for r99; the portable shell wrapper and publication checker were added for this folder.

## Reproduce

Check the published sources and audit evidence locally, without invoking Lean:

```bash
cd reversible-simulation
python3 scripts/verify.py
```

Run Lean compilation on Sherlock inside a Slurm compute allocation. The accepted build used four CPUs, 16 GiB RAM, and a 2h15m time limit. Stage the checkout and caches into node-local scratch, and preserve results before releasing the allocation. Discover available partitions and follow the cluster's current policies.

With the pinned Lean 4.33.1 toolchain available, run from this folder on the compute node:

```bash
lake update
lake exe cache get
REV_WORKERS=4 ./scripts/build.sh
```

Mathlib is pinned to `0df444a360eaa60ab8c11dca51a86af692955474`. The driver recompiles every project module in dependency order; it does not reuse project build records. The checker then validates the new object hashes and ordered axiom audit. Outputs are `src/*.olean`, `logs/`, and `result.json`.

The published evidence describes the accepted r99 run; the lightweight publication check verifies source identity and recorded evidence without pretending to recompile Lean or recheck absent object files.
