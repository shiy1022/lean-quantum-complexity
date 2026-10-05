# BQP ⊆ PP

The public theorem is proved for the original circuit-family BQP and counting-class PP definitions:

```lean
theorem ShiBQP.bqp_subset_pp : ShiBQP.BQP ⊆ ShiClassPP.PP
```

[Proof](src/BQP-final-inclusion.lean) · [Exact-type and axiom audit](src/BQP-router-assembly-fresh-audit.lean) · [Verification record](verification/clean-build.json)

The proof constructs the uniform-family compiler, binary threshold arithmetic, witness splitting and retention, comparisons, Boolean dispatch, and the polynomial-time checker for the exact counting relation. The counting reduction and short-input patch establish the original inclusion without additional helper hypotheses. BQP, PP, and their encodings are unchanged.

## Verified result

On 2026-10-05, Sherlock job `46586447` rebuilt **all 306 project modules from source**, with **zero reused project outputs**, against pinned precompiled Mathlib libraries. Three Lean workers completed compilation in 2,179.61 seconds (36.3 minutes). All **275 selected declaration axiom reports** passed. The final endpoint uses only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

The Lean files published here are byte-for-byte copies of that verified source graph. `source-manifest.json` records their hashes and imports. Only manifest source locations have been made relative for portability. `verification/clean-build.json` records source/object hashes and compile results; `verification/axioms.json` records the selected axiom reports. Compiled objects, caches, and machine-specific workspace paths are excluded.

Some reference theorem files are statement stubs. The final proof reconstructs the needed dependencies, and the transitive axiom audit confirms that the endpoint does not depend on their `sorryAx`. Compilation alone would not establish this.

## Source layout

`src/` preserves the verified Lean import names. The `BQP-*` modules implement the proof; `AMPUNI-*` modules provide reusable machinery developed during QMA amplification; `Definitions/` and `Theorems/` hold reference dependencies. Numbered reference/candidate filenames are retained to keep this publication identical to the verified graph.

## Reproduce

Source checks are lightweight and do not compile Lean:

```bash
cd bqp-pp
python3 scripts/verify.py
```

Run compilation **inside a Sherlock Slurm allocation**, using node-local scratch for the checkout and build outputs. The clean run fit three workers in a 4-core, 16-GB allocation with a two-hour limit. Larger allocations may use more workers if memory permits.

With Lean 4.33.1 installed, prepare the pinned Mathlib environment on the compute node:

```bash
lake update
lake exe cache get
BQP_WORKERS=3 ./scripts/build.sh
```

Alternatively, set `BQP_LEAN` to the Lean 4.33.1 executable, `BQP_MATHLIB` to the pinned Mathlib checkout, and `LEAN_PATH` to its cached libraries and package libraries; the build script then skips Lake environment discovery. Use `ml system git/2.45.1` if the compute node's default Git cannot read the checkout. The build checks the Lean version, Mathlib revision, and source hashes, compiles in dependency order with one Lean thread per worker, and verifies all object hashes and selected axiom reports. The exact-type check is part of the compiled final audit.

For a clean rebuild, use a fresh checkout without project `.olean` files or `previous-build-result.json` / `previous-source-manifest.json`. Confirm `reused_project_modules` is zero in the generated `current-verification.json`. Save build outputs from node-local scratch before releasing the allocation.

This publication does not claim a new clean build of Mathlib itself or a new full build of the QMA project.
