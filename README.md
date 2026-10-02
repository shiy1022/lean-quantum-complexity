# QMA amplification in Lean 4

This repository contains the source closure for a checked **copy-based** QMA strong error-reduction theorem, plus the open witness-preserving Marriott–Watrous mission statement. The copy-based construction uses polynomially many copies of the witness. It does **not** prove amplification with the original witness length.

The principal local endpoint is `ShiQMAGeneralGap.QMAWith_general_threshold_amplification` in [`proofs/AMPUNI-arithmetic-front.lean`](proofs/AMPUNI-arithmetic-front.lean). Its source includes an axiom audit that permits only Lean's usual `propext`, `Classical.choice`, and `Quot.sound`. The endpoint was compiled and audited in the source workspace before this repository was assembled. The full endpoint has **not yet been transplanted to Prove2Me**.

The separate, unsolved goal is in [`mission-draft/Theorems/Thm_ShiQMAWitnessPreserving_general_threshold_amplification.lean`](mission-draft/Theorems/Thm_ShiQMAWitnessPreserving_general_threshold_amplification.lean). It explicitly requires `∀ n, G.wit n = F.wit n`. The other two mission files provide its interface and a constant-gap milestone. These statements type-check, but both theorem bodies are `sorry`: they are targets, not proved results. The proposal's parameter functions are literal `Polynomial ℕ` values, a narrower class than the paper's full unary-time constructible `poly` functions.

## Source layout

- `proofs/`: the 426 local Lean modules in the import closure of the copy-based endpoint. Generated `.olean` files and experimental drafts are excluded.
- `Definitions/` and `Theorems/`: the 104 Prove2Me reference source modules imported by that closure. The theorem files are **statement stubs** and may contain `sorry`; their 89 matching platform theorems have separately accepted proofs. The local closed endpoint reconstructs the proof dependencies and checks its final axioms.
- `platform-submissions/`: exact definition, theorem-statement, and solution sources for 42 supporting results accepted by Prove2Me.
- `mission-draft/`: the three-item witness-preserving proposal and its description.
- `provenance/`: Prove2Me theorem IDs and verification records, without credentials. See [PUBLICATION.md](PUBLICATION.md).

## Build

The project pins Lean 4.33.1 and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. With `lake` and the Lean toolchain available, run:

```bash
./scripts/build.sh
```

The script builds the reference modules, then compiles the local proof modules in import order and runs the endpoint's axiom audit. It can take substantial time on a fresh Mathlib checkout. The source-copy and import-closure checks used to assemble this repository passed; a fresh full build in this new checkout has not yet been run.

## Mathematical reference

C. Marriott and J. Watrous, [*Quantum Arthur–Merlin Games*](https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf), Section 3. The copy-based result corresponds to the error-reduction approach discussed around Theorem 3. The witness-preserving open goal is a formalization target for Theorem 4 in this circuit model.

Source files retain their authorship headers. Code is distributed under [Apache 2.0](LICENSE).
