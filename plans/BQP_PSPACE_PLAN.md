# BQP ⊆ PSPACE: implementation and verification plan

Date: 2026-10-05. **Status: plan only; PP ⊆ PSPACE and BQP ⊆ PSPACE are not proved here.**

> Execution note (2026-10-05): tasks S00–S16 have been carried out in [`bqp-pspace/`](../bqp-pspace/). See its [progress ledger](../bqp-pspace/verification/progress.md). Compilation was local on a Windows workstation at the user's instruction, not on Sherlock. The plan text below is kept as written.

This plan targets a complete, reusable classical polynomial-space simulation of PP, followed by composition with the already proved BQP ⊆ PP theorem. It is designed for execution in small, bounded tasks by a model that benefits from explicit contracts. Do not interpret suggested signatures as already compiled Lean.

## 1. Fixed objective and baseline

Required public endpoints, with the new corrected space class described below:

```lean
-- Proposed names and exact mathematical target; create these only with real proofs.
theorem ShiSpace.pp_subset_pspace : ShiClassPP.PP ⊆ ShiSpace.PSPACE
theorem ShiBQP.bqp_subset_pspace : ShiBQP.BQP ⊆ ShiSpace.PSPACE
```

The second proof should ultimately be a short composition:

```lean
intro L hL
exact ShiSpace.pp_subset_pspace (ShiBQP.bqp_subset_pp hL)
```

The mathematical workload is the first theorem and the validity of the space model. The final theorems must have no extra simulation, checker-space, termination, enumeration, or model-equivalence hypotheses.

Baseline inspected at repository commit `da6aba9167e9802b57b651cff845462612f163cc`:

- `bqp-pp/src/BQP-final-inclusion.lean` proves `ShiBQP.bqp_subset_pp` for the original `ShiBQP.BQP` and `ShiClassPP.PP` definitions.
- `bqp-pp/verification/clean-build.json` records the 2026-10-05 Sherlock rebuild: 306 project modules, no reused project objects, and 275 selected axiom reports. This uses pinned precompiled Mathlib; it is not a fresh Mathlib build.
- `python3 bqp-pp/scripts/verify.py` passed during plan preparation, checking the 306 source hashes and dependency closure. No new Lean compilation was performed for this plan.
- Lean is **4.33.1**; Mathlib is **`0df444a360eaa60ab8c11dca51a86af692955474`**.
- Existing BQP endpoint axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.

Preserve the BQP and PP definitions and this verified source graph. Read current repository state before working; other developments may have advanced since this baseline.

## 2. The mathematical proof in plain language

A PP language has a deterministic polynomial-time checker `R(x,w)`. For an input `x` of length `n`, it considers every Boolean string `w` of length `m = n^k`. The language accepts exactly when strictly more than half of those strings make the checker return true.

A polynomial-space decider can:

1. Retain `x`.
2. Keep a single `m`-bit witness, initially all zero.
3. Run the checker on that witness, reusing the same scratch space each time.
4. Increment a binary accepting-count register when the checker returns true.
5. Advance to the next witness; stop after the all-ones witness has been processed.
6. Test `2 * acceptingCount > 2^m` and output that Boolean.

There are exponentially many iterations, which is allowed. The witness uses `m` bits and the accepting count uses `m+1` bits, even when its value reaches `2^m`. A single checker call takes polynomial time in `n+m`, and therefore uses polynomial space. Scratch space is reset between calls. Total peak space is polynomial in `n`, although total time need not be.

The formal proof must construct this machine. A recursive Lean function, a finite-set expression, or an assertion that the enumeration is executable does not establish machine computability or its space use.

## 3. Critical definition repair: do not use the historical PSPACE unchanged

A historical local bundle, `/Users/yuehengshi/prove2me_workspace/Definitions/Def_ShiClassPSPACE.lean`, was inspected outside this repository. That local path is provenance, not a build dependency: a remote executor need not have the file. Its essential definition was:

```lean
-- HISTORICAL, UNSUITABLE TARGET: shown as evidence, not proposed code.
{L | ∃ (χ : List Bool → Bool) (k : Nat)
    (c : Turing.TM2ComputableInPolyTime
      (id : List Bool → List Bool) Computability.encodeBool χ),
  (∀ x, SpaceBoundedOn c.tm (x.map c.inputAlphabet.invFun) (x.length ^ k)) ∧
  ∀ x, x ∈ L ↔ χ x = true}
```

Two defects matter:

- It requires `TM2ComputableInPolyTime`, despite prose saying no time bound is imposed. Membership thus entails a polynomial-time decider. Proving general PP containment into this class would require an unjustified PP-to-P conclusion.
- The bare bound `n^k` cannot uniformly absorb constants or offsets at short inputs. At length one it is always one; at length zero it is zero for positive `k`. Initialization, output and scratch costs need room.

This file is not part of the published `bqp-pp/src` source graph. Do not copy its class definition unchanged, overwrite a published definition, or silently prove an inclusion into a renamed version of the old class. Introduce a documented new namespace `ShiSpace` and use a natural-coefficient polynomial bound. Do not claim equivalence with the flawed historical class.

### 3.1 Required corrected space interface

Use Mathlib's actual `Turing.FinTM2`. A configuration's space is the sum of the lengths of all its stacks, including input and output. Reuse `ShiTMStackGrowth.size` where compatible.

Define reachability using an explicit iteration of Mathlib's `step`, preferably the existing `ShiTMSubroutine.run` on `Option Cfg`. Initial and final configurations are Mathlib's `initList` and `haltList`. State the space property over **every reachable configuration**, including initialization and the halted configuration before a subsequent step yields `none`.

A proposed interface, to elaborate and freeze in task S01, is:

```lean
-- Schematic: resolve imports, instances, and exact helper names in S01.
def SpaceBoundedOn (tm : Turing.FinTM2)
    (xs : List (tm.Γ tm.k₀)) (s : Nat) : Prop :=
  ∀ t c, (ShiTMSubroutine.run tm.m)^[t]
      (some (Turing.initList tm xs)) = some c →
    cfgSpace tm c ≤ s

def PolySpaceDecider (χ : List Bool → Bool) : Prop :=
  ∃ c : Turing.TM2Computable
      (id : List Bool → List Bool) Computability.encodeBool χ,
    ∃ p : Polynomial Nat, ∀ x,
      SpaceBoundedOn c.tm (x.map c.inputAlphabet.invFun) (p.eval x.length)

def PSPACE : Set (Language Bool) :=
  {L | ∃ χ : List Bool → Bool,
    PolySpaceDecider χ ∧ ∀ x, x ∈ L ↔ χ x = true}
```

`TM2Computable`, not its polynomial-time variant, supplies a real machine and a successful halting/output proof on every input. Space bounds alone do not guarantee halting. The machine in the correctness certificate and in the space proof must be the same machine.

### 3.2 Model adequacy obligations

- Counting input storage is appropriate for this polynomial-space endpoint: an additional linear input copy fits a polynomial bound. This convention must not be reused to claim logarithmic-space results.
- `FinTM2` makes stack indices, labels and internal control finite, but only its input alphabet is explicitly finite. Do not assume every `tm.Γ j` has a `Fintype` instance.
- Prove a reachable-alphabet lemma: for each fixed machine and stack, every symbol reachable from allowed initial inputs lies in a fixed finite set. Use the finite input alphabet and the images of the finitely many syntactic push expressions over the finite control-state type. Peek/pop only update finite control; they do not create arbitrary new stack symbols.
- This establishes that stack height measures bounded information per symbol for the machines at issue. Also explain that a statement is a fixed finite tree, so its internal transient stack peak differs from statement-boundary space by a machine-dependent constant. Prove the peak bound if needed by the chosen model bridge.
- Describe the endpoint explicitly as the corrected finite-multistack PSPACE model. A formal equivalence to a separately defined single-tape/read-only-input class is not silently supplied by this work. If such an equivalence is later advertised, it requires a separate proved simulation. Do not make that larger equivalence project a prerequisite for the present named-model theorem.
- A machine may depend on fixed `R`'s computation certificate and fixed `k`; its finite control must not depend on the input length or contain an unbounded natural counter.

## 4. Exact PP input contract and edge cases

Read `bqp-pp/src/Definitions/Def_ShiClassPP.lean` and `Def_PvsNP.lean` first. The theorem must preserve:

```lean
∃ (R : PvsNP.Str × PvsNP.Str → Bool) (k : Nat),
  PvsNP.PolyTimeChecker R ∧
  ∀ x, x ∈ L ↔
    2 * ShiClassPP.countAccept R x (x.length ^ k) > 2 ^ (x.length ^ k)
```

`countAccept` ranges over functions `Fin m → Bool`, passed to the checker as `List.ofFn`. Checker inputs use `PvsNP.encodePair`: input bits tagged `Sum.inl`, followed by witness bits tagged `Sum.inr`. Its length is exactly `n+m`; it is a four-symbol alphabet. This is not a binary alphabet equivalence. Preserve the tags via the certificate's supplied alphabet equivalence.

Mandatory boundary cases:

- `n=0,k=0`: Lean's `0^0=1`, so enumerate two one-bit witnesses.
- `n=0,k>0`: `m=0`, so enumerate the **one empty witness** exactly once.
- `n=1`: `m=1` for every `k`.
- All witnesses reject; all accept; exactly half accept; one more or one fewer than half.
- Accepting count can equal `2^m`; an `m`-bit accumulator is too small.
- Strict majority rejects ties. Do not replace `>` with `≥`.
- The checker can halt immediately; its input and output stack indices may coincide.
- Bit order must agree between enumeration, numeric interpretation, `List.ofFn`, and physical stack order.
- Halting state `some ⟨none,...⟩` and the later `none` returned by stepping it are distinct.

## 5. What can be reused

Inspect the named files and declarations, including their full types and transitive axioms. Documentation alone is not an interface guarantee.

| Existing source | Verified role to inspect | New work still needed |
|---|---|---|
| `BQP-final-inclusion.lean` | Final BQP-to-PP theorem | Composition only at the end |
| `Definitions/Def_ShiClassPP.lean` | Exact PP and `countAccept` definitions | Enumeration-to-count identity |
| `Definitions/Def_PvsNP.lean` | Checker certificate, tagged pair input | Preserve these conventions |
| `AMPUNI-subroutine-lift.lean` | `run`, `stmt`, `cfg`, `stepAux_lift`, `run_to_terminal` | Protected-stack and restart contracts |
| `AMPUNI-subroutine-full-lift.lean` | `run_lift`, `run_iter_lift` | Peak-space transfer and halt redirection |
| `AMPUNI-run-stack-growth.lean` | `size`, `potential_run_le`, `run_size_le` | Time-certificate-to-all-prefix space bridge |
| `AMPUNI-finite-stack-growth.lean` | `pushBudget`, `stepAux_size_le`, `finite_growth` | Reachable alphabets and statement transient peaks |
| `AMPUNI-total-function.lean` | `halted_unique`, `outputs_unique`, `function_of_total` | Apply to the actual total enumerator if useful |
| `BQP-binary-add.lean` | Little-endian arithmetic, actual add machine | Fixed-width increment and peak-space bounds |
| `BQP-binary-compare.lean` | Borrow-based comparison and actual machine | Connect orientations/widths and bound scratch peaks |
| `Definitions/Def_ShiTM2_Composite.lean` | Concrete finite machine composition | Repeated calls with preserved master input and counters |

Existing runtime lemmas can bound space for a **single polynomial-time call**. They cannot bound the entire enumerator's space by its total runtime, since that runtime is exponential.

The reversible-simulation project may independently build finite reachable alphabets or configuration encodings. Coordinate through explicit stable theorem interfaces when available. Do not assume unpublished/in-progress results, edit its files, or expand this task into reversible compilation.

## 6. Repository layout and dependency handling

Create a separate `bqp-pspace/` project. Reuse `bqp-pp/src` as a dependency without changing its source manifest or source files. Proposed layout:

```text
bqp-pspace/
  README.md
  lean-toolchain
  lakefile.toml
  src/
    Space/Model.lean
    Space/Run.lean
    Space/ReachableAlphabet.lean
    Space/TimeToSpace.lean
    Space/Frame.lean
    Space/PeakComposition.lean
    Count/FixedBits.lean
    Count/Enumeration.lean
    Count/Prefix.lean
    Machine/Increment.lean
    Machine/CopyRestore.lean
    Machine/WitnessLength.lean
    Machine/CheckerCall.lean
    Machine/MajorityTest.lean
    Machine/Enumerator.lean
    Machine/EnumeratorCorrect.lean
    Machine/EnumeratorSpace.lean
    PPToPSPACE.lean
    BQPToPSPACE.lean
    Audit/Space.lean
    Audit/Counting.lean
    Audit/Machines.lean
    Audit/Final.lean
  scripts/
  verification/
  source-manifest.json
```

Names are proposed; freeze them once tasks start. Namespace roots should be distinctive, such as `ShiSpace` and `ShiPPPSPACE`; avoid new declarations colliding with existing reference imports.

Build the new modules with both new and baseline library roots on `LEAN_PATH`, plus pinned Mathlib. The baseline has a custom dependency builder, not a conventional single `lean_lib`; do not assume `lake build` discovers its published `src` graph automatically. Extend orchestration in the **new project** to consume and validate the baseline graph. The existing BQP verifier asserts an exact 306-file manifest and should continue to pass unchanged.

The new combined build manifest must include all baseline modules actually imported and all new modules, explicit dependency edges, pinned versions, source hashes and audit targets. Preserve baseline verification as historical evidence; do not relabel it as proof of the new theorem. Keep QMA's separate source root out of the new search path because reference module names overlap.

## 7. Detailed tasks and acceptance gates

Complete a task only after its real declarations compile and a fresh-import axiom audit passes. Pure specification drafts can be recorded separately as unverified; they do not count as completed proof tasks.

### S00 — Inventory and scope lock

Read the files in sections 1, 3–5 and current repository instructions. Search only for relevant existing declarations. Record each reusable theorem's exact type, source and status in `bqp-pspace/verification/reuse-map.md`. Check whether a corrected space interface has appeared since this plan. If compatible, reuse it after reviewing semantics; otherwise implement section 3 under the proposed new namespace.

Set up the separate pinned project and the smallest source-matched build/audit runner needed to compile S01 on Sherlock. Reuse the baseline runner's approach; do not defer all build setup until S16. Create `bqp-pspace/verification/progress.md` with one row per S00–S16: status, implementation paths, accepted source hash, verification evidence, and next unresolved obligation. Use `not started`, `in progress`, `verified`, or `blocked`; a successful tactic sketch is not `verified`.

Exit: a dependency map, a usable incremental verification route, the explicit corrected target and the first unresolved task. Do not compile the whole repository merely for inventory.

### S01 — Space model

Implement `cfgSpace`, `SpaceBoundedOn`, `PolySpaceDecider`, `PSPACE`. Use `TM2Computable` for total output correctness and `Polynomial Nat` for space. Prove initialization space equals input length, the Boolean final configuration has output-encoding length, and space bounds are monotone.

Exit: definitions and elementary lemmas compile; exact-type examples confirm the language type is `Language Bool` and no time restriction is hidden in PSPACE.

### S02 — Run algebra and all-prefix bounds

Connect the chosen iterator with Mathlib's `TM2Outputs`/`EvalsTo` and the existing `run`. Prove iteration concatenation, prefix decomposition, terminal uniqueness, and absence of successful configurations after the terminal step has returned `none`. State a reusable way to bound every configuration before and at a successful halt.

In `Space/Frame.lean`, define and prove preservation of stacks outside an explicitly listed active region. In `Space/PeakComposition.lean`, package a finite run segment with entry/exit assertions and a bound on all its prefixes. Prove sequential composition uses the maximum of the two absolute peak bounds. If a routine's contract counts only its private stacks, add the retained external-stack space before applying that rule. A repeated-loop version may be completed in S14, using a common bound and a restored loop-entry invariant.

Exit: a run-prefix API that downstream tasks can use without repeatedly unfolding `Option.bind` or guessing whether a halt costs an extra step.

### S03 — Reachable alphabets and primitive peaks

For every stack `j`, collect input symbols when `j=k₀` and all push-expression images at `j` from every finite program label and every finite state. Prove these sets finite, then prove invariance by induction on `Stmt` and on runs. Avoid constructing a nonexistent `Fintype (tm.Γ j)` for arbitrary source stacks.

Bound the maximum number of pushes in a statement, including the branch chosen; use the existing `pushBudget` structure. Record the relation between statement-boundary space and space during its internal primitive operations.

Exit: meaningful finite-symbol interpretation of the chosen stack-space model, without an extra assumption about the source checker.

### S04 — Polynomial time implies polynomial space for a checker call

From the actual `TM2ComputableInPolyTime` certificate for `R`, extract its machine and runtime polynomial `T`. Let `D` be its proved finite per-step stack-growth constant. Prove a bound of the form `inputLength + D * T.eval inputLength`, enlarged for the precise termination convention if necessary, on every reachable configuration of a successful call.

Do not stop at `t ≤ T(inputLength) → space(t) ≤ ...`; use the halting certificate and S02 to prove all later iterations cannot create new larger configurations. Account for internal statement peaks if included in the declared measure.

Exit: a generic certificate-to-space theorem that supplies the bound from `PolyTimeChecker R`, with no caller-supplied space hypothesis.

### S05 — Fixed-width binary words

Use little-endian Boolean lists with explicit length invariants. Define `value` or prove equivalence to an existing one. Prove `value w < 2^w.length`, encoding/decoding for values below `2^m`, and a bijection between width-`m` words and `Fin m → Bool` via `List.ofFn` and indexing.

Define functional increment returning `(newWord, overflow)`, preserving width. Prove `newValue = oldValue+1` without overflow and `oldValue=2^m-1`, `newValue=0` on overflow. At width zero, increment must report overflow and leave the empty word.

Exit: no arithmetic convention is left implicit. Small executable examples cover widths 0, 1 and 2, in addition to general proofs.

### S06 — Enumeration and prefix-count specification

Define a mathematical prefix count `A(x,m,j)` counting accepting witnesses with numeric value below `j`, for `j ≤ 2^m`. Finite sets are allowed in this specification; they must not become the machine's stored data.

Prove `A(...,0)=0`, `A(...,j+1)=A(...,j)+indicator(R(x,word(m,j)))` for `j<2^m`, `A≤j`, and `A(...,2^m)=ShiClassPP.countAccept R x m` using S05's bijection. Prove increment enumerates every word once in the specified order.

Exit: exact agreement with the existing PP counting scaffold, including the unique empty word.

### S07 — Binary increment machine

Implement a finite-state ripple-carry routine over Boolean stacks. Restore the output to the frozen little-endian orientation. Prove it implements S05's increment, preserves external stacks, terminates, and has peak space at most a fixed linear function of the word width plus entry space on protected stacks.

Use an `m`-bit witness word with a one-bit overflow flag; use an `m+1`-bit accepting counter. The latter never overflows during legal enumeration because at most `2^m` increments occur. Prove this rather than assuming it.

Exit: actual finite machine operations, exact run, frame theorem and peak bound. A functional increment lemma alone is insufficient.

### S08 — Copy, reverse, restore, and clear routines

Construct reusable stack routines for preserving master input/witness while emitting working copies. A pair of reversals may restore order; prove the final orientation explicitly. Clearing must decrease stack space and terminate. Bound temporary duplication at every phase.

Exit: routines with contracts for input/output stacks, untouched stacks, finite control reset, peak space and termination. Handle empty stacks and explicit aliasing conditions.

### S09 — Witness-length initialization

Compute `n = x.length` without destroying the master input and construct a unary width budget of length `m=n^k`. Since `k` is fixed in the PP witness, its repeated-multiplication control can be hard-coded finitely; `n` and `m` must live on stacks, not in the control-state type.

A simple repeated-addition implementation is acceptable. Prove intermediate storage polynomial in `n`, with degree/constants depending on fixed `k`. For `k=0`, initialize the result to one even at `n=0`. Then allocate `m` zero witness bits and `m+1` zero accepting-count bits.

This task only needs a polynomial **space** guarantee and termination; do not make efficient arithmetic a new research project. Never allocate unary `2^m`.

Exit: correct initialized registers, a terminating concrete machine, and a polynomial peak bound.

### S10 — Embed and restart the checker

Given the extracted checker machine, embed its stacks under an injective assignment into a disjoint source-stack summand; add external Boolean stacks for master input, witness and accepting counter. Use a finite disjoint-sum label set and a finite product/sum of control states. Preserve the possibility `k₀=k₁` within the source summand.

Prepare the exact tagged list `encodePair (x,w)` and map through `inputAlphabet.invFun`. Lift the source statements structurally; redirect a source halt to a continuation. Source load operations must not overwrite the wrapper's phase/flags. Source operations must leave external stacks unchanged.

After a successful source run, read the encoded answer through `outputAlphabet`, clear the checker output, and restore the canonical source state so the next invocation starts afresh. Prove these facts for the **same embedded machine**. The existing whole-computation composition operator may consume its input; it is not automatically the needed retaining/restarting wrapper.

Exit: a generic call contract with exact Boolean answer, termination, protected-stack preservation, reusable clean source workspace, and S04's peak-space bound plus wrapper overhead.

### S11 — Strict-majority test machine

Given an exact `m+1`-bit accepting count `a`, decide `2*a > 2^m`. Use a binary shift and comparison, or a separately proved equivalent bit test. A safe generic comparison allocates `m+2` bits for both operands: prepend a zero to the little-endian count for doubling; represent the threshold as `m` zeros followed by one and a final padding zero.

This comparison must handle `m=0`, ties and `a=2^m`. The threshold is stored in binary, using `O(m)` space. If reusing the existing borrow machine, prove its precise strict/non-strict orientation and whether it consumes inputs. Consumption is acceptable in the final phase if cleanup handles all leftovers.

Exit: concrete Boolean output correctness, termination and linear peak space. Do not implement doubling by unary replication of the numeric count.

### S12 — Abstract loop invariant and termination

Before constructing the full control graph, freeze the following invariant at each loop head:

- master input is the original `x`;
- width is `m=n^k`;
- witness is the fixed-width encoding of a ghost index `j<2^m`;
- accepting counter equals `A(x,m,j)`;
- checker and routine scratch stacks are empty in their required initial states;
- control is at the loop-head label;
- every protected register has its prescribed width/orientation.

One iteration invokes the checker, conditionally increments the accepting counter, and then increments the witness. On overflow, all `2^m` witnesses have been processed. Otherwise the invariant holds for `j+1`.

Use `2^m-j` as a mathematical well-founded measure. It may appear in the proof but is not a stored unary counter. A proof by induction over all iterations is fine; an execution that materializes all witnesses is not.

Exit: the abstract invariant and termination proof using precisely the subroutine contracts available from S07–S11. Any assumed contracts must be visibly temporary and discharged in S13.

### S13 — Assemble the actual finite enumerator

Define a fixed `FinTM2` whose labels cover initialization, input preparation, checker execution, count update, witness update, final comparison and final cleanup. Parameterize it only by the fixed checker certificate and exponent `k`.

Implement all handoffs and instantiate S12 with actual routines. Prove final output is `decide (2 * countAccept R x (x.length^k) > 2^(x.length^k))`, with the output in Mathlib's canonical `haltList` shape. Include output preparation, control reset and clearing all other stacks in the termination proof.

Exit: unconditional total correctness of the actual machine. This is not yet the space theorem.

### S14 — Peak-space proof for arbitrarily many iterations

Use phase-specific invariants and S07–S11. Prove the same bound at every loop entry and throughout each routine. The completed cleanup restores scratch usage for the next iteration.

Let `m=n^k`, `u=n+m`, and let `T` be the original checker's time polynomial. A typical target shape is

`P(n) = C * (n + n^k + 1) + D * T(n+n^k) + Qinit(n)`

for fixed constants `C,D` and a proved initialization polynomial `Qinit`. Enlarge constants as required; the displayed formula is a design guide, not permission to assert an unproved bound. Formalize polynomial composition as `T.comp (X + X^k)` with the pinned API's actual lemma names.

Crucially, **do not multiply this bound by `2^m`**. Sequential reuse bounds peak space by a maximum of phase peaks plus retained storage, not by a sum over iterations. A retained input copy, witness, count, width markers and all temporary copies must be counted simultaneously where they coexist.

Exit: `SpaceBoundedOn` for every input and every reachable configuration of exactly S13's machine, with one explicit polynomial. Source correctness and space cannot refer to different machines.

### S15 — PP containment and BQP composition

Package S13–S14 into `PolySpaceDecider`. Unpack original PP membership and use its strict-majority equivalence to prove `ShiSpace.pp_subset_pspace`. Then import the original BQP endpoint and prove `ShiBQP.bqp_subset_pspace` by inclusion composition.

Exit: exact endpoint statements with no extra hypotheses, no altered PP witness length, and no alternative BQP definition.

### S16 — Fresh audits, clean build and documentation

Create fresh-import exact-type checks and in-kernel axiom checks for the class endpoints and the major construction lemmas. Inspect full declarations and dependent definitions for hidden assumptions, not just axiom lists.

Perform a clean source-matched build of the new theorem's complete project import closure on Sherlock, using the pinned Mathlib libraries. Record source/object hashes, dependency graph, logs, toolchain, job/allocation metadata, exit codes, selected declaration reports and reuse counts. A final clean project build should report zero reused project objects; cached Mathlib is allowed and must be described accurately.

Update the project/root READMEs with the exact proved endpoint and model conventions only after acceptance. Keep partial progress and plans labeled as such.

## 8. Scheduling and bounded work for the executor

Recommended sequence:

`S00 → S01 → S02 → S03 → S04 → S05 → S06 → S07 → S08 → S09 → S10 → S11 → S12 → S13 → S14 → S15 → S16`.

Some mathematical tasks are independent, but the default executor should work serially. This plan does not request spawning agents. Do not begin several competing implementations of the same helper.

The harder design tasks are S10, S13 and S14. Break each into one statement constructor, one phase or one invariant at a time. If they need a stronger model, leave a minimal handoff containing the exact missing theorem and diagnostic; continue independent bounded tasks where possible.

This is a substantial machine-construction project even though the textbook argument is short. The plan makes small tasks suitable for a less capable executor; it does not guarantee that the embedding and global invariant can be completed without a stronger review. No elapsed-time estimate should substitute for the acceptance gates.

For each task:

1. Read its direct dependencies and the last progress entry. Do not reload the full proof archive.
2. Write its exact intended theorem type before its proof.
3. Keep implementation and proof helpers in the assigned module.
4. Compile the new module and necessary changed dependents on Sherlock.
5. Run its fresh-import audit; record full statements, allowed axioms and source hashes.
6. Update a compact progress ledger with evidence and the next task.

After three failed repairs of the same diagnostic, preserve the candidate and write the exact Lean goal, relevant declaration types and attempted fixes. Do not solve an elaboration problem by weakening the theorem. Do not repeatedly raise heartbeat limits without diagnosing the cause.

## 9. Verification and compute workflow

The repository requires **all Lean compilation on Sherlock within a Slurm allocation**. Do not run Lean/Lake compilation on the laptop or a login node. Read `/etc/agents/AGENTS.md` and applicable remote instructions before cluster operations. Discover active allocations; never reuse job identifiers from old logs without checking live state.

The baseline BQP clean build used three workers in a 4-core/16-GB allocation. Treat this as measured baseline evidence, not a universal memory guarantee. One Lean thread per process; parallelize only independent ready modules and stay within allocated memory/CPU limits. Poll no more often than permitted by cluster policy and preserve meaningful batch work.

S00 can run these local read-only checks without invoking Lean:

```bash
python3 bqp-pp/scripts/verify.py
git status --short
git rev-parse HEAD
```

The new build scripts must, before accepting results:

- verify Lean and Mathlib versions;
- verify every submitted source hash and import edge;
- reject missing, failed or blocked modules;
- verify source-to-object correspondence and artifact hashes;
- reject missing or duplicate required axiom reports;
- reject all transitive axioms outside `propext`, `Classical.choice`, `Quot.sound`;
- compile fresh exact-type checks for both final theorems;
- distinguish a dependency-closure build from a full-project build;
- preserve prior accepted records rather than overwrite them with a new label.

Copy the design of `bqp-pp/scripts/verify.py` and `build_graph.py` where useful, but do not mutate the baseline acceptance logic to accommodate the new project. Verify new manifest/audit tooling with temporary negative fixtures: missing report, bad hash and forbidden axiom must be rejected. Lean semantic tests should address real edge cases, not merely restate implementations.

Once build scripts exist, document exact commands that were actually exercised. Do not publish guessed setup commands as tested. Fetch durable evidence before releasing the allocation. Never transfer macOS Lean objects into the Linux build.

## 10. Anti-shortcut rules and common failure modes

- No `sorry`, `admit`, new axioms or hidden `proof_wanted` in the endpoint closure. Existing statement stubs in the baseline are not usable proofs; only audited reconstructed exports are safe.
- No hypothesis whose content is the missing simulation, space bound, enumeration correctness or halting proof.
- No `Nat`-valued unbounded control state, input-sized label type, infinite precomputed answer table or atomic call to arbitrary `R` in the machine's step function.
- Abstract `R` may appear in mathematical specifications. Its actual machine must be used in executable control.
- `Classical.choice` may select a proved computation witness or finite enumeration; it cannot replace a missing computation proof.
- No materialized list of all `2^m` witnesses; no unary accepting count; no exponential unary clock.
- No reliance on host-language execution or successful `#eval` as proof of a Mathlib machine bound.
- No inference of space from total exponential runtime. Prove scratch reuse and phase peak bounds.
- No equivalence between binary and tagged-pair alphabets without an actual encoding translation; an alphabet equivalence cannot change cardinality.
- No output-only space checks: temporary copying and subroutine execution contribute to peak usage.
- No ignoring short inputs, all-accept overflow, majority ties or the unique zero-width witness.
- No silent redefinition of PP, BQP or the historical PSPACE. Use the documented corrected class.
- No claim of standard-model equivalence beyond what the formal development establishes.
- Do not count definitions, conditional lemmas, compiled files or published theorem stubs as completed endpoint proofs.

## 11. Completion checklist

- [ ] Corrected PSPACE explicitly separates total computability from polynomial space.
- [ ] All-input polynomial bounds allow constant and linear overhead.
- [ ] Reachable alphabets and statement granularity have been justified.
- [ ] The actual checker certificate is embedded, with exact pair/alphabet conventions.
- [ ] Binary enumeration covers precisely `Fin m → Bool` once each.
- [ ] The count register represents `2^m` without overflow.
- [ ] All empty-input, zero-width, immediate-halt and tie cases are proved.
- [ ] The entire enumerator halts with canonical Boolean output.
- [ ] Every reachable configuration satisfies the polynomial bound.
- [ ] `ShiSpace.pp_subset_pspace` has no extra premises.
- [ ] `ShiBQP.bqp_subset_pspace` composes the existing BQP theorem unchanged.
- [ ] Fresh-import exact-type and axiom audits pass.
- [ ] Complete source-matched clean build evidence is saved.
- [ ] Baseline BQP source-manifest verification still passes.
- [ ] READMEs distinguish mathematical results, model conventions and remaining model-equivalence work.

## 12. Mathematical references

- John Watrous, [Quantum Computational Complexity](https://cs.uwaterloo.ca/~watrous/Papers/QuantumComputationalComplexity.pdf), for the quantum/classical class context and BQP counting upper bounds.
- Sebastiaan A. Terwijn, [Complexity Theory](https://www.math.ru.nl/~terwijn/teaching/complexitytheory.pdf), the PP ⊆ PSPACE argument by sequential path enumeration and counting.
- [Mathlib TM2 computability API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/TuringMachine/Computable.html). Online documentation can drift; the pinned local source is authoritative for declaration signatures.
- [Mathlib stack-machine semantics](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/TuringMachine/StackTuringMachine.html), especially `Stmt`, `stepAux`, `step` and `Cfg`.

## 13. First bounded execution prompt

> Read `plans/BQP_PSPACE_PLAN.md` in `lean-quantum-complexity`. Execute S00 and S01 only. Inspect the published BQP/PP interfaces and create the separate `bqp-pspace` space-model module. Define PSPACE using total `TM2Computable` plus a polynomial bound on every reachable configuration; never use the historical polynomial-time PSPACE definition. Prove initialization, final-output and bound-monotonicity lemmas. Preserve the baseline BQP source graph and its manifest. Follow the repository's Sherlock-only Lean compilation policy. Verify the new module and fresh-import axiom audit, then record exact source/evidence locations and the next task. Do not start the full enumerator, change class definitions to ease a proof, or claim either containment is complete.
