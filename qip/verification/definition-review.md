# Q41 — review of the definitions behind `qip_eq_qip3`

Axiom cleanliness says nothing about whether the classes are the intended ones. This note
checks the definitions that `ShiQIP.qip_eq_qip3 : ShiQIP.QIP = ShiQIP.QIPm 3` quantifies over,
read directly from the sources. It was written by the same agent that wrote the proof; an
independent human review is still recommended.

## Classes (`QIP.Classes`)

- `PromiseProblem`: yes and no sets of `List Bool`, disjoint. `ofLanguage L = (L, Lᶜ)`.
- `Decides F A`: **completeness** — every yes instance has *some* prover with
  `2/3 ≤ accept P`; **soundness** — on every no instance *every* prover has `accept P ≤ 1/3`.
  The thresholds are the usual constants with non-strict inequalities.
- `QIP = {A | ∃ F : VerifierFamily, Decides F A}`.
- `QIPm k = {A | ∃ F, (∀ x, (F.desc x).HasSchedule k) ∧ Decides F A}`. Neither class is defined
  through the other, through an SDP, or through a transformation. `QIPm k ⊆ QIP` is immediate
  (`qipm_subset_qip`); the substantive direction is `QIP ⊆ QIPm 3`.

## Uniformity and size (`VerifierFamily`)

- `desc : Str → Desc` with `valid : ∀ x, (desc x).Valid` (the decidable checker `Desc.check`:
  output wire private, alternating messages, `numMsgs + 1` blocks, every gate acts only on wires
  the verifier holds during its block).
- `gen : Str → Str` with `gen_polyTime : PvsNP.PolyTimeComputable gen` (Cook's definition: a
  multi-stack Turing machine halting within a polynomial in `|x|` with the output on its output
  stack) and `gen_eq : ∀ x, gen x = encode (desc x)`. The encoding (`QIP.Encoding`) is explicit
  and unary, and is decoded strictly (`decode_eq_some_iff`), so the generator prints exactly the
  verifier and nothing is hidden in the encoding.
- One polynomial `bound` bounds messages, total wires (which include every message width) and
  gates, evaluated at `x.length` (lengths `0` and `1` included).
- The verifier depends on `x` only through `desc x`; a classical input must be prepared by
  explicit gates.

For the transformed family `F.three`, the generator is `printer ∘ F.gen` where `printer` is
proved `PolyTimeComputable` by exhibiting concrete `FinTM2` machines (`QIP.Uniform.*`). No Lean
recursion is assumed to be polynomial time; every machine has a fixed finite label type
independent of the input.

## Interaction (`QIP.Execution`, `QIP.StrategyRealization`)

- **Adversarial memory.** `Prover d = OpStrategy (Reg d) (Reg d) d.numMsgs`: arbitrary finite
  memory types `M k : Type` (no bound on dimension), an arbitrary initial density operator, and
  arbitrary quantum channels `act k` on the message register and the memory, one per message.
  Soundness quantifies over all of these, so it covers arbitrary (finite-dimensional) entangled
  provers. Infinite-dimensional provers are not modelled; for finite verifiers this is the
  standard model.
- **No signalling.** A prover turn acts on its message register and memory only
  (`proverStep_marginal`); private wires never lie in a message register (`inReg_ge_priv`).
- **Verifier.** All `totalWires` wires start in `|0⟩`; block `j` is the exact unitary of its
  H/S/T/X/CNOT gates; acceptance is the probability that the output wire reads `1`, with the
  prover memory traced out (`accept`). `accept_mem_Icc`: it lies in `[0, 1]`.
- **Value.** `value d = sSup (range accept)` is attained (`value_attained`); `le_value_iff` and
  `value_le_iff` translate `Decides` to statements about `value`.

## Message count (`QIP.Syntax`)

`d.HasSchedule k ↔ d.msgs.map dir = stdSchedule k`: exactly `k` directed messages, alternating,
the last to the verifier. `stdSchedule 3 = [toVerifier, toProver, toVerifier]` (prover → verifier,
verifier → prover, prover → verifier), by `rfl`. Message widths may be zero but are counted in
the wire bound.

## What the proof does not use

No statement of `QIP = PSPACE`, `IP = PSPACE`, `BQP ⊆ PSPACE` or the target equality is cited.
The only axioms are `propext`, `Classical.choice` and `Quot.sound` (`Audit/Final.lean`).
