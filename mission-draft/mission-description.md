## Motivation

A QMA verifier receives a quantum witness and checks it with a circuit generated efficiently from the input. An acceptance probability separated by an inverse-polynomial gap is enough to define the class, but applications often need the probability of a wrong answer to be exponentially small. Repeating the verifier on many supplied witness registers achieves this error reduction while allowing the witness to grow. Marriott and Watrous proved the stronger statement that the same error reduction can be obtained **without increasing the number of witness qubits** [Quantum Arthur–Merlin Games, Section 3](https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf).

The existing Lean development verifies the copy-based theorem, including soundness for witnesses entangled across the copies, and constructs a uniform circuit family with polynomial resources. This mission asks for the separate witness-preserving theorem. The paper already proves that mathematical statement; the open work here is its formalization in the stated QMA circuit model.

## Setting

At each input length $n$, a verifier has $m(n)$ witness qubits, a finite work register, a designated output wire, and a quantum circuit. A uniformly generated family has a polynomial-time classical procedure that emits the complete circuit description, including the witness and work-register sizes. On yes-instances, some normalized witness makes the verifier accept with probability at least $a(n)$. On no-instances, every normalized witness is accepted with probability at most $b(n)$. The thresholds satisfy $0\le b(n)\le a(n)\le1$ and $a(n)-b(n)\ge1/q(n)$ for a polynomial $q$.

The existing formalization represents witnesses as complex amplitude functions on bit strings, requires normalization explicitly, and uses layered circuits over its specified finite gate set. It also represents efficiently available real thresholds by polynomial-time procedures that output dyadic approximations. These are part of the formal statement's interface and must be made visible to users of the mission.

## Target

For every polynomial error exponent $r$ and every source verifier satisfying the conditions above, construct a uniformly generated, well-formed, polynomial-resource verifier for the same language, with completeness at least $1-2^{-r(n)}$ and soundness at most $2^{-r(n)}$, while keeping the witness count **exactly $m(n)$ at every input length**:

$$m_{\mathrm{new}}(n)=m_{\mathrm{old}}(n).$$

This is the witness-preserving strong error-reduction result of Marriott and Watrous (Theorem 4). The existing copy-based result corresponds to the weaker QMA class inclusion in Theorem 3 and will be linked as a proved background result. The mission goal must state the witness-count equation explicitly so that a copy-based amplifier cannot satisfy it.

## Significance

Witness-preserving amplification lets a QMA protocol demand much stronger reliability without asking the prover for a longer message. That matters whenever witness size is itself a resource being compared or bounded. The copy-based theorem shows that the QMA class is robust under error reduction, but does not establish this fixed-message guarantee.

Formalizing the stronger result would add a reusable account of a verifier that reuses one witness, proves soundness for every normalized input state, and compiles its behavior into an ordinary uniform circuit family. Those components can support later formalizations that reason about repeated quantum verification under a fixed witness budget.

## Difficulty

The completed copy-based proof uses three independent verifier blocks in each amplification round and bounds arbitrary entangled witnesses across those blocks. Its circuit resource analysis therefore allows the witness count to grow. A witness-preserving argument cannot use that construction. It must analyze repeated verification on one register and establish exponentially small error without assuming the input witness has a special spectral form. The formal circuit model currently exposes final-output measurements; any additional measurement behavior used in the analysis must be justified in that model and shown implementable by a finite, uniformly generated circuit.

The central audit point is the exact witness-length equation. A theorem that merely returns another polynomial-size witness, or that changes the source verifier's witness definition, is a useful class-level result but does not prove this mission's target.

## Formalization scope

The goal is parameterized by input-length-dependent completeness and soundness thresholds with an inverse-polynomial gap, and by a polynomial target exponent. Every witness quantifier is over normalized states. The output verifier must satisfy the same well-formedness and polynomial-resource conditions as the completed copy-based development. The platform statement uses its existing `ShiClassQMAU.UniformQMA` circuit-family encoding, which includes the witness and ancilla counts separately. A final proof should be kernel checked with only Lean's standard logical axioms and should not assume an amplification transducer or an unproved measurement lemma.

The paper quantifies over the class `poly` of unary-time constructible functions. This proposal represents the gap denominator and target exponent as literal `Polynomial ℕ` values, matching the checked copy-based development. It therefore formalizes a polynomial-parameter instance of Theorem 4 rather than the paper's full function-class generality. The threshold functions are supplied by polynomial-time dyadic approximators in place of the paper's informal efficient-computation convention. These interface choices are explicit in the Lean goal and should not be read as a proof of the broader formulation.

The local copy-based proof is complete and audited, but it has not yet been transplanted to Prove2Me. Its publication is preparatory work for this mission, not evidence that the witness-preserving goal is already solved. The proposal should reference the published copy-based endpoint and include only a few substantial milestones, so each item is meaningful to audit.

## Selected references

- C. Marriott and J. Watrous, *Quantum Arthur–Merlin Games*, Computational Complexity 14 (2005), Section 3, Theorems 3 and 4. [Paper](https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf).
- A. Kitaev, A. Shen, and M. Vyalyi, *Classical and Quantum Computation*, Graduate Studies in Mathematics 47, American Mathematical Society (2002), Section 14.2, cited by Marriott and Watrous for the copy-based amplification proof.
