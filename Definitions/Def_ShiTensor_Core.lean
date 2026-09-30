/-
# Amplitude-array tensor product of computational-basis state vectors

Splits a `Bits (m + p)` index into its left `Bits m` and right `Bits p` halves along
`Fin.castAdd` / `Fin.natAdd`, and defines the product state whose amplitude at a joint index
is the product of the two factor amplitudes.

## Main definitions

* `ShiTensor.leftBits y` -- the first `m` bits of `y : Bits (m + p)`, i.e. `y ∘ Fin.castAdd p`.
* `ShiTensor.rightBits y` -- the last `p` bits, i.e. `y ∘ Fin.natAdd m`.
* `ShiTensor.tensor ψ φ` -- the joint state `fun y => ψ (leftBits y) * φ (rightBits y)`.

## HONEST LIMITATIONS -- read before citing this as a tensor product

1. **This is an AMPLITUDE-ARRAY product, not a bundled tensor product.** There is NO connection
   to Mathlib's `TensorProduct`, no universal property, no bilinear map, and no claim that
   `QState (m + p)` is spanned by such products. `tensor` is a plain formula on functions.
2. **No bijectivity fact is proved here.** `leftBits` and `rightBits` are the two projections
   induced by `Fin.castAdd`/`Fin.natAdd`, and `y ↦ (leftBits y, rightBits y)` IS a bijection
   `Bits (m + p) ≃ Bits m × Bits p`, but that is NOT established in this file. Every reindexing
   argument over a joint index therefore needs that bijection supplied separately.
3. **No normalisation and no unitarity.** `ψ` and `φ` are arbitrary functions to `ℂ`, not unit
   vectors. Nothing here says the tensor of normalised states is normalised; that requires the
   reindexing of limitation 2 and is a separate theorem.
4. **Nothing connects `tensor` to circuit dynamics.** No relation to `runLayered`, `runLayer`,
   `Instr.apply`, `apply1`, `cnotState`, `embedCirc`, `inputState`, `outDist` or `acceptProb` is
   stated or proved. In particular the fact a caller most likely wants -- that a circuit acting
   on disjoint wire blocks maps a product state to a product state, so acceptance probabilities
   MULTIPLY -- is NOT here and does not follow from anything in this file.
5. **No independence interpretation is justified.** Calling `tensor` a product of "independent"
   registers is motivation, not mathematics: there is no measure, no `PMF`, and no probabilistic
   structure anywhere in this file.
6. **The splitting is positional and asymmetric.** `leftBits`/`rightBits` are tied to the
   specific `m + p` decomposition; no commutativity or associativity of `tensor` is stated, and
   `tensor ψ φ` and `tensor φ ψ` inhabit different types unless `m = p`.
7. **Every limitation of `Def_ShiShallow_Core` applies**, since `Bits` and `QState` come from
   there: gate set `H, S, T, X, CNOT` with no universality theorem, and single-output-wire
   acceptance with no intermediate measurement or mixed-state formalism.
8. **DEFINITIONS ONLY: this file contains no theorem or lemma.** Even the `rfl`-restatement of
   `tensor` is omitted deliberately. A theorem placed inside a definition bundle is permanently
   unrecoverable, so every derivable fact above must be a SEPARATE theorem submission.
-/
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiTensor

open ShiShallow

/-- The first `m` bits of a joint index `y : Bits (m + p)`, read along `Fin.castAdd p`. -/
def leftBits {m p : ℕ} (y : Bits (m + p)) : Bits m := fun i => y (Fin.castAdd p i)

/-- The last `p` bits of a joint index `y : Bits (m + p)`, read along `Fin.natAdd m`. -/
def rightBits {m p : ℕ} (y : Bits (m + p)) : Bits p := fun j => y (Fin.natAdd m j)

/-- The amplitude-array tensor product: the joint amplitude at `y` is the product of the left
factor's amplitude at `leftBits y` and the right factor's amplitude at `rightBits y`.

See the module docstring: this is a formula on functions, NOT a bundled tensor product, and
nothing here relates it to circuit dynamics or to normalisation. -/
def tensor {m p : ℕ} (ψ : QState m) (φ : QState p) : QState (m + p) :=
  fun y => ψ (leftBits y) * φ (rightBits y)

end ShiTensor
