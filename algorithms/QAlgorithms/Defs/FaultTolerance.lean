import QAlgorithms.Defs.LocCircuit

/-!
# Fault-tolerant protocols: gadgets, ideal and *-decoders, Defs. 1–5, ExRecs and their
correctness (shared definition layer)

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N" (PDF pages), §§4.2, 5.1–5.2.

Model. A protocol uses one `[[n, 1, 2t + 1]]` code (p.19). Each gadget is a concrete circuit of
locations; a gadget for a location acting on `k` blocks runs on `k · (n + A)` qubits, where
physical qubit (block `i`, position `j`) is wire `finProdFinEquiv (i, j)`, positions `j < n` are
the block's data qubits and `n ≤ j < n + A` its ancillas. The superoperator a gadget implements
under a Pauli fault arrangement (p.20: faults are Pauli errors) is computed from
`LocCircuit.run`: the input on the data qubits, the ancillas in `|0⟩`, the measurement records
summed over, the ancillas traced out. All the diagram equations of Defs. 2–5 and 8 are equalities
of superoperators, i.e. on every input operator ("for all input states, including superpositions
and parts of entangled states", p.38).
-/

namespace QAlgorithms

open scoped Matrix

/-- Gottesman intro p.19 (Def. 1, §4.2), p.20 and p.33 (Def. 6): the data of a fault-tolerant
protocol for one `[[n, 1, 2t + 1]]` code: block length `n`, number `t` of errors corrected,
number `A` of ancillas per block, the code, its encoding isometry, the ideal decoder, a gadget for
every type of location (the wait gadget is the gate gadget for `U = I`, p.20), the error-correction
gadget, and the classical decoding of the measurement gadget's outcomes to the logical outcome. -/
structure FTProtocol where
  n : ℕ
  t : ℕ
  A : ℕ
  code : Submodule ℂ (EuclideanSpace ℂ (Qubits n))
  enc : Matrix (Qubits n) Bool ℂ
  dec : Superop (Qubits n) Bool
  gadget : (κ : LocKind) → LocCircuit (κ.arity * (n + A))
  ec : LocCircuit (n + A)
  measDecode : List Bool → Bool

/-- Gottesman intro p.19 (§4.2: one encoded qubit per block): `enc` encodes one qubit into the
code `C`: it is an isometry (`enc† enc = I`) with range `C`. -/
def IsEncodingOf {n : ℕ} (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n)))
    (enc : Matrix (Qubits n) Bool ℂ) : Prop :=
  encᴴ * enc = 1 ∧ LinearMap.range (Matrix.toEuclideanLin enc) = C

/-- Gottesman intro p.19 (Def. 1: "a map constructed by taking the input state and performing a
decoding operation (including error correction) consisting of a circuit with no faulty
locations"): `D` is an ideal decoder for the encoding `enc` correcting `t` errors: a quantum
operation from one block to one qubit that maps `E (enc ψ)` back to `ψ` for every error `E` in the
span of the Pauli errors of weight `≤ t` and every normalized one-qubit state `ψ` (weighted by
`‖E enc ψ‖²`; by linearity this covers mixed and entangled inputs). Its action outside the
`t`-correctable inputs is unconstrained (any fault-free decoding circuit qualifies). -/
def IsIdealDecoder {n : ℕ} (enc : Matrix (Qubits n) Bool ℂ) (t : ℕ) (D : Superop (Qubits n) Bool) :
    Prop :=
  IsChannel D ∧ ∀ E ∈ pauliSpan n t, ∀ ψ : EuclideanSpace ℂ Bool, ‖ψ‖ = 1 →
    D (pureDensity (act E (Matrix.toEuclideanLin enc ψ))) =
      ((‖act E (Matrix.toEuclideanLin enc ψ)‖ ^ 2 : ℝ) : ℂ) • pureDensity ψ

/-- Gottesman intro p.37 (§5.2: "the *-decoder is a unitary operation" whose extra output holds the
error syndrome) and p.38 (Lemma 2: "the ideal decoder is just the *-decoder with the error syndrome
discarded"): `W` is a *-decoder for the ideal decoder `D` with syndrome register `Fin σ`. -/
def IsStarDecoder {n σ : ℕ} (D : Superop (Qubits n) Bool) (W : Matrix (Bool × Fin σ) (Qubits n) ℂ) :
    Prop :=
  Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ ∀ ρ, traceRight (W * ρ * Wᴴ) = D ρ

/-- The block layout of a gadget on `k` blocks: qubit `finProdFinEquiv (i, j)` is position `j` of
block `i`; positions `< n` are data, the others ancillas. -/
def blockLayout (k n A : ℕ) : Qubits (k * (n + A)) ≃ (Fin k → Qubits n) × (Fin k → Qubits A) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    ((Equiv.curry (Fin k) (Fin (n + A)) Bool).trans
      ((Equiv.arrowCongr (Equiv.refl (Fin k)) (qubitsAppendEquiv n A)).trans
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Qubits n) (fun _ => Qubits A))))

/-- The layout of the error-correction gadget on one block: positions `< n` are data. -/
def singleLayout (n A : ℕ) : Qubits (n + A) ≃ (Fin 1 → Qubits n) × (Fin 1 → Qubits A) :=
  (qubitsAppendEquiv n A).trans
    (Equiv.prodCongr (Equiv.funUnique (Fin 1) (Qubits n)).symm (Equiv.funUnique (Fin 1) (Qubits A)).symm)

/-- The data qubits of a gadget on `k` blocks. -/
def blockDataWires (k n A : ℕ) : Finset (Fin (k * (n + A))) :=
  Finset.univ.image fun p : Fin k × Fin n => finProdFinEquiv (p.1, Fin.castAdd A p.2)

/-- The data qubits of the error-correction gadget. -/
def ecDataWires (n A : ℕ) : Finset (Fin (n + A)) :=
  Finset.univ.image (Fin.castAdd A)

/-- The input operator `X` of the blocks' data placed on the data qubits, the ancillas in
`|0…0⟩⟨0…0|`, trivial environment. -/
def embedVia {N k n A : ℕ} (L : Qubits N ≃ (Fin k → Qubits n) × (Fin k → Qubits A))
    (X : Matrix (Fin k → Qubits n) (Fin k → Qubits n) ℂ) :
    Matrix (Qubits N × Fin 1) (Qubits N × Fin 1) ℂ :=
  Matrix.of fun p p' =>
    if (L p.1).2 = (fun _ _ => false) ∧ (L p'.1).2 = (fun _ _ => false) then X (L p.1).1 (L p'.1).1
    else 0

/-- The partial trace over the ancillas and the environment, keeping the blocks' data. -/
def traceVia {N k n A : ℕ} (L : Qubits N ≃ (Fin k → Qubits n) × (Fin k → Qubits A))
    (Y : Matrix (Qubits N × Fin 1) (Qubits N × Fin 1) ℂ) :
    Matrix (Fin k → Qubits n) (Fin k → Qubits n) ℂ :=
  Matrix.of fun x x' => ∑ a : Fin k → Qubits A, ∑ e : Fin 1, Y (L.symm (x, a), e) (L.symm (x', a), e)

/-- Gottesman intro p.20: the (unnormalized) state a gadget leaves under the Pauli arrangement
`fa`, started in `ρin`, summed over the measurement records accepted by `B`. -/
noncomputable def gadgetOut {N : ℕ} (G : LocCircuit N) (fa : PauliArrangement)
    (ρin : Matrix (Qubits N × Fin 1) (Qubits N × Fin 1) ℂ) (B : List Bool → Bool) :
    Matrix (Qubits N × Fin 1) (Qubits N × Fin 1) ℂ :=
  ∑ r : Fin G.measCount → Bool,
    if B (List.ofFn r) then G.run (pauliErr G fa) (fun r' => if r' = [] then ρin else 0) (List.ofFn r)
    else 0

/-- The number of faulty locations of a gadget under a Pauli arrangement (the `s` of its
diagram, p.20). -/
def faultCount {N : ℕ} (G : LocCircuit N) (fa : PauliArrangement) : ℕ :=
  (faultyLocs G fa).card

/-- Gottesman intro p.20 (Def. 4) and p.35 (Def. 8): the location types handled as gates: `H`,
`R_{π/8}`, CNOT and wait (the wait gadget being the gate gadget for `U = I`). -/
def LocKind.IsGateOrWait (κ : LocKind) : Prop :=
  κ = .had ∨ κ = .tgate ∨ κ = .cnot ∨ κ = .wait

namespace FTProtocol

variable (P : FTProtocol)

/-- Gottesman intro pp.20–21: the superoperator on the `k` input blocks implemented by the gadget
for the gate (or wait) location type `κ` under the Pauli arrangement `fa`. -/
noncomputable def gateOp (κ : LocKind) (fa : PauliArrangement) :
    Superop (Fin κ.arity → Qubits P.n) (Fin κ.arity → Qubits P.n) :=
  fun X => traceVia (blockLayout κ.arity P.n P.A)
    (gadgetOut (P.gadget κ) fa (embedVia (blockLayout κ.arity P.n P.A) X) fun _ => true)

/-- Gottesman intro p.21 (Def. 3): the block state output by the preparation gadget under `fa`
(it takes no input: every qubit is prepared inside it). -/
noncomputable def prepState (fa : PauliArrangement) : Matrix (Qubits P.n) (Qubits P.n) ℂ :=
  (traceVia (blockLayout 1 P.n P.A)
    (gadgetOut (P.gadget .prep) fa (Matrix.kronecker (pureDensity (zeroKet _)) 1) fun _ => true)).submatrix
      (fun y _ => y) (fun y _ => y)

/-- Gottesman intro p.20 (Def. 2): the measurement gadget under `fa` as an instrument on one
block: the weight of the decoded logical outcome `β` (`false` = `|0⟩`) on the block operator `ρ`.
Since every qubit of the gadget is measured, nothing else remains; equality of these functionals on
every block operator is equality of the instruments ("the remainder of the computer is left in the
same relative state"). -/
noncomputable def measFunctional (fa : PauliArrangement) (β : Bool) :
    Matrix (Qubits P.n) (Qubits P.n) ℂ → ℂ :=
  fun ρ => (gadgetOut (P.gadget .meas) fa
    (embedVia (blockLayout 1 P.n P.A) (ρ.submatrix (fun x => x 0) (fun x => x 0)))
    fun r => decide (P.measDecode r = β)).trace

/-- Gottesman intro p.21 (Def. 5): the superoperator on one block implemented by the
error-correction gadget under `fa`. -/
noncomputable def ecOp (fa : PauliArrangement) : Superop (Qubits P.n) (Qubits P.n) :=
  fun ρ => (traceVia (singleLayout P.n P.A)
    (gadgetOut P.ec fa (embedVia (singleLayout P.n P.A) (ρ.submatrix (fun x => x 0) (fun x => x 0)))
      fun _ => true)).submatrix (fun y _ => y) (fun y _ => y)

/-- Gottesman intro p.19 (Def. 1): the `r`-filter applied to a block. -/
noncomputable def filterOp (r : ℕ) : Superop (Qubits P.n) (Qubits P.n) :=
  conjSuperop (filterProj P.code r)

/-- Gottesman intro pp.19–22 (Defs. 1–5): the protocol is fault tolerant. The code is an
`[[n, 1, 2t + 1]]` code with encoding `enc` and ideal decoder `dec`; every gadget is a well-formed
circuit whose live qubits at its two ends are the data qubits of its input and output blocks; and,
for every Pauli fault arrangement with `s` faulty locations in the gadget and all filter sizes
(`F_r` the `r`-filter, applied to each block separately):
* Meas (Def. 2): `r + s ≤ t` → the gadget after `F_r` has the outcome weights of ideal decoding
  followed by a standard-basis measurement;
* Prep A, Prep B (Def. 3): `s ≤ t` → the output passes the `s`-filter, and decodes to `|0⟩`;
* Gate A, Gate B (Def. 4), for `H`, `R_{π/8}`, CNOT and wait: `s + Σ_i r_i ≤ t` → after the
  `r_i`-filters on the inputs, the output passes the `(s + Σ r_i)`-filter on each block, and
  decoding each block gives the ideal gate applied to the decoded inputs;
* EC A, EC B (Def. 5): `s ≤ t` → the output passes the `s`-filter, whatever the input;
  `r + s ≤ t` → decoding after the gadget equals decoding before it, after `F_r`. -/
def IsFaultTolerant : Prop :=
  IsQCode P.n 1 (2 * P.t + 1) P.code ∧ IsEncodingOf P.code P.enc ∧ IsIdealDecoder P.enc P.t P.dec ∧
  (P.gadget .prep).IsWellFormed ∅ (blockDataWires 1 P.n P.A) ∧
  (P.gadget .meas).IsWellFormed (blockDataWires 1 P.n P.A) ∅ ∧
  (∀ κ : LocKind, κ.IsGateOrWait →
    (P.gadget κ).IsWellFormed (blockDataWires κ.arity P.n P.A) (blockDataWires κ.arity P.n P.A)) ∧
  P.ec.IsWellFormed (ecDataWires P.n P.A) (ecDataWires P.n P.A) ∧
  -- Meas
  (∀ (fa : PauliArrangement) (r : ℕ), r + faultCount (P.gadget .meas) fa ≤ P.t →
    ∀ (β : Bool) (ρ : Matrix (Qubits P.n) (Qubits P.n) ℂ),
      P.measFunctional fa β (P.filterOp r ρ) = P.dec (P.filterOp r ρ) β β) ∧
  -- Prep A
  (∀ fa : PauliArrangement, faultCount (P.gadget .prep) fa ≤ P.t →
    P.filterOp (faultCount (P.gadget .prep) fa) (P.prepState fa) = P.prepState fa) ∧
  -- Prep B
  (∀ fa : PauliArrangement, faultCount (P.gadget .prep) fa ≤ P.t →
    P.dec (P.prepState fa) = pureDensity (ket false)) ∧
  -- Gate A
  (∀ κ : LocKind, κ.IsGateOrWait → ∀ (fa : PauliArrangement) (r : Fin κ.arity → ℕ),
    faultCount (P.gadget κ) fa + ∑ i, r i ≤ P.t →
      piSuperop (fun _ => P.filterOp (faultCount (P.gadget κ) fa + ∑ i, r i)) ∘ P.gateOp κ fa ∘
          piSuperop (fun i => P.filterOp (r i)) =
        P.gateOp κ fa ∘ piSuperop (fun i => P.filterOp (r i))) ∧
  -- Gate B
  (∀ κ : LocKind, κ.IsGateOrWait → ∀ (fa : PauliArrangement) (r : Fin κ.arity → ℕ),
    faultCount (P.gadget κ) fa + ∑ i, r i ≤ P.t →
      piSuperop (fun _ => P.dec) ∘ P.gateOp κ fa ∘ piSuperop (fun i => P.filterOp (r i)) =
        conjSuperop κ.idealMatrix ∘ piSuperop (fun _ => P.dec) ∘ piSuperop (fun i => P.filterOp (r i))) ∧
  -- EC A
  (∀ fa : PauliArrangement, faultCount P.ec fa ≤ P.t →
    P.filterOp (faultCount P.ec fa) ∘ P.ecOp fa = P.ecOp fa) ∧
  -- EC B
  (∀ (fa : PauliArrangement) (r : ℕ), r + faultCount P.ec fa ≤ P.t →
    P.dec ∘ P.ecOp fa ∘ P.filterOp r = P.dec ∘ P.filterOp r)

end FTProtocol

/-- Gottesman intro p.34 (Def. 7): the number of leading EC steps of an ExRec (one per input
block; none for a preparation). -/
def LocKind.leadCount : LocKind → ℕ
  | .prep => 0
  | κ => κ.arity

/-- Gottesman intro p.34 (Def. 7): the number of trailing EC steps of an ExRec (one per output
block; none for a measurement). -/
def LocKind.trailCount : LocKind → ℕ
  | .meas => 0
  | κ => κ.arity

/-- Gottesman intro p.34 (Def. 7), p.35 (Def. 9) and p.38 (Def. 10): a Pauli fault arrangement of
an ExRec of type `κ`: one for each leading EC, one for the gadget, one for each trailing EC. -/
structure ExRecFaults (κ : LocKind) where
  lead : Fin κ.leadCount → PauliArrangement
  gad : PauliArrangement
  trail : Fin κ.trailCount → PauliArrangement

/-- Gottesman intro p.35 (Def. 9) and p.38 (Def. 10): the number of faults in the ExRec, the
trailing ECs of the blocks in `trunc` being removed (truncation; `trunc = ∅` is the full ExRec). -/
def ExRecFaults.count (P : FTProtocol) {κ : LocKind} (F : ExRecFaults κ)
    (trunc : Finset (Fin κ.trailCount)) : ℕ :=
  ∑ i, faultCount P.ec (F.lead i) + faultCount (P.gadget κ) F.gad +
    ∑ i ∈ Finset.univ.filter (fun i => i ∉ trunc), faultCount P.ec (F.trail i)

namespace FTProtocol

variable (P : FTProtocol)

/-- The leading EC steps of a gate ExRec, one on each input block. -/
noncomputable def leadOp {k : ℕ} (lead : Fin k → PauliArrangement) :
    Superop (Fin k → Qubits P.n) (Fin k → Qubits P.n) :=
  piSuperop fun i => P.ecOp (lead i)

/-- The trailing EC steps of a gate ExRec, one on each output block not in `trunc` (removed
there, Def. 10). -/
noncomputable def trailOp {k : ℕ} (trail : Fin k → PauliArrangement) (trunc : Finset (Fin k)) :
    Superop (Fin k → Qubits P.n) (Fin k → Qubits P.n) :=
  piSuperop fun j => if j ∈ trunc then (fun ρ => ρ) else P.ecOp (trail j)

/-- Gottesman intro p.35 (Def. 8, eq. (72)): a gate or wait ExRec is correct for the ideal
decoder. -/
def GateExRecCorrect (κ : LocKind) (lead trail : Fin κ.arity → PauliArrangement)
    (gad : PauliArrangement) (trunc : Finset (Fin κ.arity)) : Prop :=
  piSuperop (fun _ => P.dec) ∘ P.trailOp trail trunc ∘ P.gateOp κ gad ∘ P.leadOp lead =
    conjSuperop κ.idealMatrix ∘ piSuperop (fun _ => P.dec) ∘ P.leadOp lead

end FTProtocol

/-- Gottesman intro p.35 (Def. 8, eqs. (72)–(74)) and p.38 (Def. 10, truncated ExRecs: "removing
the trailing EC step from each diagram"): the ExRec of type `κ` is correct for the fault
arrangement `F`. Gate and wait (72): decoding after the trailing ECs equals the ideal gate after
decoding after the leading ECs. Preparation (73): decoding after the trailing EC gives `|0⟩`.
Measurement (74): the gadget after the leading EC has the outcome weights of decoding after the
leading EC and measuring. -/
def ExRecCorrect (P : FTProtocol) :
    (κ : LocKind) → ExRecFaults κ → Finset (Fin κ.trailCount) → Prop
  | .prep, F, trunc =>
      P.dec ((if (⟨0, by decide⟩ : Fin LocKind.prep.trailCount) ∈ trunc then (fun ρ => ρ)
        else P.ecOp (F.trail ⟨0, by decide⟩)) (P.prepState F.gad)) = pureDensity (ket false)
  | .meas, F, _ =>
      ∀ β : Bool, P.measFunctional F.gad β ∘ P.ecOp (F.lead ⟨0, by decide⟩) =
        fun ρ => P.dec (P.ecOp (F.lead ⟨0, by decide⟩) ρ) β β
  | .had, F, trunc => P.GateExRecCorrect .had F.lead F.trail F.gad trunc
  | .tgate, F, trunc => P.GateExRecCorrect .tgate F.lead F.trail F.gad trunc
  | .cnot, F, trunc => P.GateExRecCorrect .cnot F.lead F.trail F.gad trunc
  | .wait, F, trunc => P.GateExRecCorrect .wait F.lead F.trail F.gad trunc

/-- Gottesman intro p.38 (eq. (83): "`U` ⊗ some operation `V` on the error syndrome"): the
superoperator `ρ ↦ U ρ U†` on the decoded qubits tensored with `V` on the syndrome registers,
acting on `k` (qubit, syndrome) pairs. -/
noncomputable def pairedSuperop {k σ : ℕ} (U : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (V : Superop (Fin k → Fin σ) (Fin k → Fin σ)) :
    Superop (Fin k → Bool × Fin σ) (Fin k → Bool × Fin σ) :=
  fun X =>
    (conjSuperop (Matrix.kronecker U (1 : Matrix (Fin k → Fin σ) (Fin k → Fin σ) ℂ))
      (idTensorSuperop (R := Fin k → Bool) V
        (X.submatrix (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Bool) (fun _ => Fin σ)).symm
          (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Bool) (fun _ => Fin σ)).symm))).submatrix
      (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Bool) (fun _ => Fin σ))
      (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Bool) (fun _ => Fin σ))

namespace FTProtocol

variable (P : FTProtocol)

/-- Gottesman intro p.38 (eq. (83)): a gate or wait ExRec is correct for the *-decoder `W`: for
some quantum operation `V` on the syndrome registers, the *-decoders after the trailing ECs give
the ideal gate on the decoded qubits and `V` on the syndromes, applied after the *-decoders after
the leading ECs. -/
def GateExRecCorrectStar {σ : ℕ} (W : Matrix (Bool × Fin σ) (Qubits P.n) ℂ) (κ : LocKind)
    (lead trail : Fin κ.arity → PauliArrangement) (gad : PauliArrangement)
    (trunc : Finset (Fin κ.arity)) : Prop :=
  ∃ V : Superop (Fin κ.arity → Fin σ) (Fin κ.arity → Fin σ), IsChannel V ∧
    piSuperop (fun _ => conjSuperop W) ∘ P.trailOp trail trunc ∘ P.gateOp κ gad ∘ P.leadOp lead =
      pairedSuperop κ.idealMatrix V ∘ piSuperop (fun _ => conjSuperop W) ∘ P.leadOp lead

end FTProtocol

/-- Gottesman intro p.38 (eq. (83) and "the definitions for preparation and measurement ExRecs are
similar; for the preparation ExRec, the error syndrome is brought in as a separate input on the RHS
of the definition, and for the measurement ExRec, the error syndrome is discarded immediately after
being produced"), with Def. 10's truncation: the ExRec is correct for the *-decoder `W`. -/
def ExRecCorrectStar (P : FTProtocol) {σ : ℕ} (W : Matrix (Bool × Fin σ) (Qubits P.n) ℂ) :
    (κ : LocKind) → ExRecFaults κ → Finset (Fin κ.trailCount) → Prop
  | .prep, F, trunc =>
      ∃ τ : Matrix (Fin σ) (Fin σ) ℂ, IsDensityMatrix τ ∧
        conjSuperop W ((if (⟨0, by decide⟩ : Fin LocKind.prep.trailCount) ∈ trunc then (fun ρ => ρ)
          else P.ecOp (F.trail ⟨0, by decide⟩)) (P.prepState F.gad)) =
          Matrix.kronecker (pureDensity (ket false)) τ
  | .meas, F, _ =>
      ∀ β : Bool, P.measFunctional F.gad β ∘ P.ecOp (F.lead ⟨0, by decide⟩) =
        fun ρ => traceRight (W * P.ecOp (F.lead ⟨0, by decide⟩) ρ * Wᴴ) β β
  | .had, F, trunc => P.GateExRecCorrectStar W .had F.lead F.trail F.gad trunc
  | .tgate, F, trunc => P.GateExRecCorrectStar W .tgate F.lead F.trail F.gad trunc
  | .cnot, F, trunc => P.GateExRecCorrectStar W .cnot F.lead F.trail F.gad trunc
  | .wait, F, trunc => P.GateExRecCorrectStar W .wait F.lead F.trail F.gad trunc

/-! ### Sanity tests -/

example {k n A : ℕ} (z : Qubits (k * (n + A))) (i : Fin k) (j : Fin n) :
    (blockLayout k n A z).1 i j = z (finProdFinEquiv (i, Fin.castAdd A j)) := rfl

example {k n A : ℕ} (z : Qubits (k * (n + A))) (i : Fin k) (a : Fin A) :
    (blockLayout k n A z).2 i a = z (finProdFinEquiv (i, Fin.natAdd n a)) := rfl

example {n A : ℕ} (z : Qubits (n + A)) (j : Fin n) :
    (singleLayout n A z).1 0 j = z (Fin.castAdd A j) := rfl

example : LocKind.leadCount .prep = 0 ∧ LocKind.trailCount .meas = 0 ∧
    LocKind.leadCount .cnot = 2 := ⟨rfl, rfl, rfl⟩

example {N : ℕ} (G : LocCircuit N) : faultCount G (fun _ => none) = 0 := by
  simp [faultCount, faultyLocs]

example (P : FTProtocol) (κ : LocKind) (F : ExRecFaults κ) (h : ∀ i, F.lead i = fun _ => none)
    (hg : F.gad = fun _ => none) : F.count P Finset.univ = 0 := by
  simp [ExRecFaults.count, h, hg, faultCount, faultyLocs]

end QAlgorithms
