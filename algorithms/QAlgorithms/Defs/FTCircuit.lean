import QAlgorithms.Defs.FaultTolerance

/-!
# The fault-tolerant circuit C′, its ExRecs, good and bad locations, the circuit C̃, local
stochastic error models, concatenation (shared definition layer)

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N" (PDF pages), §§5.1–5.2, Defs. 6, 7,
10, 12, Thms 8–10.

Layout of `C′ = ftCircuit P C` (Def. 6). Qubit `q` of `C` owns the block of physical qubits
`finProdFinEquiv (q, j)`, `j < n + A`. Time step `s` of `C` becomes `period = D + D_ec` time steps
of `C′`: a gadget phase of `D` steps (`D` the gadget depth; every location of step `s` replaced by
its gadget on the blocks of its qubits, in parallel) followed by an EC phase of `D_ec` steps (the
EC gadget on the block of every qubit whose step-`s` location is not a measurement, in parallel:
the EC between consecutive locations). Within a `C′` step the gadget instances appear in the order
of the `C` locations (resp. of the qubits). A classically controlled gate location of `C` (these
arise in `C^{(k)}`, `k ≥ 1`) becomes its gadget with every location's condition conjoined with the
location's condition on the decoded logical outcomes.
-/

namespace QAlgorithms

open scoped Matrix

namespace FTProtocol

variable (P : FTProtocol)

/-- Gottesman intro p.33 (Def. 6: "C can be divided up into time steps"): all location gadgets have
the same number of time steps, so that the gadgets of one time step of `C` run in parallel without
padding. -/
def HasUniformDepth : Prop :=
  ∀ κ : LocKind, (P.gadget κ).steps.length = (P.gadget .prep).steps.length

/-- The number of time steps of the gadget phase of `C′`: the largest gadget depth. -/
def gadgetDepth : ℕ :=
  [LocKind.prep, .had, .tgate, .cnot, .meas, .wait].foldr (fun κ acc => max (P.gadget κ).steps.length acc) 0

/-- The number of time steps of `C′` per time step of `C`. -/
def period : ℕ :=
  P.gadgetDepth + P.ec.steps.length

end FTProtocol

/-- The gadget instances of `C′`: the gadget of the `C` location `ℓ`, or the EC gadget after time
step `s` of `C` on the block of qubit `q`. -/
inductive FTInstance (N : ℕ) where
  | gadget (ℓ : ℕ × ℕ)
  | ec (s : ℕ) (q : Fin N)
  deriving DecidableEq

/-- The physical qubits of the blocks of the qubits `w` of a `C` location: block `i`, position `p`
of the gadget is block `w i`, position `p` of `C′`. -/
def blockEmb (n A : ℕ) {k N : ℕ} (w : Fin k ↪ Fin N) : Fin (k * (n + A)) ↪ Fin (N * (n + A)) :=
  ⟨fun x => finProdFinEquiv (w (finProdFinEquiv.symm x).1, (finProdFinEquiv.symm x).2), by
    intro x y h
    have h' := Prod.ext_iff.1 (finProdFinEquiv.injective h)
    exact finProdFinEquiv.symm.injective (Prod.ext (w.injective h'.1) h'.2)⟩

/-- The physical qubits of the block of qubit `q`. -/
def ecEmb (n A : ℕ) {N : ℕ} (q : Fin N) : Fin (n + A) ↪ Fin (N * (n + A)) :=
  ⟨fun p => finProdFinEquiv (q, p), fun _ _ h => (Prod.ext_iff.1 (finProdFinEquiv.injective h)).2⟩

variable {N : ℕ}

/-- The position in its `C′` step at which the gadget of the `C` location `(s, j)` starts, at local
step `d` of the gadget. -/
def gadgetOffset (P : FTProtocol) (C : LocCircuit N) (s j d : ℕ) : ℕ :=
  (((C.steps.getD s []).take j).map fun l => ((P.gadget l.kind).steps.getD d []).length).sum

/-- The id in `C′` of the location with local id `lid` of the gadget of the `C` location
`(s, j)`. -/
def gadgetGlobalId (P : FTProtocol) (C : LocCircuit N) (s j : ℕ) (lid : ℕ × ℕ) : ℕ × ℕ :=
  (s * P.period + lid.1, gadgetOffset P C s j lid.1 + lid.2)

/-- The qubits of `C` receiving an EC gadget after time step `s`: those whose step-`s` location is
not a measurement (the EC between consecutive locations, Def. 6). -/
def ecBlocks (C : LocCircuit N) (s : ℕ) : List (Fin N) :=
  (List.finRange N).filter fun q =>
    (C.steps.getD s []).any fun l => decide (l.kind ≠ .meas) && decide (q ∈ l.qubits)

/-- The id in `C′` of the location with local id `lid` of the EC gadget after step `s` on the
`idx`-th block of `ecBlocks C s`. -/
def ecGlobalId (P : FTProtocol) (s idx : ℕ) (lid : ℕ × ℕ) : ℕ × ℕ :=
  (s * P.period + P.gadgetDepth + lid.1, idx * (P.ec.steps.getD lid.1 []).length + lid.2)

/-- The decoded logical outcomes of the measurement locations of `C`, read from the outcomes `O`
of `C′` (`none` until every outcome of the measurement gadget is available). -/
def decodedOutcomes (P : FTProtocol) (C : LocCircuit N) (O : ℕ × ℕ → Option Bool) :
    ℕ × ℕ → Option Bool :=
  fun cid => match C.locAt cid with
    | some l =>
        if l.kind = .meas then
          if ((P.gadget .meas).measIds.map fun lid => O (gadgetGlobalId P C cid.1 cid.2 lid)).all
              Option.isSome then
            some (P.measDecode ((P.gadget .meas).measIds.map fun lid =>
              (O (gadgetGlobalId P C cid.1 cid.2 lid)).getD false))
          else none
        else none
    | none => none

/-- Time step `d` of the gadget phase for time step `s` of `C`, its locations tagged with their
gadget instance. -/
def gadgetPhaseStep (P : FTProtocol) (C : LocCircuit N) (s d : ℕ) :
    List (Loc (N * (P.n + P.A)) × FTInstance N) :=
  (C.steps.getD s []).zipIdx.flatMap fun p =>
    ((P.gadget p.1.kind).steps.getD d []).map fun g =>
      (⟨g.kind, g.wires.trans (blockEmb P.n P.A p.1.wires),
        fun O => g.cond (fun lid => O (gadgetGlobalId P C s p.2 lid)) &&
          (if p.1.kind.IsGate then p.1.cond (decodedOutcomes P C O) else true)⟩,
       FTInstance.gadget (s, p.2))

/-- Time step `e` of the EC phase after time step `s` of `C`, its locations tagged with their
gadget instance. -/
def ecPhaseStep (P : FTProtocol) (C : LocCircuit N) (s e : ℕ) :
    List (Loc (N * (P.n + P.A)) × FTInstance N) :=
  (ecBlocks C s).zipIdx.flatMap fun p =>
    (P.ec.steps.getD e []).map fun g =>
      (⟨g.kind, g.wires.trans (ecEmb P.n P.A p.1),
        fun O => g.cond (fun lid => O (ecGlobalId P s p.2 lid))⟩,
       FTInstance.ec s p.1)

/-- The time steps of `C′`, every location tagged with its gadget instance. -/
def ftTaggedSteps (P : FTProtocol) (C : LocCircuit N) :
    List (List (Loc (N * (P.n + P.A)) × FTInstance N)) :=
  (List.range C.steps.length).flatMap fun s =>
    (List.range P.gadgetDepth).map (gadgetPhaseStep P C s) ++
      (List.range P.ec.steps.length).map (ecPhaseStep P C s)

/-- Gottesman intro p.33 (Def. 6: "a quantum circuit `C′` constructed by replacing each location
`C_i` with a fault-tolerant gadget for `C_i`, and adding fault-tolerant error correction gadgets
between any pair of consecutive locations") and p.34 (Fig. 7): the fault-tolerant circuit for
`C`. -/
def ftCircuit (P : FTProtocol) (C : LocCircuit N) : LocCircuit (N * (P.n + P.A)) :=
  ⟨(ftTaggedSteps P C).map fun st => st.map Prod.fst⟩

/-- The gadget instance the location `id` of `C′` belongs to. -/
def ftOwner (P : FTProtocol) (C : LocCircuit N) (id : ℕ × ℕ) : Option (FTInstance N) :=
  ((ftTaggedSteps P C).getD id.1 [])[id.2]?.map Prod.snd

/-- Gottesman intro p.19 ("the final fault-tolerant measurement gadgets will produce classical
information which should … give the same outcome as the original circuit") and p.17 (classical
computation is perfect): the measurement record of `C` decoded from that of `C′`: for each
measurement location of `C` (in `C`'s record order), `measDecode` of the outcomes of its
measurement gadget; EC and other outcomes are discarded. -/
def ftDecode (P : FTProtocol) (C : LocCircuit N) (r : List Bool) : List Bool :=
  C.measIds.map fun cid => P.measDecode ((P.gadget .meas).measIds.map fun lid =>
    ((ftCircuit P C).outcomeAt r (gadgetGlobalId P C cid.1 cid.2 lid)).getD false)

/-- Gottesman intro p.34 (Def. 7) and p.38 (Def. 10): the locations of `C′` in the ExRec of the `C`
location `ℓ`: its gadget, the leading ECs (the EC after the previous step on each of its qubits,
unless `ℓ` is a preparation) and the trailing ECs (the EC after its step on each of its qubits not
in `trunc`, unless `ℓ` is a measurement). `trunc = ∅` is the full ExRec. -/
noncomputable def exRecLocs (P : FTProtocol) (C : LocCircuit N) (ℓ : ℕ × ℕ) (trunc : Finset (Fin N)) :
    Finset (ℕ × ℕ) :=
  open Classical in
  match C.locAt ℓ with
  | none => ∅
  | some l => (ftCircuit P C).locs.filter fun id =>
      match ftOwner P C id with
      | some (.gadget ℓ') => ℓ' = ℓ
      | some (.ec s q) => q ∈ l.qubits ∧
          ((l.kind ≠ .prep ∧ s + 1 = ℓ.1) ∨ (l.kind ≠ .meas ∧ s = ℓ.1 ∧ q ∉ trunc))
      | none => False

/-- Gottesman intro p.38 (Def. 10): the qubits of the `C` location `ℓ` whose trailing EC is removed
because it is the leading EC of a bad location (of the next time step) in `B`. -/
noncomputable def truncOf (C : LocCircuit N) (B : Finset (ℕ × ℕ)) (ℓ : ℕ × ℕ) : Finset (Fin N) :=
  open Classical in
  match C.locAt ℓ with
  | none => ∅
  | some l => l.qubits.filter fun q =>
      ∃ ℓ' ∈ B, ℓ'.1 = ℓ.1 + 1 ∧ ∃ l', C.locAt ℓ' = some l' ∧ q ∈ l'.qubits

/-- The bad locations among the last `k` time steps of `C`, for the set `S` of faulty locations of
`C′` (Def. 10's recursion, from the end of the circuit backwards). -/
noncomputable def badAbove (P : FTProtocol) (C : LocCircuit N) (S : Finset (ℕ × ℕ)) :
    ℕ → Finset (ℕ × ℕ)
  | 0 => ∅
  | k + 1 =>
      open Classical in
      badAbove P C S k ∪
        ((Finset.range (C.steps.getD (C.steps.length - (k + 1)) []).length).image
          fun j => (C.steps.length - (k + 1), j)).filter fun ℓ =>
            P.t < (S ∩ exRecLocs P C ℓ (truncOf C (badAbove P C S k) ℓ)).card

/-- Gottesman intro p.38 (Def. 10): the set of locations of `C` whose ExRec (full or truncated) is
bad, i.e. contains more than `t` of the faulty locations `S` of `C′`; an ExRec is truncated on the
qubits whose trailing EC is a leading EC of a bad ExRec, determined from the end of the circuit
backwards. -/
noncomputable def badAssignment (P : FTProtocol) (C : LocCircuit N) (S : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  badAbove P C S C.steps.length

/-- The superoperator `Ψ` on `k` registers (of type `α`) lifted to `N` registers along `w`, the
identity on the others. -/
noncomputable def liftReg {α : Type*} {k : ℕ} (w : Fin k ↪ Fin N)
    (Ψ : Superop (Fin k → α) (Fin k → α)) : Superop (Fin N → α) (Fin N → α) :=
  fun X =>
    (liftSuperop (E := Unit) w
      (fun Y => (Ψ (Y.submatrix (fun x => (x, ())) (fun x => (x, ())))).submatrix Prod.fst Prod.fst)
      (X.submatrix Prod.fst Prod.fst)).submatrix (fun x => (x, ())) (fun x => (x, ()))

/-- A superoperator `Ψ` on the (data qubit, syndrome register) pairs of `k` qubits, lifted to the
qubits of `C` with one syndrome register per qubit as environment. -/
noncomputable def pairLift {σ k : ℕ} (w : Fin k ↪ Fin N)
    (Ψ : Superop (Fin k → Bool × Fin σ) (Fin k → Bool × Fin σ)) :
    Superop (Qubits N × (Fin N → Fin σ)) (Qubits N × (Fin N → Fin σ)) :=
  fun X =>
    (liftReg w Ψ (X.submatrix (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Bool) (fun _ => Fin σ))
      (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Bool) (fun _ => Fin σ)))).submatrix
      (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Bool) (fun _ => Fin σ)).symm
      (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Bool) (fun _ => Fin σ)).symm

/-- Gottesman intro pp.37–39 (eqs. (82), (83), Thm 8): `err` is an error assignment of a circuit
`C̃` for `C` with bad set `B` and syndrome registers `Fin σ` (one per qubit of `C`, the environment;
"`C̃` uses ancilla registers to control the types of `U′` errors"): no error off the locations; at
every location `ℓ`, after its ideal operation, a quantum operation `Ψ` on the qubits of `ℓ` and
their syndrome registers; if `ℓ ∉ B` ("include `C_i` unchanged"), `Ψ` is the identity on the qubits
tensored with a quantum operation `V` on the syndrome registers (eq. (83)); if `ℓ ∈ B`, `Ψ` is
arbitrary (the erroneous `U′` of (82), controlled by the syndrome). -/
def IsTildeErrors (C : LocCircuit N) (B : Finset (ℕ × ℕ)) (σ : ℕ)
    (err : ErrAssign N (Fin N → Fin σ)) : Prop :=
  ∀ ℓ : ℕ × ℕ, (C.locAt ℓ = none → err ℓ = none) ∧
    ∀ l : Loc N, C.locAt ℓ = some l →
      ∃ Ψ : Superop (Fin l.kind.arity → Bool × Fin σ) (Fin l.kind.arity → Bool × Fin σ),
        IsChannel Ψ ∧
        (ℓ ∉ B → ∃ V : Superop (Fin l.kind.arity → Fin σ) (Fin l.kind.arity → Fin σ),
          IsChannel V ∧ Ψ = pairedSuperop 1 V) ∧
        err ℓ = some (pairLift l.wires Ψ)

/-- Gottesman intro p.40 (Def. 12): an error model on a circuit with `N` qubits: an environment
register `Fin e` in the state `σ0`, the probability `prob S` of faults at precisely the set `S` of
locations, and the errors `err S ℓ` chosen (by an adversary) when the faulty set is `S`; they act
at the locations of `S` in chronological order and may be entangled through the environment. -/
structure LocalStochasticModel (N : ℕ) where
  e : ℕ
  σ0 : Matrix (Fin e) (Fin e) ℂ
  prob : Finset (ℕ × ℕ) → ℝ
  err : Finset (ℕ × ℕ) → ℕ × ℕ → Superop (Qubits N × Fin e) (Qubits N × Fin e)

/-- Gottesman intro p.40 (Def. 12): the output distribution of `C` under the error model: the
mixture over the faulty set `S` of the output distributions with the errors at `S`. -/
noncomputable def noisyOutDist (C : LocCircuit N) (M : LocalStochasticModel N) :
    (Fin C.measCount → Bool) → ℝ :=
  fun r => ∑ S ∈ C.locs.powerset,
    M.prob S * C.outDist (fun ℓ => if ℓ ∈ S then some (M.err S ℓ) else none) M.σ0 r

/-- Gottesman intro p.40 (Def. 12): `M` is a local stochastic error model on `C` with error bounds
`bound`: the environment state is a density matrix; `prob` is a probability distribution on the
sets of locations of `C`; each error at a faulty location is any quantum operation on that
location's qubits and the environment; and for every set `R` of locations the probability of
faults on every location of `R` (and possibly elsewhere) is at most `Π_{i ∈ R} p_i`. The side
condition `p_i < 1` of Def. 12 is a separate hypothesis of the statements (Thm 9's induced bounds
(84) may exceed 1). -/
def IsLocalStochastic (C : LocCircuit N) (M : LocalStochasticModel N) (bound : ℕ × ℕ → ℝ) : Prop :=
  IsDensityMatrix M.σ0 ∧ (∀ S, 0 ≤ M.prob S) ∧ (∀ S, ¬ S ⊆ C.locs → M.prob S = 0) ∧
    ∑ S ∈ C.locs.powerset, M.prob S = 1 ∧
    (∀ (S : Finset (ℕ × ℕ)) (ℓ : ℕ × ℕ) (l : Loc N), ℓ ∈ S → C.locAt ℓ = some l →
      IsLocError l.wires (M.err S ℓ)) ∧
    ∀ R ⊆ C.locs, ∑ S ∈ C.locs.powerset.filter (fun S => R ⊆ S), M.prob S ≤ ∏ i ∈ R, bound i

/-- Transport of a circuit along an equality of qubit numbers. -/
def LocCircuit.castN {N N' : ℕ} (h : N = N') (C : LocCircuit N) : LocCircuit N' :=
  h ▸ C

/-- Gottesman intro p.36 (§5.2: "a sequence of circuits `C^{(k)}`, `k = 1, …, L`, where each `C^{(k)}`
is a fault-tolerant simulation of `C^{(k−1)}`, with `C^{(0)} = C`") and p.42 (proof of Thm 10): the
`L`-level concatenated fault-tolerant circuit for `C`, on `N (n + A)^L` qubits. -/
def concatCircuit (P : FTProtocol) : (L : ℕ) → LocCircuit N → LocCircuit (N * (P.n + P.A) ^ L)
  | 0, C => C.castN (by simp)
  | L + 1, C => (ftCircuit P (concatCircuit P L C)).castN (by rw [pow_succ, mul_assoc])

/-- The classical decoding of the record of `C^{(L)}` to the record of `C`, level by level. -/
def concatDecode (P : FTProtocol) : (L : ℕ) → LocCircuit N → List Bool → List Bool
  | 0, _ => id
  | L + 1, C => fun r => concatDecode P L C (ftDecode P (concatCircuit P L C) r)

/-! ### Sanity tests -/

example (P : FTProtocol) : ftCircuit P (⟨[]⟩ : LocCircuit N) = ⟨[]⟩ := by
  simp [ftCircuit, ftTaggedSteps]

example (P : FTProtocol) (S : Finset (ℕ × ℕ)) : badAssignment P (⟨[]⟩ : LocCircuit N) S = ∅ := rfl

example (P : FTProtocol) (C : LocCircuit N) : concatDecode P 0 C = id := rfl

example (P : FTProtocol) (r : List Bool) : ftDecode P (⟨[]⟩ : LocCircuit N) r = [] := rfl

example (n A : ℕ) (q : Fin N) (p : Fin (n + A)) :
    blockEmb n A (Stabilizer.wire1 q) (finProdFinEquiv (0, p)) = finProdFinEquiv (q, p) := by
  show finProdFinEquiv (_, _) = _
  rw [Equiv.symm_apply_apply]
  rfl

example (C : LocCircuit N) (M : LocalStochasticModel N) (h : C.locs = ∅) (r : Fin C.measCount → Bool) :
    noisyOutDist C M r = M.prob ∅ * C.outDist (fun _ => none) M.σ0 r := by
  simp [noisyOutDist, h]

end QAlgorithms
