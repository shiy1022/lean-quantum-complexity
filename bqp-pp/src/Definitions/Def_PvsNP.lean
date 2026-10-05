import Mathlib

/-!
S. Cook, *The P versus NP problem*, Clay Mathematics Institute Millennium Prize Problem
description (2000), pp. 1–5 and p. 9.

The objects of Cook's Section 1: the classes `P` (p. 2) and `NP` (p. 2, via polynomial-time
checking relations), polynomial-time (Karp) reducibility `≤ₚ` (Definition 3), `NP`-completeness
(Definition 4), the exponential-time class `E` (p. 9), and the languages Satisfiability and 3-SAT
(p. 5) as sets of binary strings coding CNF formulas.

Conventions.  The alphabet is `Σ = {0,1} = Bool` throughout (Cook, p. 2: the problem is
independent of the alphabet size, provided `|Σ| ≥ 2`); a string is a `List Bool` and a language
is a `Language Bool = Set (List Bool)`.  The machine model is Mathlib's bundled multi-stack
machine `Turing.FinTM2` (finitely many stacks, finitely many program labels, finite internal
memory, finite input alphabet), and "computable in polynomial time" is Mathlib's
`Turing.TM2ComputableInPolyTime`: the machine, started with the input on its input stack, halts
within `p(|input|)` steps (`p` a polynomial with natural coefficients) with the required output
on its output stack, every other stack empty and the internal memory reset.  Each step executes
one program statement, which is a fixed finite tree of stack pushes/pops/peeks, so this step
count is within a constant factor of the number of elementary operations.  Multi-stack machines
and Turing machines simulate each other with polynomial overhead, so `P`, `NP`, `≤ₚ` and
`NP`-completeness below are the standard classes (Cook, p. 1: "`P` is a robust class and has
equivalent definitions over a large class of computer models").
-/

namespace PvsNP

open Computability Turing

/-- A binary string `w ∈ Σ*` with `Σ = {0,1}`. -/
abbrev Str := List Bool

/-! ### Polynomial-time computation -/

/-- Cook, p. 1–2: a decision procedure `χ : Σ* → {0,1}` runs in polynomial time.  There is a
bundled multi-stack machine and a polynomial `p` (natural coefficients) such that, for every
string `w`, the machine started with `w` on its input stack halts within `p(|w|)` steps with the
single symbol `χ w` on its output stack.  `χ w = true` means "accept". -/
def PolyTimeDecider (χ : Str → Bool) : Prop :=
  Nonempty (TM2ComputableInPolyTime (id : Str → Str) encodeBool χ)

/-- Cook, p. 2: the class `P` of languages `L ⊆ Σ*` accepted by some Turing machine that runs in
polynomial time, i.e. `L = {w | χ w = true}` for some polynomial-time decision procedure `χ`. -/
def P : Set (Language Bool) :=
  {L | ∃ χ : Str → Bool, PolyTimeDecider χ ∧ ∀ w, w ∈ L ↔ χ w = true}

/-- Cook, p. 2: the string `w#y` coding a pair `(w, y)` of strings.  The symbols of `w` are tagged
with `Sum.inl` and those of `y` with `Sum.inr`, so the input alphabet is `Bool ⊕ Bool` (four
symbols) and the boundary between `w` and `y` is visible to the machine, exactly as with Cook's
separator symbol `#`.  Its length is `|w| + |y|`. -/
def encodePair (x : Str × Str) : List (Bool ⊕ Bool) :=
  x.1.map Sum.inl ++ x.2.map Sum.inr

/-- Cook, p. 2: a checking relation `R ⊆ Σ* × Σ*`, given as its indicator `R : Σ* × Σ* → {0,1}`,
is polynomial-time: the language `L_R = {w#y | R(w,y)}` is decided by a multi-stack machine
within `p(|w| + |y|)` steps for some polynomial `p`. -/
def PolyTimeChecker (R : Str × Str → Bool) : Prop :=
  Nonempty (TM2ComputableInPolyTime encodePair encodeBool R)

/-- Cook, p. 2: the class `NP`.  A language `L` is in `NP` iff there are `k ∈ ℕ` and a
polynomial-time checking relation `R` such that for all `w ∈ Σ*`,
`w ∈ L ⟺ ∃ y (|y| ≤ |w|^k and R(w,y))`. -/
def NP : Set (Language Bool) :=
  {L | ∃ (R : Str × Str → Bool) (k : ℕ), PolyTimeChecker R ∧
        ∀ w, w ∈ L ↔ ∃ y : Str, y.length ≤ w.length ^ k ∧ R (w, y) = true}

/-- Cook, Definition 3: a function `f : Σ* → Σ*` is polynomial-time computable: a multi-stack
machine started with `w` on its input stack halts within `p(|w|)` steps with `f w` on its output
stack, for some polynomial `p`. -/
def PolyTimeComputable (f : Str → Str) : Prop :=
  Nonempty (TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) f)

/-- Cook, Definition 3: `L₁ ≤ₚ L₂` (`L₁` is p-reducible to `L₂`) iff there is a polynomial-time
computable `f : Σ* → Σ*` with `x ∈ L₁ ⟺ f(x) ∈ L₂` for all `x ∈ Σ*`. -/
def PReducible (L₁ L₂ : Language Bool) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ x, x ∈ L₁ ↔ f x ∈ L₂

/-- Cook, Definition 4: `L` is `NP`-complete iff `L ∈ NP` and `L' ≤ₚ L` for every `L' ∈ NP`. -/
def NPComplete (L : Language Bool) : Prop :=
  L ∈ NP ∧ ∀ L' ∈ NP, PReducible L' L

/-- Cook, p. 9: the class `E` of languages recognizable in exponential time, `L = L(M)` for a
Turing machine `M` with worst-case running time `T_M(n) = O(2^{cn})` for some `c`.  Here the
machine is a multi-stack machine with a time function `t : ℕ → ℕ` (a bound on the number of steps
on inputs of length `n`) satisfying `t n ≤ C · 2^{c·n}` for all `n`, for some constants `c, C`. -/
def E : Set (Language Bool) :=
  {L | ∃ χ : Str → Bool,
        (∃ M : TM2ComputableInTime (id : Str → Str) encodeBool χ,
          ∃ c C : ℕ, ∀ n, M.time n ≤ C * 2 ^ (c * n)) ∧
        ∀ w, w ∈ L ↔ χ w = true}

/-! ### Satisfiability -/

/-- A propositional literal `(s, i)`: the variable `xᵢ` if `s = true`, its negation `¬xᵢ` if
`s = false`. -/
abbrev Literal := Bool × ℕ

/-- A clause: a disjunction of literals, given as a list. -/
abbrev Clause := List Literal

/-- A formula in conjunctive normal form (CNF): a conjunction of clauses, given as a list. -/
abbrev CNF := List Clause

/-- The truth value of a literal under a truth assignment `τ : ℕ → Bool` to the variables. -/
def evalLiteral (τ : ℕ → Bool) (l : Literal) : Bool :=
  if l.1 then τ l.2 else !τ l.2

/-- A clause is true under `τ` iff at least one of its literals is (the empty clause is false). -/
def evalClause (τ : ℕ → Bool) (c : Clause) : Bool :=
  c.any (evalLiteral τ)

/-- A CNF formula is true under `τ` iff all of its clauses are (the empty formula is true). -/
def evalCNF (τ : ℕ → Bool) (F : CNF) : Bool :=
  F.all (evalClause τ)

/-- Cook, p. 5: a formula `F` is satisfiable iff some truth assignment makes it true. -/
def Satisfiable (F : CNF) : Prop :=
  ∃ τ : ℕ → Bool, evalCNF τ F = true

/-- Binary coding of a literal `(s, i)`: the sign bit followed by the binary digits of `i`
(least significant first, no leading zeros), each written as the two-bit block `0b`, followed by
the end-of-literal marker `10`.  Its length is `2 · (⌈log₂(i+1)⌉ + 2)`. -/
def encodeLiteral (l : Literal) : Str :=
  ((l.1 :: Nat.bits l.2).flatMap fun b => [false, b]) ++ [true, false]

/-- Binary coding of a clause: the codes of its literals in order, followed by the end-of-clause
marker `11`. -/
def encodeClause (c : Clause) : Str :=
  c.flatMap encodeLiteral ++ [true, true]

/-- Cook, p. 5, "standard coding methods": the binary code of a CNF formula is the concatenation
of the codes of its clauses.  Every symbol is a two-bit block (`0b` = data bit `b`, `10` = end of
literal, `11` = end of clause), so the code can be parsed unambiguously from left to right, and
its length is linear in the number of literals times the number of bits of the variable indices.
The empty formula is coded by the empty string. -/
def encodeCNF (F : CNF) : Str :=
  F.flatMap encodeClause

/-- Cook, p. 5: Satisfiability, as a language over `{0,1}`: the set of strings coding a
satisfiable CNF formula.  Strings that code no formula are not in `SAT`. -/
def SAT : Language Bool :=
  {w | ∃ F : CNF, encodeCNF F = w ∧ Satisfiable F}

/-- Cook, p. 5: 3-SAT, the set of strings coding a satisfiable CNF formula in which every clause
has exactly three literals. -/
def ThreeSAT : Language Bool :=
  {w | ∃ F : CNF, encodeCNF F = w ∧ (∀ c ∈ F, c.length = 3) ∧ Satisfiable F}

end PvsNP
