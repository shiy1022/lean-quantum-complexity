import QAlgorithms.Defs.Fourier

/-!
# de Wolf, Chapter 5: Shor's Factoring Algorithm

R. de Wolf, *Quantum Computing: Lecture Notes*, §5.2 (reduction from factoring to period-finding,
PDF pp.49–50) and §5.3 (Shor's period-finding algorithm, PDF pp.51–53).

The order ("period") of `x` modulo `N` is `orderOf (x : ZMod N)`: the least `r > 0` with
`x ^ r ≡ 1 (mod N)` (p.50), which exists when `x` is coprime to `N`.
-/

namespace QAlgorithms.DeWolf

/-- de Wolf §5.2, PDF pp.49–50 (unnumbered): the number-theoretic core of the reduction from
factoring to period-finding. Let `N > 1` be odd and not a prime power (in particular composite;
p.49), and pick `x ∈ {2, …, N − 1}`. Then:

1. if `x` is not coprime to `N`, then `gcd(x, N)` is a nontrivial factor of `N`;
2. if `x` is coprime to `N`, its period `r` (the least `0 < r ≤ N` with `x^r ≡ 1 mod N`) is the
   period of `f(a) = x^a mod N`, i.e. `f(a) = f(b)` iff `a ≡ b (mod r)`;
3. if moreover `r` is even and `N` divides neither `x^{r/2} + 1` nor `x^{r/2} − 1`, then both
   `gcd(x^{r/2} + 1, N)` and `gcd(x^{r/2} − 1, N)` are nontrivial factors of `N`;
4. for `x` uniform in `{2, …, N − 1}` and conditioned on `x` coprime to `N`, the event
   "`r` even, `N ∤ x^{r/2} + 1`, `N ∤ x^{r/2} − 1`" has probability `≥ 1/2`
   (cited to Nielsen–Chuang Thm A4.13), stated as `2 · #good ≥ #coprime`. -/
theorem factoring_reduces_to_periodFinding (N : ℕ) (hN : 1 < N) (hodd : Odd N)
    (hpp : ¬ IsPrimePow N) :
    (∀ x ∈ Finset.Icc 2 (N - 1), ¬ Nat.Coprime x N → 1 < Nat.gcd x N ∧ Nat.gcd x N < N) ∧
    (∀ x : ℕ, Nat.Coprime x N →
      0 < orderOf (x : ZMod N) ∧ orderOf (x : ZMod N) ≤ N ∧
        HasPeriod (fun a => x ^ a % N) (orderOf (x : ZMod N))) ∧
    (∀ x ∈ Finset.Icc 2 (N - 1), Nat.Coprime x N → Even (orderOf (x : ZMod N)) →
      ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) + 1 → ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) - 1 →
        (1 < Nat.gcd (x ^ (orderOf (x : ZMod N) / 2) + 1) N ∧
          Nat.gcd (x ^ (orderOf (x : ZMod N) / 2) + 1) N < N) ∧
        (1 < Nat.gcd (x ^ (orderOf (x : ZMod N) / 2) - 1) N ∧
          Nat.gcd (x ^ (orderOf (x : ZMod N) / 2) - 1) N < N)) ∧
    ((Finset.Icc 2 (N - 1)).filter fun x => Nat.Coprime x N).card ≤
      2 * ((Finset.Icc 2 (N - 1)).filter fun x => Nat.Coprime x N ∧
        Even (orderOf (x : ZMod N)) ∧ ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) + 1 ∧
        ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) - 1).card := by
  sorry

open Classical in
/-- de Wolf §5.3, PDF pp.50–53 (unnumbered): Shor's period-finding algorithm. Let
`f : ℕ → {0, …, N − 1}` have period `r ∈ {1, …, N}` (`f(a) = f(b)` iff `a ≡ b mod r`, p.50), let
`q = 2^ℓ` with `N² < q ≤ 2N²` (`ℓ = shorEll N`), and run the circuit of Figure 5.1 once:
`F_q` on the first (`ℓ`-qubit) register of `|0^ℓ⟩|0^n⟩` (`n = ⌈log N⌉`), one application of
`O_f : |a⟩|z⟩ ↦ |a⟩|z ⊕ f(a)⟩`, `F_q` on the first register, and measure the first register,
obtaining `b`. Then:

1. there are constants `C > 0` and `N₀`, independent of `N`, `r`, `f`, such that for all `N ≥ N₀`
   the outcome `b` satisfies `|b/q − c/r| ≤ 1/(2q)` for some `c ∈ {0, …, r − 1}` coprime to `r`
   with probability at least `C / log log N` (so `O(log log N)` expected repetitions suffice);
2. whenever `|b/q − c/r| ≤ 1/(2q)` with `c` coprime to `r ≤ N`, the fraction `c/r` is the only
   fraction with denominator `≤ N` within `1/(2q)` of `b/q`, and its lowest-terms denominator
   is `r`. -/
theorem shor_periodFinding :
    (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℕ, 1 ≤ r → r ≤ N →
      ∀ f : ℕ → ℕ, (∀ a, f a < N) → HasPeriod f r →
        C / Real.log (Real.log N) ≤ probEvent (shorRunState N f) fun z =>
          ∃ c : ℕ, c < r ∧ Nat.Coprime c r ∧
            |(bitsToNat z.1 : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r| ≤
              1 / (2 * (2 : ℝ) ^ shorEll N)) ∧
    (∀ N r c b : ℕ, 1 ≤ r → r ≤ N → c < r → Nat.Coprime c r →
      |(b : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r| ≤ 1 / (2 * (2 : ℝ) ^ shorEll N) →
        ((c : ℚ) / r).den = r ∧
        ∀ (p : ℤ) (s : ℕ), 1 ≤ s → s ≤ N →
          |(b : ℝ) / (2 : ℝ) ^ shorEll N - (p : ℝ) / s| ≤ 1 / (2 * (2 : ℝ) ^ shorEll N) →
            (p : ℝ) / s = (c : ℝ) / r) := by
  sorry

end QAlgorithms.DeWolf
