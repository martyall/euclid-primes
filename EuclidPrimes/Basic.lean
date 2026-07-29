/-
Copyright (c) 2026 Martin Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Allen
-/
import Mathlib

/-!
# Definitions and elementary divisibility

Project-local versions of primality, irreducibility and the gcd relation, plus
the elementary divisibility facts the factorisation induction needs.

Mathlib's `Nat.Prime`, the generic `Irreducible`/`Prime` classes and `Nat.gcd`
are deliberately not used: reproducing Euclid's development from first
principles is the point of the project.

Both `IsPrime` and `IsIrreducible` carry `1 < p` as their first conjunct. The
informal source omits it, but without it `0` and `1` satisfy the remaining
clause and the factorisation theorem becomes false.
-/

namespace EuclidPrimes

/-- A natural number `p` is *prime* when `1 < p` and `p` divides a factor of
every product it divides. -/
def IsPrime (p : ℕ) : Prop :=
  1 < p ∧ ∀ a b : ℕ, p ∣ a * b → p ∣ a ∨ p ∣ b

/-- A natural number `p` is *irreducible* when `1 < p` and every factorisation
of `p` has `p` itself as one of its factors. -/
def IsIrreducible (p : ℕ) : Prop :=
  1 < p ∧ ∀ a b : ℕ, p = a * b → p = a ∨ p = b

/-- `d` is *a* greatest common divisor of `a` and `b`, stated by its universal
property. This is a relation, not a function: existence and uniqueness of such
a `d` are proved later, from Bézout. -/
def IsGcd (a b d : ℕ) : Prop :=
  d ∣ a ∧ d ∣ b ∧ ∀ c : ℕ, c ∣ a → c ∣ b → c ∣ d

/-- A divisor of `b` that differs from `b` is strictly smaller than `b`.

The source argues via `b - a = a * (c - 1) > 0`; over `ℕ` that subtraction
truncates, so the argument here is multiplicative instead. -/
theorem dvd_lt_of_ne {a b : ℕ} (ha : 1 < a) (hb : 1 < b) (hne : a ≠ b)
    (hdvd : a ∣ b) : a < b := by
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hc
    omega
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [Nat.mul_one] at hc
    omega
  have hc2 : 2 ≤ c := by omega
  calc a < a + a := by omega
    _ = a * 2 := by ring
    _ ≤ a * c := Nat.mul_le_mul_left a hc2
    _ = b := hc.symm

/-- A factor of a number greater than one is either `1` or greater than `1`. -/
theorem one_lt_factor {n a b : ℕ} (hn : 1 < n) (h : n = a * b) (ha : a ≠ 1) :
    1 < a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Nat.zero_mul] at h
    omega
  omega

/-- A factor of `n` paired with a non-unit cofactor is strictly smaller than
`n`. By symmetry of the hypotheses the same statement gives `b < n`. -/
theorem factor_lt {n a b : ℕ} (hn : 1 < n) (h : n = a * b) (ha : a ≠ 1)
    (hb : b ≠ 1) : a < n := by
  have ha1 : 1 < a := one_lt_factor hn h ha
  have hne : a ≠ n := by
    intro hEq
    apply hb
    have h0 : 0 < a := by omega
    have hmul : a * 1 = a * b := by rw [Nat.mul_one]; exact hEq.trans h
    exact (Nat.eq_of_mul_eq_mul_left h0 hmul).symm
  exact dvd_lt_of_ne ha1 hn hne ⟨b, h⟩

/-! ## Adequacy of the definitions

The three predicates above are project-original, and the source's versions of
them are defective. The four results below pin `IsPrime` down from three sides:
it excludes the units, it holds of `2`, it excludes a composite, and (via
`IsIrreducible`) it agrees with the schoolbook condition on divisors. Each is
proved from the definitions alone, so that the check is not circular; nothing
downstream uses any of them. -/

/-- Units are not prime: `1 < p` is what carries the exclusion of `0` and `1`,
and nothing else does. Blueprint: `lem:not_is_prime_of_le_one`. -/
theorem not_isPrime_of_le_one {p : ℕ} (hp : p ≤ 1) : ¬ IsPrime p := by
  intro h
  -- the first conjunct of `IsPrime` is `1 < p`, contradicting `p ≤ 1`
  have h1 : 1 < p := h.1
  omega

/-- `2` is prime, by a parity argument. Deliberately independent of
irreducibility: a witness that the definition is satisfiable must not rest on
the development it validates. Blueprint: `lem:is_prime_two`. -/
theorem isPrime_two : IsPrime 2 := by
  refine ⟨by omega, ?_⟩
  intro a b hab
  by_cases ha : 2 ∣ a
  · exact Or.inl ha
  · right
    -- divisibility by `2` is the vanishing of the residue mod `2`
    have hab' : a * b % 2 = 0 := by omega
    -- `a % 2 < 2` and `a % 2 ≠ 0` leave `a % 2 = 1`
    have ha1 : a % 2 = 1 := by omega
    -- residues are multiplicative, so `a * b % 2` collapses to `b % 2`
    rw [Nat.mul_mod, ha1, Nat.one_mul] at hab'
    omega

/-- `4` is not prime, so the predicate is not `1 < p` in disguise.
Blueprint: `lem:not_is_prime_four`. -/
theorem not_isPrime_four : ¬ IsPrime 4 := by
  intro h
  -- `4 = 2 * 2`, so `4` divides the product `2 * 2`
  have hdvd : (4 : ℕ) ∣ 2 * 2 := by norm_num
  -- the divisibility clause at `a = b = 2` gives `4 ∣ 2` on either branch
  have h2 : (4 : ℕ) ∣ 2 := by
    rcases h.2 2 2 hdvd with h' | h' <;> exact h'
  -- a positive number is at least as large as any of its divisors
  have h4 : (4 : ℕ) ≤ 2 := Nat.le_of_dvd (by omega) h2
  omega

/-- Irreducibility is the schoolbook condition on divisors: `1 < p`, and the
only divisors of `p` are `1` and `p`. Composed with `isPrime_iff_isIrreducible`
this identifies `IsPrime` with the familiar notion.
Blueprint: `lem:is_irreducible_iff_forall_dvd`. -/
theorem isIrreducible_iff_forall_dvd {p : ℕ} :
    IsIrreducible p ↔ 1 < p ∧ ∀ d : ℕ, d ∣ p → d = 1 ∨ d = p := by
  constructor
  · -- (→) the `1 < p` conjunct is shared; only the quantified clause moves
    rintro ⟨hp, hirr⟩
    refine ⟨hp, ?_⟩
    rintro d ⟨c, hc⟩
    rcases hirr d c hc with h | h
    · -- `p = d` is the right disjunct outright
      exact Or.inr h.symm
    · -- `p = c` substituted into `p = d * c` gives `p * 1 = p * d`; cancel `p`
      subst h
      have h0 : 0 < p := by omega
      have hmul : p * 1 = p * d := by rw [Nat.mul_one, Nat.mul_comm p d]; exact hc
      exact Or.inl (Nat.eq_of_mul_eq_mul_left h0 hmul).symm
  · -- (←) no cancellation and no positivity needed in this direction
    rintro ⟨hp, hdvd⟩
    refine ⟨hp, ?_⟩
    intro a b h
    -- `a ∣ p` by the one-step witness `⟨b, h⟩`
    rcases hdvd a ⟨b, h⟩ with ha | ha
    · -- `a = 1` turns `p = a * b` into `p = b`
      rw [ha, Nat.one_mul] at h
      exact Or.inr h
    · -- `a = p` is the left disjunct
      exact Or.inl ha.symm

end EuclidPrimes
