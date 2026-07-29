/-
Copyright (c) 2026 Martin Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Allen
-/
import Mathlib
import EuclidPrimes.Basic
import EuclidPrimes.Irreducible

/-!
# Existence of a prime factorisation

Every `n > 1` is the product of a list of primes, and consequently has at least
one prime divisor.

The factorisation is recorded as a `List ℕ` whose product is `n`, with
multiplicity expressed by repetition rather than by exponents; grouping the list
by value recovers the classical `∏ pᵢ ^ eᵢ` form. Uniqueness is deliberately out
of scope — nothing downstream needs it.
-/

namespace EuclidPrimes

/-- Failure of irreducibility for `n > 1` produces a factorisation of `n` into
two factors, neither of which is `1`. -/
theorem exists_factor_of_not_isIrreducible {n : ℕ} (hn : 1 < n)
    (h : ¬ IsIrreducible n) : ∃ a b : ℕ, n = a * b ∧ a ≠ 1 ∧ b ≠ 1 := by
  rw [IsIrreducible] at h
  push Not at h
  obtain ⟨a, b, hab, hna, hnb⟩ := h hn
  refine ⟨a, b, hab, ?_, ?_⟩
  · rintro rfl
    exact hnb (by rw [hab, Nat.one_mul])
  · rintro rfl
    exact hna (by rw [hab, Nat.mul_one])

/-- **Existence of a prime factorisation**: every `n > 1` is the product of a
list of primes. -/
theorem exists_factorization {n : ℕ} (hn : 1 < n) :
    ∃ l : List ℕ, (∀ p ∈ l, IsPrime p) ∧ l.prod = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hirr : IsIrreducible n
    · -- `n` is irreducible, hence prime, and `[n]` is its factorisation.
      have hprime : IsPrime n := isPrime_iff_isIrreducible.mpr hirr
      exact ⟨[n], by simpa using hprime, by simp⟩
    · obtain ⟨a, b, hab, ha1, hb1⟩ := exists_factor_of_not_isIrreducible hn hirr
      have hba : n = b * a := by rw [hab, Nat.mul_comm]
      have ha : 1 < a := one_lt_factor hn hab ha1
      have hb : 1 < b := one_lt_factor hn hba hb1
      obtain ⟨la, hla, hlap⟩ := ih a (factor_lt hn hab ha1 hb1) ha
      obtain ⟨lb, hlb, hlbp⟩ := ih b (factor_lt hn hba hb1 ha1) hb
      refine ⟨la ++ lb, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with h | h
        · exact hla p h
        · exact hlb p h
      · rw [List.prod_append, hlap, hlbp, hab]

/-- Every `n > 1` has a prime divisor: the head of any prime factorisation of
`n` divides `n`. -/
theorem exists_isPrime_dvd {n : ℕ} (hn : 1 < n) : ∃ p : ℕ, IsPrime p ∧ p ∣ n := by
  obtain ⟨l, hl, hlp⟩ := exists_factorization hn
  match l, hl, hlp with
  | [], _, hlp => rw [List.prod_nil] at hlp; omega
  | p :: t, hl, hlp =>
    exact ⟨p, hl p (by simp), hlp ▸ List.dvd_prod (by simp)⟩

/-- **Existence of a prime factorisation, exponent form**: every `n > 1` is a
product `∏ p ∈ S, p ^ e p` over a finite set `S` of primes with every exponent
positive. Indexing by a `Finset` is what records that the primes are distinct.

This is `exists_factorization` with the list grouped by value: `S` is the set of
distinct values occurring in the list and `e p` is the multiplicity of `p` in
it. `e` is total on `ℕ`, but only its values on `S` are constrained — the others
do not enter the product. -/
theorem exists_factorization_pow {n : ℕ} (hn : 1 < n) :
    ∃ (S : Finset ℕ) (e : ℕ → ℕ),
      (∀ p ∈ S, IsPrime p) ∧ (∀ p ∈ S, 0 < e p) ∧ ∏ p ∈ S, p ^ e p = n := by
  obtain ⟨l, hl, hlp⟩ := exists_factorization hn
  -- Regard `l` as a multiset: the order the induction produced carries no
  -- information here.
  refine ⟨(l : Multiset ℕ).toFinset, fun p => (l : Multiset ℕ).count p, ?_, ?_, ?_⟩
  · -- A value occurring in the multiset occurs in `l`, hence is prime.
    intro p hp
    exact hl p (by simpa using hp)
  · -- A value occurs in a multiset exactly when its multiplicity is positive.
    intro p hp
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
  · -- Collecting equal factors: the multiset product is the product over the
    -- distinct values of each value raised to its multiplicity.
    rw [← Finset.prod_multiset_count, Multiset.prod_coe]
    exact hlp

end EuclidPrimes
