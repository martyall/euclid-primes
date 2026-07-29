/-
Copyright (c) 2026 Martin Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Allen
-/
import Mathlib
import EuclidPrimes.Basic
import EuclidPrimes.Factorization

/-!
# There are infinitely many primes

Euclid's theorem, in the three shapes the blueprint asks for: no list of
naturals contains exactly the primes, the set of primes is infinite, and the
primes are unbounded.

The list hypothesis is deliberately two-sided — the list contains *only* primes
as well as *all* primes. With only the second half the list could contain `0`,
making its product `m = 0`, and then `m + 1 = 1` has no prime divisor and the
statement is false.

The contradiction is `q ∣ 1` against `1 < q`, so it is the `1 < p` conjunct of
`EuclidPrimes.IsPrime` that carries the argument.
-/

namespace EuclidPrimes

/-- **Euclid's theorem.** No finite list of naturals contains exactly the
primes: there is no `l` whose members are all prime and which contains every
prime.

The proof takes `m := l.prod`, which is positive because every member of `l` is
`> 1`, obtains a prime `q ∣ m + 1`, notes `q ∈ l` hence `q ∣ m`, and concludes
`q ∣ 1`, contradicting `1 < q`. -/
theorem not_exists_isPrime_list :
    ¬ ∃ l : List ℕ, (∀ p ∈ l, IsPrime p) ∧ (∀ p : ℕ, IsPrime p → p ∈ l) := by
  rintro ⟨l, honly, hall⟩
  -- Step 1: `0 < l.prod`, because every member is `> 1` hence `> 0`.
  have hmpos : 0 < l.prod := List.prod_pos fun a ha => lt_trans Nat.zero_lt_one (honly a ha).1
  -- Step 2: `1 < l.prod + 1`, so `l.prod + 1` has a prime divisor.
  obtain ⟨q, hq, hqdvd⟩ := exists_isPrime_dvd (n := l.prod + 1) (by omega)
  -- Step 3: `q` is prime, hence a member of `l`, hence divides `l.prod`.
  have hqm : q ∣ l.prod := List.dvd_prod (hall q hq)
  -- Step 4: `q` divides `(l.prod + 1) - l.prod = 1`, contradicting `1 < q`.
  have hq1 : q ∣ 1 := by simpa using Nat.dvd_sub hqdvd hqm
  have hqle : q ≤ 1 := Nat.le_of_dvd Nat.one_pos hq1
  have h1q : 1 < q := hq.1
  omega

/-- The set of primes is infinite. -/
theorem infinite_setOf_isPrime : {p : ℕ | IsPrime p}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  refine not_exists_isPrime_list ⟨hfin.toFinset.toList, ?_, ?_⟩
  · intro p hp
    exact (Set.Finite.mem_toFinset hfin).mp (Finset.mem_toList.mp hp)
  · intro p hp
    exact Finset.mem_toList.mpr ((Set.Finite.mem_toFinset hfin).mpr hp)

/-- The primes are unbounded: for every `n` there is a prime `p` with `n < p`. -/
theorem exists_isPrime_gt (n : ℕ) : ∃ p : ℕ, IsPrime p ∧ n < p := by
  obtain ⟨p, hmem, hlt⟩ := infinite_setOf_isPrime.exists_gt n
  exact ⟨p, hmem, hlt⟩

end EuclidPrimes
