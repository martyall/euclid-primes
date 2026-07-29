/-
Copyright (c) 2026 Martin Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Allen
-/
import Mathlib
import EuclidPrimes.Basic
import EuclidPrimes.Bezout

/-!
# Primality and irreducibility coincide on `ℕ`

The two notions introduced in `EuclidPrimes.Basic` coincide on `ℕ`.

The forward direction is pure cancellation: from `p = a * b` we get `p ∣ a * b`,
and whichever factor `p` divides turns out to equal `p`.

The reverse direction is the only consumer of Bézout's identity in the project:
it runs `exists_isGcd` and `bezout` from `EuclidPrimes.Bezout` on the pair
`(a, p)`, shows the gcd is `1`, and pushes the resulting identity through `ℤ`.
-/

namespace EuclidPrimes

/-- A prime is irreducible.

Blueprint: `thm:prime_imp_irreducible`. -/
theorem IsPrime.isIrreducible {p : ℕ} (hp : IsPrime p) : IsIrreducible p := by
  refine ⟨hp.1, fun a b hab => ?_⟩
  have hp0 : 0 < p := lt_trans Nat.zero_lt_one hp.1
  have hdvd : p ∣ a * b := hab ▸ dvd_rfl
  rcases hp.2 a b hdvd with h | h
  · -- `p ∣ a`, say `a = p * k`; then `p * 1 = p * (k * b)`, so `b = 1` and `p = a`.
    obtain ⟨k, hk⟩ := h
    have hcancel : p * 1 = p * (k * b) := by
      rw [mul_one]
      conv_lhs => rw [hab, hk]
      ring
    have hkb : k * b = 1 := (Nat.eq_of_mul_eq_mul_left hp0 hcancel).symm
    have hb : b = 1 := Nat.eq_one_of_mul_eq_one_left hkb
    exact Or.inl (by rw [hab, hb, mul_one])
  · -- Symmetric: `p ∣ b`, say `b = p * k`; then `a = 1` and `p = b`.
    obtain ⟨k, hk⟩ := h
    have hcancel : p * 1 = p * (k * a) := by
      rw [mul_one]
      conv_lhs => rw [hab, hk]
      ring
    have hka : k * a = 1 := (Nat.eq_of_mul_eq_mul_left hp0 hcancel).symm
    have ha : a = 1 := Nat.eq_one_of_mul_eq_one_left hka
    exact Or.inr (by rw [hab, ha, one_mul])

/-- An irreducible natural number is prime.

Blueprint: `thm:irreducible_imp_prime`. The `1 < p` clause transfers directly;
the divisibility clause is the Bézout argument, run on the pair `(a, p)`. -/
theorem IsIrreducible.isPrime {p : ℕ} (hp : IsIrreducible p) : IsPrime p := by
  refine ⟨hp.1, fun a b hab => ?_⟩
  -- Assume `¬ p ∣ a` and derive `p ∣ b`.
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · refine Or.inr ?_
    have hp0 : 0 < p := lt_trans Nat.zero_lt_one hp.1
    -- Step 1: pick `d` with `IsGcd a p d` (`exists_isGcd`).
    obtain ⟨d, hd⟩ := exists_isGcd a p
    -- Step 2: `d ∣ p` gives `p = d * k`; irreducibility forces `p = d` or `p = k`.
    --   `p = d` contradicts `¬ p ∣ a`; `p = k` cancels to `d = 1`.
    obtain ⟨k, hk⟩ := hd.2.1
    have hd1 : d = 1 := by
      rcases hp.2 d k hk with h | h
      · -- `p = d` and `d ∣ a`, so `p ∣ a`: impossible.
        exact absurd (h ▸ hd.1) ha
      · -- `p = k`, so `p * 1 = p * d`; cancel `p` (using `0 < p`).
        refine (Nat.eq_of_mul_eq_mul_left hp0 ?_).symm
        rw [mul_one]
        conv_lhs => rw [hk, ← h]
        ring
    -- Step 3: `bezout` gives `x * a + y * p = 1` in `ℤ`; multiply by `b`.
    obtain ⟨x, y, hxy⟩ := bezout (hd1 ▸ hd : IsGcd a p 1)
    push_cast at hxy
    have key : x * ((a : ℤ) * (b : ℤ)) + (y * (b : ℤ)) * (p : ℤ) = (b : ℤ) := by
      linear_combination (b : ℤ) * hxy
    -- Step 4: `(p : ℤ)` divides both summands, hence `(p : ℤ) ∣ (b : ℤ)`.
    have habZ : (p : ℤ) ∣ (a : ℤ) * (b : ℤ) := by
      have h := Int.natCast_dvd_natCast.mpr hab
      push_cast at h
      exact h
    have hpb : (p : ℤ) ∣ (b : ℤ) := by
      rw [← key]
      exact dvd_add (habZ.mul_left x) (Dvd.intro_left _ rfl)
    -- Step 5: cross back to `ℕ` via `Int.natCast_dvd_natCast`.
    exact Int.natCast_dvd_natCast.mp hpb

/-- Primality and irreducibility agree on `ℕ`.

Blueprint: `cor:prime_iff_irreducible`. -/
theorem isPrime_iff_isIrreducible {p : ℕ} : IsPrime p ↔ IsIrreducible p :=
  ⟨IsPrime.isIrreducible, IsIrreducible.isPrime⟩

/-- The schoolbook characterisation of primality: `p` is prime exactly when
`1 < p` and the only divisors of `p` are `1` and `p`.

The right-hand side is the definition of a prime number a reader already has, so
this identifies `IsPrime` with the familiar notion. It is stated here rather than
in `EuclidPrimes.Basic` because it consumes `isPrime_iff_isIrreducible`, which is
proved in this file.

Blueprint: `cor:prime_iff_forall_dvd`. -/
theorem isPrime_iff_forall_dvd {p : ℕ} :
    IsPrime p ↔ 1 < p ∧ ∀ d : ℕ, d ∣ p → d = 1 ∨ d = p :=
  isPrime_iff_isIrreducible.trans isIrreducible_iff_forall_dvd

end EuclidPrimes
