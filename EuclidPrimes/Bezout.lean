/-
Copyright (c) 2026 Martin Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Allen
-/
import Mathlib
import EuclidPrimes.Basic

/-!
# Existence of gcds, and Bézout's identity

The informal source states Bézout's identity with `proof: TODO`; this module
supplies the argument. We take the Euclidean-algorithm route — strong induction
along `b % a` — rather than the least-positive-element route, because it needs
no well-ordering setup and produces the gcd *and* the coefficients in a single
recursion.

## Coercion discipline

`IsGcd` and every divisibility hypothesis live in `ℕ`. `ℤ` appears only for the
two Bézout coefficients, and only inside the equation they satisfy. Truncated
subtraction is never used inside a cast: wherever the Euclidean step wants
`b - a * q` we transport the *addition* identity `a * (b / a) + b % a = b` into
`ℤ`, where subtraction is total.
-/

namespace EuclidPrimes

/-- A gcd is unique: `IsGcd` pins down `d` exactly. -/
theorem IsGcd.unique {a b d d' : ℕ} (h : IsGcd a b d) (h' : IsGcd a b d') :
    d = d' :=
  Nat.dvd_antisymm (h'.2.2 d h.1 h.2.1) (h.2.2 d' h'.1 h'.2.1)

/-- The Euclidean reduction preserves gcds: a gcd of `(b % a, a)` is a gcd of
`(a, b)`.

No positivity hypothesis is needed: `b % 0 = b`, so the `a = 0` case is the
hypothesis with its two divisibility clauses swapped. -/
theorem isGcd_of_mod {a b d : ℕ} (h : IsGcd (b % a) a d) :
    IsGcd a b d := by
  obtain ⟨hdr, hda, huniv⟩ := h
  exact ⟨hda, (Nat.dvd_mod_iff hda).mp hdr,
    fun c hca hcb => huniv c ((Nat.dvd_mod_iff hca).mpr hcb) hca⟩

/-- Simultaneous existence of a gcd and of Bézout coefficients.

The two conclusions are proved *together*, in one strong induction on `a` with
`b` universally quantified, recursing on the swapped pair `(b % a, a)`.
Separating them would force the induction to run twice, and the second run
would have no handle on *which* `d` the first one produced. -/
theorem exists_isGcd_bezout (a b : ℕ) :
    ∃ d : ℕ, IsGcd a b d ∧ ∃ x y : ℤ, x * (a : ℤ) + y * (b : ℤ) = (d : ℤ) := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact ⟨b, ⟨Nat.dvd_zero b, dvd_rfl, fun _ _ hcb => hcb⟩, 0, 1,
        by push_cast; ring⟩
    · obtain ⟨d, hd, x, y, hxy⟩ := ih (b % a) (Nat.mod_lt b ha) a
      have hdm : (a : ℤ) * ((b / a : ℕ) : ℤ) + ((b % a : ℕ) : ℤ) = (b : ℤ) := by
        exact_mod_cast Nat.div_add_mod b a
      exact ⟨d, isGcd_of_mod hd, y - x * ((b / a : ℕ) : ℤ), x,
        by linear_combination hxy - x * hdm⟩

/-- Every pair of naturals has a gcd. -/
theorem exists_isGcd (a b : ℕ) : ∃ d : ℕ, IsGcd a b d := by
  obtain ⟨d, hd, _⟩ := exists_isGcd_bezout a b
  exact ⟨d, hd⟩

/-- Bézout's identity, in the form the source states it: for *any* gcd `d` of
`a` and `b` there are integer coefficients `x`, `y` with `x * a + y * b = d`. -/
theorem bezout {a b d : ℕ} (h : IsGcd a b d) :
    ∃ x y : ℤ, x * (a : ℤ) + y * (b : ℤ) = (d : ℤ) := by
  obtain ⟨d₀, hd₀, hxy⟩ := exists_isGcd_bezout a b
  rwa [hd₀.unique h] at hxy

end EuclidPrimes
