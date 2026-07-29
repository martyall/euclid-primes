# References

<!-- archon:references-summary -->
<!-- One row per file. Agents append/update rows as they discover what -->
<!-- actually works. The `How to read` column is a LIVING LOG, not a -->
<!-- static cheat-sheet — fill it in the first time you successfully -->
<!-- ingest a file, and correct it if a later attempt finds a better way. -->

## File inventory

| File | Description | How to read (confirmed working) |
| ---- | ----------- | ------------------------------- |
| `euclid-infinitude-of-primes.md` | The sole source for this project: a hand-written, from-scratch informal development of Euclid's theorem, ~68 lines. Chain of results, in dependency order: (1) definitions of *prime* (`p ∣ a*b → p ∣ a ∨ p ∣ b`), *irreducible* (`p = a*b → p = a ∨ p = b`), and *gcd* by its universal property; (2) Bézout — `∃ x y : ℤ, x*a + y*b = gcd a b` — stated with `proof: TODO`; (3) prime ↔ irreducible, proved both directions, the hard direction via Bézout; (4) `a ∣ b → a < b` for distinct naturals > 1; (5) existence of a prime factorization by strong induction; (6) uniqueness of that factorization, explicitly annotated by the author as *not needed* for the main theorem; (7) infinitude of primes via `m = ∏ pᵢ`, factoring `m + 1`. See "Known gaps" below — the notes are a sketch, not a finished text. | `Read` (plain Markdown, no options needed) |

## Known gaps in the source

Recorded here so no agent rediscovers them. These are defects in the informal
notes, not in the mathematics — each needs a decision during formalization.

- **Missing `1 < p` side conditions.** Both `prime` and `irreducible` are stated
  without excluding units, so `p = 1` satisfies each vacuously, and `p = 0`
  satisfies the prime condition (`0 ∣ a*b ↔ a*b = 0 ↔ a = 0 ∨ b = 0`). The Lean
  definitions must carry `1 < p`, otherwise the factorization theorem is false.
- **`irreducible` needs a positivity hypothesis to be usable.** As written,
  `p = a*b → p = a ∨ p = b` is the intended notion only for `p > 0`; the step
  "`p = a` therefore `b = 1`" is cancellation, which needs `p ≠ 0`.
- **Bézout is stated with `proof: TODO`.** This is the one genuinely open step
  in the source and the largest piece of work in the project. Neither the
  Euclidean-algorithm route nor the least-positive-element route is indicated.
- **Bézout mixes ℕ and ℤ.** `gcd` is defined on naturals but the coefficients
  `x, y` are integers, so the statement and everything downstream of it must
  cross into ℤ and back. The notes do not address the coercion.
- **`a ∣ b → a < b` is proved with truncated subtraction.** The informal step
  `b - a = a*(c-1) > 0` is over ℕ, where `-` truncates; the argument needs
  restating (or moving to ℤ) to be valid.
- **Uniqueness of factorization is flagged `## Note: I dont think we actually
  need this` by the author, and its proof is visibly incomplete** — the
  displayed equation `∏₁ pᵢ^eᵢ = ∏₂ pᵢ^fᵢ` has mismatched indices and the
  bijection argument is only gestured at. Treat as out of scope unless the
  mathematician says otherwise.
- **The final proof needs `1 < m + 1`.** Applying the factorization theorem to
  `m + 1` requires it to exceed 1, i.e. `m ≥ 1`; true for a product of primes
  but not remarked on. The concluding line `p_j ∣ 1, contradiction` also has a
  typo (`m_j` for `p_j`).
