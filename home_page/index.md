---
usemathjax: true
---

A self-contained Lean 4 formalization of Euclid's theorem that there are
infinitely many primes. Mathlib already proves the theorem, so the point here is
the *route*: divisibility and gcd, Bézout's identity, the equivalence of
$\mathrm{Prime}$ and $\mathrm{Irred}$, and the existence of a prime
factorization, each proved against definitions this project states for itself.

The blueprint below is the informal counterpart of the Lean development. Every
statement it marks with a checkmark is formalized; clicking a statement's
**Lean** link opens the corresponding declaration in the API documentation,
which in turn links to its source line on GitHub.

Useful links:

* [Blueprint]({{ site.url }}/blueprint/) — the paper, web version
* [Blueprint as pdf]({{ site.url }}/blueprint.pdf)
* [Dependency graph]({{ site.url }}/blueprint/dep_graph_document.html) — what is proved, and what each result rests on
* [API documentation]({{ site.url }}/docs/) — generated from the Lean source
* [GitHub repository](https://github.com/martyall/euclid-primes)
