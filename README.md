# Euclid Primes

[![CI](https://github.com/martyall/euclid-primes/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/martyall/euclid-primes/actions/workflows/lean_action_ci.yml)
[![Blueprint](https://img.shields.io/badge/blueprint-web-blue)](https://martyall.github.io/euclid-primes/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/blueprint-pdf-blue)](https://martyall.github.io/euclid-primes/blueprint.pdf)
[![Docs](https://img.shields.io/badge/docs-API-blue)](https://martyall.github.io/euclid-primes/docs/)

<!-- archon:readme -->
<!-- Claude fills in the prose sections below. Keep the section headers. -->

## Project

A self-contained Lean 4 formalization of Euclid's theorem that there are
infinitely many primes, developed from first principles rather than assembled
from Mathlib's number theory. The point of the project is the *route*, not the
destination: Mathlib already proves the theorem as `Nat.exists_infinite_primes`,
so the goal here is to reconstruct the full chain of reasoning behind it —
divisibility and gcd, Bézout's identity, the equivalence of *prime* (`p ∣ a*b →
p ∣ a ∨ p ∣ b`) and *irreducible* (`p = a*b → p = a ∨ p = b`), and the existence
of a prime factorization — each proved against definitions this project states
for itself. Uniqueness of factorization is deliberately out of scope; the
informal source observes it is not needed for the main theorem, and it is not.

The development follows `references/euclid-infinitude-of-primes.md` step for
step. That source is a sketch rather than a finished text: it leaves Bézout's
identity as `proof: TODO`, omits the `1 < p` side conditions that keep the
definitions from admitting units, and argues one lemma with truncated natural
subtraction. `references/summary.md` records each of these gaps; closing them is
part of the formalization work.

## References

See [`references/summary.md`](references/summary.md) for a description of each source.

## Structure

- `EuclidPrimes/` — main Lean source
- `blueprint/src/` — the paper: `content.tex` plus one chapter per Lean module
- `home_page/` — Jekyll landing page for the published site
- `references/` — PDFs, papers, and informal notes backing the formalization
- `archon-protected.yaml` — declarations agents must not modify
- `.archon/` — agent state (not committed)

## Blueprint

The blueprint is the informal counterpart of the Lean development: every
statement carries a `\lean{...}` pointing at the declaration that formalizes it,
and a `\leanok` once that declaration is proved. It is published on every push
to `main`:

| | |
|---|---|
| Landing page | <https://martyall.github.io/euclid-primes/> |
| Blueprint (web) | <https://martyall.github.io/euclid-primes/blueprint/> |
| Blueprint (pdf) | <https://martyall.github.io/euclid-primes/blueprint.pdf> |
| Dependency graph | <https://martyall.github.io/euclid-primes/blueprint/dep_graph_document.html> |
| API documentation | <https://martyall.github.io/euclid-primes/docs/> |

In the web version each statement's **Lean** link opens that declaration in the
API docs, whose header links on to its source line on GitHub.

## How to build

```bash
lake exe cache get   # download Mathlib olean cache
lake build           # compile the project
```

To build the blueprint locally you need `leanblueprint` and graphviz:

```bash
sudo apt install graphviz libgraphviz-dev  # pygraphviz needs the headers
pip install -U leanblueprint

leanblueprint pdf     # -> blueprint/print/print.pdf
leanblueprint web     # -> blueprint/web/index.html
leanblueprint serve   # serve the web version locally
lake exe checkdecls blueprint/lean_decls   # every \lean{...} really exists
```

## How to run the formalization loop

```bash
archon loop .
```

This launches the plan → prove → review loop and opens a dashboard.
