# Iwasawa's class-number growth theorem

For a prime p and a number field K, let K_n be an increasing sequence of
intermediate fields in any ambient extension L/K. Suppose each K_n/K is
Galois with cyclic Galois group and degree p^n. The compared theorem asserts
that there are natural numbers mu and lambda, an integer nu, and a threshold
N such that, for every n > N, the exponent of p in the class number of K_n is
mu*p^n + lambda*n + nu.

This is Iwasawa's classical growth theorem (Washington, *Introduction to
cyclotomic fields*, second edition, Theorem 13.13; Iwasawa, *On Gamma-extensions
of algebraic number fields*, Theorem 11). It concerns class groups in infinite
arithmetic towers and is relevant to researchers in algebraic number theory
and Iwasawa theory. No new informal theorem or solution of an open problem is
claimed.

The Challenge uses only Mathlib definitions. It explicitly assumes that every
layer is a number field to make class numbers available in the statement;
this follows mathematically from the finite degree condition. The ambient
field L need not itself be algebraic or Galois over K. The proof forms the union
of the layers, identifies its Galois group with the additive p-adic integers,
and applies the unconditional Iwasawa theorem. External class field theory
proves the Hilbert class field inputs; they are not additional axioms.

Human contributors developed the original library, with the identified copilot
and Aristotle contributions recorded in the root `formalization.yaml`. Claude
Code/MMAT completed the September proof and CFT integration; Codex prepared
the tower bridge, comparison interface and version migration. The review claims
are automated checks and agent review, not independent human peer review.

Build with `lake build IwasawalibCFT Challenge Solution`, then run
`lake comparator`. See `COMPARATOR.md` and the repository's
`docs/palomar-submission.md` for verification and submission paths.
