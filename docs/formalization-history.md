# Recovered formalization history

The September 2026 completion work was recovered from local Claude Code JSONL
records and checked against Git history. Raw conversations are not included:
they also contain unrelated work. Session IDs are local provenance locators,
not public links or independent certificates.

- Main coordinating session: `a8c9c3c8-8960-48db-be3b-fdd478fd0d79`.
  On 2026-09-26 at 16:57 UTC the user requested completion of
  `EonMath/lean-iwasawa`. On September 27 the user requested an axiom/sorry
  audit, external CFT integration, and removal of obsolete proof branches.
- MMAT FL-Prover session: `af0de6ba-5cd4-4448-919f-15910152abdb`.
  Its task reports document skeletons, proofs, integration and review.
- The coordinating record contains model IDs `claude-fable-5-1` and
  `claude-opus-5-5`; the FL-Prover record contains `claude-fable-5-1`.
  These are recorded identifiers, not retrospective guesses about model branding.

| Commit | Milestone |
| --- | --- |
| `c985999` | Export previously private declarations needed by the proof chain. |
| `4ce1bd7` | Assemble the growth theorem modulo the then-unproved CFT facts. |
| `5cff859` | Close the conditional theorem, add non-vacuity and generator results. |
| `c5d25cb` | Align Lean/Mathlib with the external CFT library. |
| `b236c1b` | Obtain a sorry-free unconditional proof through external CFT. |
| `f92099b` | Remove obsolete CFT holes and their dependent declarations; keep the unconditional theorem under the original name. |

The recovered final report says both packages built, blueprint declaration
checks passed, and the main results used only `propext`, `Classical.choice`,
and `Quot.sound`. The source contains executable axiom guards for those results.
These historical reports are distinguished from fresh verification below.
Earlier work is credited through source headers, the blueprint and Git authors.
Contributor clarification on 2026-11-10 identifies it as predominantly human-written,
with copilot assistance in `cf5cb00` and Aristotle proofs with human refactoring
in `3850e82`, `12d2514` and `31e2978`. The Aristotle commit messages corroborate
these attributions. Specific models and actual costs were not supplied.

## November 2026 metadata and comparison preparation

Codex added `formalization.yaml` using the official v0.4 schema and a separate
Comparator challenge/solution interface for both unconditional endpoints.
The CFT package was rebuilt successfully during this preparation (5241 jobs).
`lake build Challenge Solution` also passed (5243 jobs), with only the two
expected Challenge sorry warnings in the new interface. The metadata passed
validation against the official v0.4 JSON Schema. The initial attempt to run
Comparator and push was blocked by unavailable tools and terminal network access.
After network access was restored on November 9, the compatible tools were built
and both endpoints passed full Comparator validation, including Lean kernel
replay, in 11 minutes 56 seconds (exit 0). Landrun's installation command was
corrected to use `cmd/landrun` and its tested version was pinned in the setup
instructions and CI. See the [verification record](comparator-verification.md)
and [comparison instructions](../IwasawalibCFT/COMPARATOR.md).

## Mathlib-only challenge, November 10

Following contributor feedback, the challenge was replaced by the exact
`NumberField.multiplicity_classNumber_eq_of_finrank_eq_pow` statement from
upstream `ClassGroup.lean` at `aef1a74ec13d5a5684367e9c43668fae276c7cd9`.
Its sole import is `Mathlib.NumberTheory.NumberField.ClassNumber`. The earlier
structure-based theorem and cyclotomic corollary remain in the library but
are no longer Comparator targets.

The proof constructs the union of the cyclic Galois tower and restricts the
layers to it. Compactness supplies an automorphism generating every finite
quotient. These compatible quotients identify the union's Galois group with
the additive p-adic integers. The prescribed degrees identify the original
layers with the canonical Z_p-extension layers, and field isomorphisms preserve
their class numbers. The unconditional Iwasawa theorem then gives the formula.
The bridge is proved in `IwasawalibCFT.CyclicTower` and `IwasawalibCFT.Tower`;
the final statement is in `IwasawalibCFT.MathlibIwasawa`.

The first Comparator attempt detected different automatically generated
universe parameter names. Moving the final statement to its own module
preserved the requested signature and made the elaborated name, universe
list, and type literally identical to the challenge. The fresh full Comparator
run passed on November 10 (exit 0, 11 minutes 32 seconds), including Lean kernel
replay. The November 9 result above covers only the earlier pair of targets.
See [the current verification record](comparator-mathlib-verification.md).

## Lean 4.35 migration and Palomar preparation, November 18–19

The project moved to Lean 4.35.0, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, and CFT revision
`b9a2dddbf076eb96b768c333fd828d339ab3d9eb` (now the `Nyll` package).
Local compatibility changes preserve theorem statements; duplicate idele
and absolute-value declarations now supplied by Mathlib were removed.
The field-equality Galois transport was implemented through the canonical
algebra equivalence to avoid kernel timeouts. All repository Lean files
now use modules. Upstream sources were left unchanged.

Standard `lake comparator` replaces the cloned verifier; its Bubblewrap
adapter exposes the contained parent dependency and build caches. Root and
nested builds, source audits, metadata validation, Lean replay and an additional
NanoDa check passed. See `lean435-verification.md` for the exact source revision,
checksums and NanoDa's non-typechecking pretty-printer diagnostic.
The human responsible maintainers supplied by the user are Jinzhao Pan,
Yichuan Cao, and Jiawei Nie. Palomar submission materials were prepared, but
no submission or registration was made.
