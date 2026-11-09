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
Earlier work is credited through source headers, the blueprint and Git authors;
its complete human/automation history is unknown. Actual cost was not recovered.

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
