# Mathlib-only Comparator verification, 2026-11-10

The sole current target is
`NumberField.multiplicity_classNumber_eq_of_finrank_eq_pow`.
The checked proof sources and configuration are at commit
`721720997fb9f9760ca49c8e606c46a8639a0ba6`.

`Challenge.lean` imports only `Mathlib.NumberTheory.NumberField.ClassNumber`.
Its statement is exactly lines 36–46 of upstream `ClassGroup.lean` at
`aef1a74ec13d5a5684367e9c43668fae276c7cd9`, preceded by the requested import
and variables. The structure-based and cyclotomic theorems are not targets.

## Validation

- `lake build IwasawalibCFT Challenge Solution`: passed (5248 jobs).
- Build-time axiom guard: `propext`, `Classical.choice`, `Quot.sound` only.
- Exact name, universe-parameter list and elaborated-type comparison: passed.
- Metadata validation against the official v0.4 schema: passed.
- Full Comparator statement/dependency comparison and axiom allowlist: passed.
- Lean kernel replay: passed. Nanoda was not enabled.

The first run detected differently named automatic universe parameters in the
solution. The final theorem was isolated in `MathlibIwasawa.lean` with the same
variable declarations as the challenge; no challenge hypothesis or conclusion
was changed. The result below is from the complete rerun after that correction.

## Execution

The tools and runner are the same as in the
[November 9 record](comparator-verification.md): Lean 4.33.0,
Comparator `3927ad383f208ae977c340a91c48ac9b497d2097`, lean4export
`15f6055e299ad5b89345e533cc2192f4cc00f659`, and Landrun
`v0.1.18-0.20261016135722-ec104f6edc1e`. The real Landrun sandbox and systemd
AF_UNIX restriction were enabled through `scripts/check-comparator.sh`.

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
Finished with result: success
Main processes terminated with: code=exited/status=0
Service runtime: 11min 32.045s
CPU time consumed: 11min 35.254s
Memory peak: 6.5G
```

The local full log is `/tmp/iwasawa-mathlib-comparator-final.log` (not a
permanent public artifact). SHA-256:

```text
6d05e96bc86bf587bd052e6b3c061917a135512ee4ddb12fb0e332fff4582cb5
```

The single Challenge sorry is an intentional statement placeholder and does
not occur in the solution's axiom dependencies. This record does not claim
independent human review of the statement's correspondence to the literature.
