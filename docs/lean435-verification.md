# Lean 4.35 verification, 2026-11-19

Checked source revision: `a190b9a69732d83dea18e1eb3c94927641920c23`.

- Lean: `leanprover/lean4:v4.35.0`.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- CFT repository: `n-yamaguchi-0729/ClassFieldTheory`, revision
  `b9a2dddbf076eb96b768c333fd828d339ab3d9eb`; the package is now named `Nyll`.
- Root `lake build`: passed, 9371 jobs.
- Nested `lake build IwasawalibCFT Challenge Solution`: passed, 5337 jobs.
- Final theorem axiom guard: `propext`, `Classical.choice`, `Quot.sound` only.
- Standard `lake comparator`: passed, exit 0, with its bundled exporter and
  Lean checker. No cloned Comparator tool was used.

The nested project has a parent path dependency. Lake 4.35 hides home
folders, so the documented `COMPARATOR_BWRAP` adapter exposes this repository
read-only and its two build caches writable. All other Bubblewrap restrictions,
including Lake's network isolation for builds and checking, are retained.

```text
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

Local log: `/tmp/iwasawa-lake-comparator435b.log` (not a public artifact).
SHA-256: `333f3cfb34c15ba327af456498a2833a8e2dc69036ba3acb91de936c2f7fd0d4`.

## Source audit

`python3 scripts/audit-lean-sources.py` passed: 332 repository files and
5315 resolved non-core Solution import files; no missing module headers,
files over 10000 physical lines, symlinks, or unresolved non-core imports.
The largest local Lean file is 1472 lines.

All 911 CFT files in the closure of the adapter imports comply. The upstream
repository also has 294 non-module files outside that closure and no files
exceeding 10000 lines; all are listed in `cft-source-audit.md`. Upstream sources
were not modified. External Git dependencies are outside Palomar's repository
line cap, but their imported modules were checked here as requested.

## Metadata and scope

The official v0.4 schema accepts `formalization.yaml`. The responsible
maintainers are Jinzhao Pan, Yichuan Cao, and Jiawei Nie. The source is classified
as a formalization of an existing theorem, and the repository is the substantive
development. Palomar submission paths are in `palomar-submission.md`.
No submission, editorial review, or registration has been performed.

## Additional NanoDa check

The toolchain's bundled `nanoda_bin` (0.4.19) checked the exact same export
read by the successful Lean checker. It ran in Bubblewrap with no network,
allowing only `propext`, `Classical.choice`, and `Quot.sound`, with
`unpermitted_axiom_hard_error: true` and the natural-number/string extensions.
Exit status: 0.

```text
Checked 123997 declarations with no typechecker errors, 1 pretty printer errors: [
    "Unable to print axioms",
]
```

The reported pretty-printer diagnostic is recorded here; it was not a
kernel/typechecker rejection. The export SHA-256 is
`4400e5250c05e2443ac7fae99dad6411a5d06b8dcb9017093822c4df091bd723`.
Local log: `/tmp/iwasawa-nanoda435.log`. This additional check does not replace
Palomar's verification using its own pinned tools or constitute registration.
