# Comparing the unconditional results

Run from this nested Lake package: the root package intentionally has no CFT
dependency. `comparator.json` selects both final theorems, preserving their
original names, universes, instances and statements. `Challenge.lean` imports
only the root library and has two deliberate statement holes. `Solution.lean`
imports the existing unconditional proofs. The modules must never be imported
together. Only the three standard axioms are permitted; `sorryAx` is excluded.

The project uses Lean 4.33.0. Use the standalone
[Comparator](https://github.com/leanprover/comparator) revision
`3927ad383f208ae977c340a91c48ac9b497d2097`, whose committed manifest pins
lean4export to `15f6055e299ad5b89345e533cc2192f4cc00f659` for that toolchain.
Do not run `lake update` in the verifier checkout: its dependency declaration
tracks master, whereas its committed manifest supplies the compatible version.
The newer `lake comparator` command requires Lean 4.35 or later.

On Linux with Landlock and a systemd user session, prepare the tools outside
this repository (Elan/Lake and Go are prerequisites):

```bash
git clone https://github.com/leanprover/comparator.git /tmp/iwasawa-comparator
cd /tmp/iwasawa-comparator
git checkout 3927ad383f208ae977c340a91c48ac9b497d2097
lake build comparator lean4export
go install github.com/zouuup/landrun/cmd/landrun@v0.1.18-0.20261016135722-ec104f6edc1e
export PATH="/tmp/iwasawa-comparator/.lake/build/bin:/tmp/iwasawa-comparator/.lake/packages/lean4export/.lake/build/bin:$(go env GOPATH)/bin:$PATH"
```

First run `lake build Challenge Solution` from `IwasawalibCFT/` on this trusted
checkout. Its shared dependencies live in the root `.lake`, outside the
comparator sandbox's writable directory, so they must already be built.
From this repository's root, run `scripts/check-comparator.sh`. It runs the
real sandbox with upstream's additional AF_UNIX restriction and propagates
failure. Absolute tool paths can instead be supplied through `COMPARATOR_BIN`,
`COMPARATOR_LANDRUN`, and `COMPARATOR_LEAN4EXPORT`. This configuration checks
with Lean's kernel; it does not claim an additional Nanoda run.

For a build-only smoke check, run `lake build Challenge Solution` from
`IwasawalibCFT/`. The two Challenge sorry warnings are expected. This is not
Comparator verification. The separate manual GitHub Actions workflow installs
the compatible verifier and runs full comparison; metadata validation runs on
pushes and pull requests. A first CFT build can take hours.

The challenge imports, Lake configuration and pinned dependencies are part of
the trusted specification. Review them along with the theorem statements;
comparison does not prove that these statements faithfully express the book.

Both endpoints passed this full check on 2026-11-09; see the
[verification record](../docs/comparator-verification.md) for exact revisions
and output. The Landrun version above is the tested revision from upstream main.
