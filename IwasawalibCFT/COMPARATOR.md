# Comparing the Mathlib-only Iwasawa theorem

The nested project uses Lean 4.35.0's standard `lake comparator` command.
Install Bubblewrap (`bwrap`) and the pinned Lean toolchain; no separate
Comparator checkout, exporter, Go installation, or Landrun is needed.

From the repository root:

```bash
(cd IwasawalibCFT && lake build IwasawalibCFT Challenge Solution)
scripts/check-comparator.sh
```

The script runs `lake comparator` inside `IwasawalibCFT/`. The committed
manifest is required. The initial build populates the shared dependency
artifacts outside the nested package's writable `.lake` directory.
Bubblewrap needs unprivileged user namespaces or a suitable system installation.
The script preserves Lake's sandbox and propagates its exit status. Lake 4.35
hides home directories and otherwise cannot see this nested project's `..`
path dependency. `scripts/comparator-bwrap.sh` exposes only the repository
read-only and its two `.lake` caches writable via `COMPARATOR_BWRAP`, retaining
Lake's process and network restrictions. It does not disable sandboxing.

`comparator.json` selects only
`NumberField.multiplicity_classNumber_eq_of_finrank_eq_pow`.
Challenge imports only `Mathlib.NumberTheory.NumberField.ClassNumber` and
states the growth formula for an increasing cyclic Galois tower of degrees p^n.
Its single sorry is an intentional specification hole. Solution imports the
proof that constructs the union as a Z_p-extension and recovers each layer.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

`lake comparator --paranoid` additionally runs all external checkers bundled
with the toolchain. Palomar independently uses its protected verification
configuration with NanoDa enabled; a local default Lake run is not a claim of
Palomar acceptance or NanoDa verification.

The November 9 and 10 verification records in `docs/` concern the previous
Lean 4.33 snapshots. They do not certify this Lean 4.35 migration.

The Lean 4.35 migration passed standard Lake Comparator on 2026-11-19;
see [the verification record](../docs/lean435-verification.md).
