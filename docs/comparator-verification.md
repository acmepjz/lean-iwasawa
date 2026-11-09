# Comparator verification, 2026-11-09

Both declarations in `IwasawalibCFT/comparator.json` passed:

- `MvZpExtension.multiplicity_classNumber_Kn_eq₁`
- `NumberField.exists_cyclotomic_multiplicity_classNumber_eq`

The checked proof sources and statements are those at repository commit
`27fea2cdbded165dda55c5420cde8066e53b3b83`. This follow-up changes only
verification records and the Landrun installation command, not Lean sources
or the comparator configuration.

## Tools and execution

- Lean: v4.33.0, Linux aarch64.
- Comparator: `3927ad383f208ae977c340a91c48ac9b497d2097`.
- lean4export: `15f6055e299ad5b89345e533cc2192f4cc00f659`.
- Landrun: `v0.1.18-0.20261016135722-ec104f6edc1e`, built with Go 1.25.0.
- Runner: `scripts/check-comparator.sh`, with absolute tool paths supplied via
  `COMPARATOR_BIN`, `COMPARATOR_LANDRUN`, and `COMPARATOR_LEAN4EXPORT`.
- Sandbox: real Landrun, plus systemd `RestrictAddressFamilies=~AF_UNIX`.
- Permitted axioms: `propext`, `Quot.sound`, `Classical.choice`.
- Additional external kernel: none (`enable_nanoda: false`).

The shared dependencies were first built with `lake build Challenge Solution`.
Comparator then built both modules inside its sandbox, exported the selected
results and their dependencies, compared the declarations, checked the axiom
allowlist, and replayed the solution in Lean's kernel.

## Result

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
Finished with result: success
Main processes terminated with: code=exited/status=0
Service runtime: 11min 55.550s
CPU time consumed: 11min 56.126s
```

The full local execution log is `/tmp/iwasawa-comparator-full.log` (not a
permanent public artifact); its SHA-256 is:

```text
524f28cf62461633276bff5532880f767ede50008caefda5d87789310fdccfce
```

The two Challenge sorry warnings are intentional specification placeholders.
They are not permitted axioms of the solution. This result does not assert
Nanoda verification or independent review of correspondence to the literature.
