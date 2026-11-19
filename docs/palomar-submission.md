# Palomar submission preparation

This is preparation material, not a submitted or registered entry.

Use the public repository `EonMath/lean-iwasawa` and the full 40-character SHA
of the final tested, committed and pushed migration snapshot. Do not use the
older Lean 4.33 verification commits for this migration.

Submission paths (repository-relative):

| Form field | Value |
| --- | --- |
| Project directory | `IwasawalibCFT` |
| Comparator configuration | `IwasawalibCFT/comparator.json` |
| Formalization metadata | `formalization.yaml` |
| Licence | `LICENSE` |
| Compared theorem | `NumberField.multiplicity_classNumber_eq_of_finrank_eq_pow` |

The repository itself is the substantive formalization, not a thin wrapper.
The result is source-based: Washington's Theorem 13.13 and Iwasawa's Theorem 11.
The selected project's README explains the mathematics, scope, assumptions,
proof construction, automation, and review status. Both Lake manifests are
committed; the nested project's path dependency `..` remains within the checkout.

The source audit passes for all 332 repository Lean files (largest: 1,472 lines)
and all 5,315 resolved non-core files in Solution's transitive import closure.
Run `python3 scripts/audit-lean-sources.py` to reproduce it.

The root and nested builds, source audit, and standard `lake comparator` under
Lean 4.35 passed on 2026-11-19. The bundled NanoDa also checked the same
export successfully. See `lean435-verification.md`, including the recorded
pretty-printer diagnostic. Historical Lean 4.33 checks are recorded
separately and do not certify the migration. Palomar performs its own protected
verification with NanoDa, regardless of the submitted `enable_nanoda` field.
A default local Lake comparison must not be described as a NanoDa check.

See `cft-source-audit.md` for the full upstream source findings. The 911 CFT
files reached from Solution's three external imports all have module headers
and are under 10,000 lines. Other upstream files lacking module headers are
listed for the maintainer; they are not imported by Solution and were not edited.
External pinned Git dependencies are outside Palomar's repository line cap.

The responsible human maintainers are Jinzhao Pan, Yichuan Cao, and Jiawei Nie,
as supplied by the user on 2026-11-19. The submitter must confirm their
authorization relationship before filing. Do not assert source-author endorsement or independent human
peer review without evidence. No Palomar review or registration has occurred.

Official instructions consulted on 2026-11-18:

- https://palomar-registry.org/how-to-submit
- https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md

Submitting is a separate action. The human submitter must review the material
and select the final immutable snapshot; an agent submitting on their behalf
must first read the intake service's `llms.txt` and follow its authorization
and publication requirements.
