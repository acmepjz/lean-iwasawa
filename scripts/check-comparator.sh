#!/usr/bin/env bash
set -euo pipefail
# Run from any directory; tools must be installed as described in COMPARATOR.md.
repo_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
comparator_bin=$(command -v "${COMPARATOR_BIN:-comparator}") || {
  echo 'Missing comparator; see IwasawalibCFT/COMPARATOR.md.' >&2
  exit 1
}
comparator_bin=$(realpath "$comparator_bin")
export COMPARATOR_LANDRUN
COMPARATOR_LANDRUN=$(command -v "${COMPARATOR_LANDRUN:-landrun}")
export COMPARATOR_LEAN4EXPORT
COMPARATOR_LEAN4EXPORT=$(command -v "${COMPARATOR_LEAN4EXPORT:-lean4export}")
# Follow upstream's AF_UNIX restriction in addition to the real Landrun sandbox.
exec systemd-run --user --wait --pipe --collect \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --working-directory="$repo_dir/IwasawalibCFT" \
  -E PATH="$PATH" \
  -E COMPARATOR_LANDRUN="$COMPARATOR_LANDRUN" \
  -E COMPARATOR_LEAN4EXPORT="$COMPARATOR_LEAN4EXPORT" \
  lake env "$comparator_bin" comparator.json
