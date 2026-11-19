#!/usr/bin/env bash
set -euo pipefail
# Lake 4.35 hides home directories. Expose this repository's contained parent
# dependency while preserving every other sandbox restriction passed by Lake.
repo_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
args=()
while (($#)); do
  if [[ $1 == -- ]]; then
    shift
    exec bwrap "${args[@]}" \
      --ro-bind "$repo_dir" "$repo_dir" \
      --bind "$repo_dir/.lake" "$repo_dir/.lake" \
      --bind "$repo_dir/IwasawalibCFT/.lake" "$repo_dir/IwasawalibCFT/.lake" \
      -- "$@"
  fi
  args+=("$1")
  shift
done
echo 'Expected Bubblewrap command separator' >&2
exit 2
