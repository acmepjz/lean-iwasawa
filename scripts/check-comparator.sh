#!/usr/bin/env bash
set -euo pipefail
repo_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
export COMPARATOR_BWRAP="$repo_dir/scripts/comparator-bwrap.sh"
cd "$repo_dir/IwasawalibCFT"
exec lake comparator "$@"
