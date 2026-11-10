#!/usr/bin/env bash
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

# Builds the pinned `leanprover/comparator`, `leanprover/lean4export` and `Zouuup/landrun` into
# OUT_DIR (default: `$RUNNER_TEMP/comparator-tools`, else `./.lake/comparator-tools`) and writes
# `OUT_DIR/env` with `COMPARATOR_BIN`, `COMPARATOR_LEAN4EXPORT` and `COMPARATOR_LANDRUN`.
#
# Usage: comparator/install-tools.sh [OUT_DIR]
#
# The pins below must match the repository's `lean-toolchain`: comparator and lean4export are
# tagged per Lean release, and lean4export must read `.olean` files of the exact toolchain. When the
# repository bumps Lean, bump `COMPARATOR_REV` to comparator's tag of the new release (its
# `lake-manifest.json` pins the matching lean4export; the check below fails otherwise). From Lean
# v4.35.0 on, comparator is part of core (`lake comparator`), see `comparator/README.md`.
set -euo pipefail

# leanprover/comparator, tag v4.34.0.
COMPARATOR_REV='d03acab154d269c06e60e4de7e4cc85deebff94b'
COMPARATOR_TOOLCHAIN='leanprover/lean4:v4.34.0'
# leanprover/lean4export, tag v4.34.0 (the revision comparator's `lake-manifest.json` pins).
LEAN4EXPORT_REV='076e8e57707e813375e8f9da8bf989799ace9680'
# Zouuup/landrun `main` (comparator needs `--ldd`/`--add-exec`, which are not in a release yet).
LANDRUN_REV='ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a'
# Go toolchain for landrun, used only when `go` is not on PATH.
GO_VERSION='1.27.3'
GO_SHA256='65efbc80fdc1fa2cd2631cad5b481777a68e8725f34e89f50fc6ac714e379b40'

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
out="${1:-${RUNNER_TEMP:+$RUNNER_TEMP/comparator-tools}}"
out="${out:-$repo_root/.lake/comparator-tools}"
mkdir -p "$out"
out="$(cd "$out" && pwd)"

repo_toolchain="$(tr -d '[:space:]' < "$repo_root/lean-toolchain")"
if [[ "$repo_toolchain" != "$COMPARATOR_TOOLCHAIN" ]]; then
  echo "::error::lean-toolchain is $repo_toolchain but comparator/install-tools.sh pins comparator" \
    "for $COMPARATOR_TOOLCHAIN; bump COMPARATOR_REV and LEAN4EXPORT_REV" >&2
  exit 1
fi

fetch_rev() { # url rev dir
  if [[ ! -d "$3/.git" ]]; then
    git init -q "$3"
    git -C "$3" remote add origin "$1"
  fi
  git -C "$3" fetch -q --depth 1 origin "$2"
  git -C "$3" checkout -q --detach FETCH_HEAD
  local got
  got="$(git -C "$3" rev-parse HEAD)"
  [[ "$got" == "$2" ]] || { echo "::error::$1: expected $2, got $got" >&2; exit 1; }
}

# comparator (and, through its manifest, lean4export).
fetch_rev https://github.com/leanprover/comparator.git "$COMPARATOR_REV" "$out/comparator"
tc="$(tr -d '[:space:]' < "$out/comparator/lean-toolchain")"
[[ "$tc" == "$COMPARATOR_TOOLCHAIN" ]] \
  || { echo "::error::comparator $COMPARATOR_REV targets $tc, not $COMPARATOR_TOOLCHAIN" >&2; exit 1; }
python3 - "$out/comparator/lake-manifest.json" "$LEAN4EXPORT_REV" <<'PY'
import json, sys
manifest = json.load(open(sys.argv[1], encoding="utf-8"))
revs = [p["rev"] for p in manifest["packages"] if p["name"] == "lean4export"]
if revs != [sys.argv[2]]:
    sys.exit(f"::error::comparator pins lean4export {revs}, expected {sys.argv[2]}")
PY
(cd "$out/comparator" && lake build --no-ansi comparator)
(cd "$out/comparator/.lake/packages/lean4export" && lake build --no-ansi)
got="$(git -C "$out/comparator/.lake/packages/lean4export" rev-parse HEAD)"
[[ "$got" == "$LEAN4EXPORT_REV" ]] \
  || { echo "::error::lean4export: expected $LEAN4EXPORT_REV, got $got" >&2; exit 1; }

# landrun.
fetch_rev https://github.com/Zouuup/landrun.git "$LANDRUN_REV" "$out/landrun-src"
if ! command -v go > /dev/null 2>&1; then
  if [[ ! -x "$out/go/bin/go" ]]; then
    tarball="$out/go$GO_VERSION.linux-amd64.tar.gz"
    curl -LsSf -o "$tarball" "https://go.dev/dl/go$GO_VERSION.linux-amd64.tar.gz"
    echo "$GO_SHA256  $tarball" | sha256sum -c -
    tar -xzf "$tarball" -C "$out"
    rm -f "$tarball"
  fi
  export PATH="$out/go/bin:$PATH"
fi
(cd "$out/landrun-src" && CGO_ENABLED=0 GOFLAGS=-mod=readonly go build -o "$out/landrun" ./cmd/landrun)

{
  echo "COMPARATOR_BIN=$out/comparator/.lake/build/bin/comparator"
  echo "COMPARATOR_LEAN4EXPORT=$out/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
  echo "COMPARATOR_LANDRUN=$out/landrun"
} > "$out/env"
cat "$out/env"
