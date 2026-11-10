#!/usr/bin/env bash
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

# Runs `leanprover/comparator` on each given config (default: `comparator/computational.json` and
# `comparator/symbolic.json`) concurrently, from the repository root, and fails unless every run
# exits 0 and prints comparator's verdict `Your solution is okay!`.
#
# Usage: comparator/run.sh [CONFIG.json ...]
#
# Needs `COMPARATOR_BIN`, `COMPARATOR_LEAN4EXPORT` and `COMPARATOR_LANDRUN` (written by
# `comparator/install-tools.sh` to `<out>/env`) and a built tree: comparator itself runs
# `lake build` of the challenge and solution modules (in a `landrun` sandbox that can write only
# `.lake/`), which must then be a no-op. Logs go to `COMPARATOR_LOG_DIR` (default: a temp dir).
set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

: "${COMPARATOR_BIN:?run comparator/install-tools.sh and source its env file}"
: "${COMPARATOR_LEAN4EXPORT:?run comparator/install-tools.sh and source its env file}"
: "${COMPARATOR_LANDRUN:?run comparator/install-tools.sh and source its env file}"
export COMPARATOR_LEAN4EXPORT COMPARATOR_LANDRUN

configs=("$@")
if [[ ${#configs[@]} -eq 0 ]]; then
  configs=(comparator/computational.json comparator/symbolic.json)
fi
log_dir="${COMPARATOR_LOG_DIR:-$(mktemp -d)}"
mkdir -p "$log_dir"

# `comparator` runs `lake build` inside `landrun` with only `<repo>/.lake/` writable and with
# `LAKE_RESTORE_ARTIFACTS` stripped. Warm `.lake/comparator-home/.cache/lake` and subpackage
# `.hash` files (`arm64-semantics/*/.lake/`, which `landrun` mounts read-only) once outside
# `landrun`, with the toolchain `bin/` on `PATH` so `lean`/`lake` do not look for `~/.elan`.
lean_prefix="$(lean --print-prefix)" || exit 1
export PATH="$lean_prefix/bin:$PATH"
comparator_home="$repo_root/.lake/comparator-home"
mkdir -p "$comparator_home"
read -r -a prewarm_targets < <(python3 -c 'import json,sys; print(*dict.fromkeys(json.load(open(p,encoding="utf-8"))[k] for p in sys.argv[1:] for k in ("challenge_module","solution_module")))' "${configs[@]}")
[[ ${#prewarm_targets[@]} -gt 0 ]] || exit 1
env -i PATH="$PATH" HOME="$comparator_home" LEAN_ABORT_ON_PANIC=1 \
  lake build --no-ansi "${prewarm_targets[@]}" || exit 1

# Kernel replay of the whole solution environment recurses deeply on the main thread.
ulimit -s 1048576 2> /dev/null || ulimit -s 524288 2> /dev/null || true
echo "comparator: stack limit $(ulimit -s) KiB, kernel $(uname -r), logs in $log_dir"

timer=()
if [[ -x /usr/bin/time ]]; then
  timer=(/usr/bin/time -v)
fi

pids=()
for cfg in "${configs[@]}"; do
  name="$(basename "$cfg" .json)"
  (
    t0=$SECONDS
    # Streams each line, prefixed with the elapsed time and the config, so that a run killed by
    # a timeout still shows which phase (build, export, comparison, kernel replay) it reached.
    env HOME="$comparator_home" "${timer[@]}" lake env "$COMPARATOR_BIN" "$cfg" 2>&1 \
      | while IFS= read -r line; do
          printf '[%5ds %s] %s\n' "$((SECONDS - t0))" "$name" "$line"
        done | tee "$log_dir/$name.log"
    rc=${PIPESTATUS[0]}
    echo "$rc" > "$log_dir/$name.rc"
    echo "$((SECONDS - t0))" > "$log_dir/$name.wall"
  ) &
  pids+=("$!")
done
for p in "${pids[@]}"; do
  wait "$p"
done

failed=0
summary="| Config | Theorems | Verdict | Wall (s) | Max RSS (GiB) |"$'\n'"| --- | ---: | --- | ---: | ---: |"
for cfg in "${configs[@]}"; do
  name="$(basename "$cfg" .json)"
  log="$log_dir/$name.log"
  rc="$(cat "$log_dir/$name.rc" 2> /dev/null || echo 1)"
  wall="$(cat "$log_dir/$name.wall" 2> /dev/null || echo '?')"
  n_thms="$(python3 -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["theorem_names"]))' "$cfg")"
  rss_kb="$(sed -n 's/^.*Maximum resident set size (kbytes): //p' "$log" | tail -n 1)"
  rss="?"
  [[ -n "$rss_kb" ]] && rss="$(awk -v k="$rss_kb" 'BEGIN { printf "%.1f", k / 1048576 }')"
  if [[ "$rc" == 0 ]] && grep -q '] Lean default kernel accepts the solution$' "$log" \
      && grep -q '] Your solution is okay!$' "$log"; then
    verdict=PASS
  else
    verdict="**FAIL (exit $rc)**"
    echo "::error::comparator $cfg failed (exit $rc); see the log above"
    failed=1
  fi
  summary+=$'\n'"| \`$cfg\` | $n_thms | $verdict | $wall | $rss |"
done

echo "$summary"
if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
  {
    echo
    echo '### Comparator (`leanprover/comparator`, `comparator/README.md`)'
    echo
    echo "$summary"
  } >> "$GITHUB_STEP_SUMMARY"
fi
exit "$failed"
