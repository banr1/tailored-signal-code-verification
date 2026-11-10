#!/usr/bin/env bash
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

# Build (or check) every generated test ELF from its committed sources.
#
# Thin wrapper over the per-family builders; each writes its ELFs to the committed path:
#   regression     Arm64/Testing/Regression/fixtures/*.elf       scripts/dev/elf-process-fixture --elf-process
#   rust-std       CaseStudies/Hashbrown/Testing/                 scripts/dev/elf-process-fixture --rust-std
#   elf-loader     Arm64/Testing/ElfLoaderDiff/bin/*.elf          scripts/elf-loader-diff build
#   process-e2e    Arm64/Testing/ProcessE2E/bin/*.elf             scripts/process-e2e build
#   syscall-cases  Arm64/Testing/SyscallDiff/bin/<case>.elf       scripts/syscall-diff-cases build
#   syscall-probe  Arm64/Testing/SyscallDiff/bin/syscall_probe.elf scripts/syscall-diff-cases probe
#
# Toolchains (see `Arm64/Testing/README.md#testing-dependencies`): Rust 1.98.1 with targets
# `aarch64-unknown-linux-musl` and `aarch64-unknown-linux-gnu` plus `rust-src` and
# `llvm-tools-preview`; zig 0.16.0 (its bundled clang also assembles the `elf-loader` corpus). A family whose toolchain is missing is
# reported as SKIPPED (the Lean tests that need its ELFs then report SKIPPED too), unless
# `--require-all` is given. Without zig, `elf-loader` still builds everything except
# `c_zig_o{0,2}.elf`.
#
# Usage:
#   scripts/build-test-elfs.sh [--check] [--require-all] [<family>...]
#
#   --check        rebuild into temporary directories and fail unless every ELF is byte-identical
#                  to the committed one (nothing is written).
#   --require-all  fail instead of skipping a family whose toolchain is missing.
#   <family>       restrict to the named families (default: all).
#
# Examples:
#   scripts/build-test-elfs.sh
#   scripts/build-test-elfs.sh --check --require-all
#   scripts/build-test-elfs.sh process-e2e syscall-probe
set -euo pipefail

usage() { sed -n '9,/^set -euo/p' "${BASH_SOURCE[0]}" | sed '$d; s/^# \{0,1\}//'; }

ALL_FAMILIES=(regression rust-std elf-loader process-e2e syscall-cases syscall-probe)
RUST_VERSION_PIN="1.98.1"
ZIG_VERSION_PIN="0.16.0"

check=0
require_all=0
families=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --check) check=1 ;;
    --require-all) require_all=1 ;;
    -h | --help) usage; exit 0 ;;
    -*) echo "unknown argument: $1" >&2; usage >&2; exit 2 ;;
    *)
      [[ " ${ALL_FAMILIES[*]} " == *" $1 "* ]] || { echo "unknown family: $1" >&2; exit 2; }
      families+=("$1")
      ;;
  esac
  shift
done
[[ ${#families[@]} -gt 0 ]] || families=("${ALL_FAMILIES[@]}")

cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Prints the reason a required tool is missing, or nothing when everything is present.
missing_zig() {
  if ! command -v zig >/dev/null; then
    echo "zig not found in PATH (install zig $ZIG_VERSION_PIN)"
  elif [[ "$(zig version)" != "$ZIG_VERSION_PIN" ]]; then
    echo "zig $(zig version) found; test ELFs are pinned to zig $ZIG_VERSION_PIN"
  fi
}
missing_rust_target() { # <target>
  local rustc
  if ! rustc="$(rustup which --toolchain "$RUST_VERSION_PIN" rustc 2>/dev/null)"; then
    echo "Rust $RUST_VERSION_PIN not installed (rustup toolchain install $RUST_VERSION_PIN)"
  elif [[ ! -d "$("$rustc" --print target-libdir --target "$1" 2>/dev/null)" ]]; then
    echo "Rust $RUST_VERSION_PIN lacks target $1 (rustup target add --toolchain $RUST_VERSION_PIN $1)"
  fi
}
missing_llvm() { # elf-loader assembles with zig's bundled clang, else llvm-mc
  command -v zig >/dev/null || command -v llvm-mc >/dev/null \
    || echo "neither zig nor llvm-mc found in PATH (install zig 0.16.0)"
}

missing_for() { # <family>: prints the first missing prerequisite, if any
  local m=""
  case "$1" in
    regression | syscall-cases) m="$(missing_zig)" ;;
    rust-std | process-e2e) m="$(missing_rust_target aarch64-unknown-linux-musl)" ;;
    elf-loader) m="$(missing_rust_target aarch64-unknown-linux-musl)"; [[ -n "$m" ]] || m="$(missing_llvm)" ;;
    syscall-probe) m="$(missing_rust_target aarch64-unknown-linux-gnu)" ;;
  esac
  printf '%s' "$m"
}

run_family() { # <family>
  local c=()
  [[ "$check" == 1 ]] && c=(--check)
  case "$1" in
    regression) scripts/dev/elf-process-fixture --elf-process "${c[@]}" ;;
    rust-std) scripts/dev/elf-process-fixture --rust-std "${c[@]}" ;;
    elf-loader) scripts/elf-loader-diff build "${c[@]}" ;;
    process-e2e) scripts/process-e2e build "${c[@]}" ;;
    syscall-cases) if [[ "$check" == 1 ]]; then scripts/syscall-diff-cases check; else scripts/syscall-diff-cases build; fi ;;
    syscall-probe) scripts/syscall-diff-cases probe "${c[@]}" ;;
  esac
}

ok=() skipped=() failed=()
for fam in "${families[@]}"; do
  echo "=== build-test-elfs: $fam" >&2
  reason="$(missing_for "$fam")"
  if [[ -n "$reason" ]]; then
    if [[ "$require_all" == 1 ]]; then
      echo "error: $fam: $reason" >&2
      failed+=("$fam")
    else
      echo "SKIPPED: $fam: $reason" >&2
      skipped+=("$fam")
    fi
    continue
  fi
  if run_family "$fam"; then ok+=("$fam"); else failed+=("$fam"); fi
done

mode=built
[[ "$check" == 1 ]] && mode=reproducible
echo "build-test-elfs: ${mode}: ${ok[*]:-none}; skipped: ${skipped[*]:-none}; failed: ${failed[*]:-none}"
[[ ${#failed[@]} -eq 0 ]]
