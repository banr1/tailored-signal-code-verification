#!/usr/bin/env bash
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

# Download, checksum-verify, and unpack the upstream third-party sources into `third_party/`.
#
# No full upstream archive is trusted without verification: every upstream input is pinned here
# by URL and SHA-256 (archives), or by tag, commit and a SHA-256 over the tracked tree (git
# checkouts). A download that fails, or whose content differs from the pin (a moved tag, a
# re-rolled tarball, a compromised mirror), is a hard error: we only ever compile the code we
# verified.
#
# Usage:
#   scripts/fetch-upstream-sources.sh [--force] [--print-env] [TARGET...]
#
#   TARGET           musl musl-string hashbrown sail-arm fp-tools (plus additional campaign
#                    and specification-audit targets when `scripts/dev/fetch-campaign-sources.sh`
#                    is present), or `all`.
#                    Default: all configured non-opt-in targets.
#   --force          ignore stamps: re-verify the cache and re-unpack every target.
#   --print-env      print `NAME_SRC=<path>` on stdout.
#   -h, --help       show this help message and exit.
#
# Examples:
#   scripts/fetch-upstream-sources.sh
#   scripts/fetch-upstream-sources.sh musl hashbrown
#   scripts/fetch-upstream-sources.sh sail-arm fp-tools
#
# Archives are cached content-addressed in `$ARM64_UPSTREAM_CACHE` (default
# `${XDG_CACHE_HOME:-~/.cache}/arm64-verification-engine`), shared by all worktrees, and
# re-verified before every unpack. Archive targets are unpacked into the gitignored
# `third_party/<pkg>-<version>/` directories. A stamp `third_party/<pkg>-<version>/.fetched-<key>`
# (key = SHA-256 over the archive pin and the target's install function) makes re-runs a no-op.
set -euo pipefail
export LC_ALL=C

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CACHE="${ARM64_UPSTREAM_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/arm64-verification-engine}"

FORCE="${FORCE:-0}"
PRINT_ENV="${PRINT_ENV:-0}"
TARGETS=()

log() { echo "fetch-upstream-sources: $*" >&2; }
die() { log "error: $*"; exit 1; }

# ---------------------------------------------------------------------------
# Archive & Git helpers
# ---------------------------------------------------------------------------

# fetch_archive URL SHA256 [MIRROR_URL...]: download (or reuse from the cache) and verify; sets
# ARCHIVE to the path of the verified cached file. Sets a global rather than printing, so that
# `die` exits the script instead of a command-substitution subshell.
#
# The URLs are tried in order until one yields content matching SHA256; the pin, not the
# host, is what is trusted, so a mirror adds availability but no trust. The cache file name is
# derived from the primary URL so the cache key does not depend on which URL served the bytes.
fetch_archive() {
  local url="$1" sha="$2"
  shift 2
  local file="$CACHE/archives/$sha-${url##*/}"
  mkdir -p "$CACHE/archives"
  if [ ! -f "$file" ]; then
    local tmp candidate got
    tmp="$(mktemp "$file.XXXXXX.part")"
    for candidate in "$url" "$@"; do
      log "downloading $candidate"
      # Short connect timeout so a dead host fails over to the next URL quickly.
      if ! curl -fsSL --retry 1 --connect-timeout 15 -o "$tmp" "$candidate"; then
        log "download of $candidate failed"
        continue
      fi
      if echo "$sha  $tmp" | sha256sum --check --status; then
        mv -f "$tmp" "$file"
        break
      fi
      got="$(sha256sum "$tmp" | cut -d' ' -f1)"
      log "checksum mismatch for $candidate: expected sha256 $sha, got $got (discarded)"
    done
    if [ ! -f "$file" ]; then
      rm -f "$tmp"
      die "could not download $url (or any mirror) with sha256 $sha"
    fi
  fi
  if ! echo "$sha  $file" | sha256sum --check --status; then
    local got
    got="$(sha256sum "$file" | cut -d' ' -f1)"
    rm -f "$file"
    die "checksum mismatch for $url: expected sha256 $sha, got $got (removed from cache)"
  fi
  ARCHIVE="$file"
}

# with_stamp TARGET SHA256 INSTALL_FN DIR: run INSTALL_FN (which prints the installed paths,
# relative to DIR under `third_party/`) unless the stamp exists and all those paths do. The stamp
# key covers both the archive SHA-256 and the source of INSTALL_FN (`declare -f`), so editing a
# target's install list (for example adding a file to copy) invalidates the stamp; keying on
# the archive alone would accept the old stamp and silently never install the new file.
with_stamp() {
  local target="$1" sha="$2" install_fn="$3"
  local dir="$4"
  local key
  key="$(printf '%s\n%s\n' "$sha" "$(declare -f "$install_fn")" | sha256sum | cut -d' ' -f1)"
  local stamp="$dir/.fetched-$key"
  if [ "$FORCE" = 0 ] && [ -f "$stamp" ]; then
    local ok=1 f
    while IFS= read -r f; do
      [ -e "$dir/$f" ] || { ok=0; break; }
    done < "$stamp"
    [ "$ok" = 1 ] && return 0
  fi
  mkdir -p "$dir"
  rm -f "$dir"/.fetched-*
  # Not a command substitution: a failing `die` inside INSTALL_FN must exit the script.
  "$install_fn" "$dir" > "$stamp.tmp"
  mv -f "$stamp.tmp" "$stamp"
  log "$target: verified and unpacked ($(wc -l < "$stamp") files)"
}

# unpack ARCHIVE DEST: extract ARCHIVE (top-level directory stripped) into a fresh DEST.
unpack() {
  rm -rf "$2"
  mkdir -p "$2"
  tar -xf "$1" -C "$2" --strip-components=1
}

# install_rel SRC_DIR DST_DIR REL...: copy each REL (a glob relative to SRC_DIR) to the same
# relative path under DST_DIR, printing the destination paths.
install_rel() {
  local src="$1" dst="$2" pat f
  shift 2
  for pat in "$@"; do
    local matched=0
    for f in "$src"/$pat; do
      [ -e "$f" ] || continue
      matched=1
      local rel="${f#"$src"/}"
      mkdir -p "$dst/$(dirname "$rel")"
      cp -f "$f" "$dst/$rel"
      echo "$rel"
    done
    [ "$matched" = 1 ] || die "upstream archive has no file matching \`$pat\`"
  done
}

# tree_sha256 DIR: SHA-256 over the path, type and content of every file git tracks in DIR.
tree_sha256() {
  (
    cd "$1"
    local mode _obj _stage path
    local -a files=()
    {
      while IFS=$' \t' read -r -d '' mode _obj _stage path; do
        case "$mode" in
          120000) printf 'symlink %s  %s\n' "$(readlink -- "$path")" "$path" ;;
          160000) printf 'gitlink %s  %s\n' "$_obj" "$path" ;;
          *) files+=("$path") ;;
        esac
      done < <(git ls-files -s -z)
      printf '%s\0' "${files[@]}" | xargs -0 sha256sum --
    } | LC_ALL=C sort | sha256sum | cut -d' ' -f1
  )
}

# fetch_git NAME REPO_URL TAG COMMIT TREE_SHA256 ENV_VAR
fetch_git() {
  local name="$1" url="$2" tag="$3" commit="$4" tree="$5" env_var="$6"
  local dest="$CACHE/git/$name-$commit"
  local stamp="$dest/.git/arm64-verified-$tree"
  if [ "$FORCE" = 1 ] || [ ! -f "$stamp" ]; then
    mkdir -p "$CACHE/git"
    local tmp
    tmp="$(mktemp -d "$CACHE/git/.$name.XXXXXX")"
    log "cloning $url at $tag"
    git -c init.defaultBranch=main init -q "$tmp"
    git -C "$tmp" config core.autocrlf false
    if ! git -C "$tmp" fetch -q --depth 1 "$url" "+refs/tags/$tag:refs/tags/$tag"; then
      rm -rf "$tmp"
      die "fetching $url tag $tag failed"
    fi
    git -C "$tmp" -c advice.detachedHead=false checkout -q "refs/tags/$tag^{commit}"
    local got_commit got_tree
    got_commit="$(git -C "$tmp" rev-parse HEAD)"
    if [ "$got_commit" != "$commit" ]; then
      rm -rf "$tmp"
      die "$name tag $tag resolves to $got_commit, expected $commit (was the tag moved?)"
    fi
    got_tree="$(tree_sha256 "$tmp")"
    if [ "$got_tree" != "$tree" ]; then
      rm -rf "$tmp"
      die "$name $tag tree checksum mismatch: expected sha256 $tree, got $got_tree"
    fi
    touch "$tmp/.git/arm64-verified-$tree"
    if [ -e "$dest" ]; then
      rm -rf "$dest.stale"
      mv -T "$dest" "$dest.stale" 2>/dev/null || true
      rm -rf "$dest.stale"
    fi
    mv -T "$tmp" "$dest" 2>/dev/null || rm -rf "$tmp"  # lost a race: identical content
    log "$name: verified $tag ($commit)"
  fi
  [ "$PRINT_ENV" = 1 ] && echo "$env_var=$dest"
  return 0
}

lock_and() {  # serialize concurrent runs in one worktree (e.g. two `lake` processes)
  if command -v flock >/dev/null; then
    mkdir -p "$ROOT/.lake"
    exec 9>"$ROOT/.lake/fetch-upstream-sources.lock"
    flock 9
  fi
  "$@"
}

# ---------------------------------------------------------------------------
# Release targets (`musl`, `hashbrown`, `sail-arm`, `fp-tools`)
# ---------------------------------------------------------------------------

# --- musl 1.2.5 (`third_party/musl-1.2.5`) -------------------------------------
MUSL_URL="${MUSL_URL:-https://musl.libc.org/releases/musl-1.2.5.tar.gz}"
# Debian's `.orig.tar.gz` is the byte-identical upstream release tarball (same SHA-256).
MUSL_MIRROR_URL="${MUSL_MIRROR_URL:-https://deb.debian.org/debian/pool/main/m/musl/musl_1.2.5.orig.tar.gz}"
MUSL_SHA256="a9a118bbe84d8764da0ea0d28b3ab3fae8477fc7e4085d90102b8596fc7c75e4"
install_musl() {
  local dir="$1" up="$1/upstream"
  fetch_archive "$MUSL_URL" "$MUSL_SHA256" "$MUSL_MIRROR_URL"
  unpack "$ARCHIVE" "$up"
  # Verify expected `src/string/` files exist in `upstream/`.
  local s
  for s in \
    src/string/aarch64/memcpy.S \
    src/string/aarch64/memset.S \
    src/string/memcmp.c \
    src/string/bcmp.c \
    src/string/strlen.c \
    src/string/strncmp.c
  do
    [ -f "$up/$s" ] || die "musl archive has no \`$s\`"
    echo "upstream/$s"
  done
}

ensure_musl() {
  with_stamp musl "$MUSL_SHA256" install_musl "$ROOT/third_party/musl-1.2.5"
}

# --- hashbrown 0.17.1 (`third_party/hashbrown-0.17.1`) -------------------------
fetch_hashbrown() {
  # `third_party/hashbrown-0.17.1/` is committed in the repository; this target verifies that
  # `third_party/hashbrown-0.17.1/` matches the pinned upstream `v0.17.1` git checkout
  # (`c62a63a61b7caf2de8f9ecb7b06a66b0ab6bdf3d`) byte-for-byte.
  local tp_dir="$ROOT/../third_party/hashbrown-0.17.1"
  local cache_dir="$CACHE/git/hashbrown-c62a63a61b7caf2de8f9ecb7b06a66b0ab6bdf3d"
  PRINT_ENV=0 fetch_git hashbrown https://github.com/rust-lang/hashbrown.git v0.17.1 \
    c62a63a61b7caf2de8f9ecb7b06a66b0ab6bdf3d \
    32c63abe2b8df08d35a7befabb9d8683d56277bb16348e7b1d3a1cbe47523ae0 HASHBROWN_SRC
  [ -d "$tp_dir" ] || die "committed directory \`$tp_dir\` is missing"
  local f rel count=0
  while IFS= read -r -d '' f; do
    rel="${f#"$tp_dir"/}"
    [ -f "$cache_dir/$rel" ] || die "unexpected file \`$rel\` in \`$tp_dir\` (not in upstream v0.17.1)"
    cmp -s "$f" "$cache_dir/$rel" || die "\`$tp_dir/$rel\` differs from upstream hashbrown v0.17.1"
    count=$((count + 1))
  done < <(find "$tp_dir" -type f -print0)
  while IFS= read -r -d '' f; do
    rel="${f#"$cache_dir"/}"
    [ -f "$tp_dir/$rel" ] || die "missing upstream file \`$rel\` in \`$tp_dir\`"
  done < <(find "$cache_dir/Cargo.toml" "$cache_dir/LICENSE-MIT" "$cache_dir/LICENSE-APACHE" "$cache_dir/src" "$cache_dir/benches" -type f -print0)
  log "hashbrown: verified third_party/hashbrown-0.17.1 matches upstream v0.17.1 ($count files)"
  [ "$PRINT_ENV" = 1 ] && echo "HASHBROWN_SRC=$tp_dir"
  return 0
}

# --- sail-arm (rems-project/sail-arm @ 1bf2e55 + rems-project/sail @ 0.17.1) --
# Official Sail Armv9.4-A C snapshot (`arm-v9.4-a/snapshots/c/armv9.c.gz`) and Sail 0.17.1 C
# runtime (`lib/`) used by `tools/run-trusted-tests` for differential ISA validation.
SAIL_ARMV9_URL="https://raw.githubusercontent.com/rems-project/sail-arm/1bf2e5574ba9d704639a28401b6a387dcb113cae/arm-v9.4-a/snapshots/c/armv9.c.gz"
SAIL_ARMV9_SHA256="44b10531cb18ebbaebf8ac63f1b7a2f73950e693aeef874f216e759f31463d6e"
SAIL_RTS_URL="https://github.com/rems-project/sail/archive/refs/tags/0.17.1.tar.gz"
SAIL_RTS_SHA256="b874093312c13dd4eb9ca7ad45083c3278b7ebd26736d6310b6a3faa73e0c281"
SAIL_CACHE_ID="${SAIL_ARMV9_SHA256:0:16}-${SAIL_RTS_SHA256:0:16}"
fetch_sail_arm() {
  local dest="$CACHE/sail-armv9/src-$SAIL_CACHE_ID"
  local stamp="$dest/.unpacked"
  local rts_files=(sail.h sail.c rts.h rts.c elf.h elf.c sail_failure.h sail_failure.c sail_state.h sail_coverage.h)
  local ok=1 f
  if [ "$FORCE" = 0 ] && [ -f "$stamp" ] && [ -f "$dest/armv9.c" ]; then
    for f in "${rts_files[@]}"; do
      [ -f "$dest/$f" ] || { ok=0; break; }
    done
  else
    ok=0
  fi
  if [ "$ok" = 0 ]; then
    fetch_archive "$SAIL_ARMV9_URL" "$SAIL_ARMV9_SHA256"
    local armv9_gz="$ARCHIVE"
    fetch_archive "$SAIL_RTS_URL" "$SAIL_RTS_SHA256"
    local sail_tar="$ARCHIVE"
    mkdir -p "$CACHE/sail-armv9"
    local tmp
    tmp="$(mktemp -d "$CACHE/sail-armv9/.src.XXXXXX")"
    gzip -dc "$armv9_gz" > "$tmp/armv9.c"
    mkdir -p "$tmp/sail-rts"
    tar -xzf "$sail_tar" -C "$tmp/sail-rts" --strip-components=1
    for f in "${rts_files[@]}"; do
      [ -f "$tmp/sail-rts/lib/$f" ] || { rm -rf "$tmp"; die "sail 0.17.1 archive missing lib/$f"; }
      cp -f "$tmp/sail-rts/lib/$f" "$tmp/$f"
    done
    rm -rf "$tmp/sail-rts"
    touch "$tmp/.unpacked"
    rm -rf "$dest"
    mv -T "$tmp" "$dest" 2>/dev/null || rm -rf "$tmp"
    log "sail-arm: verified and unpacked Armv9.4-A C snapshot + Sail 0.17.1 runtime"
  fi
  mkdir -p "$ROOT/third_party"
  ln -sfn "$dest" "$ROOT/third_party/sail-armv9"
  [ "$PRINT_ENV" = 1 ] && echo "SAIL_ARMV9_SRC=$dest"
  return 0
}

# --- fp-tools (SoftFloat 3e, TestFloat 3e, IBM FPgen, Linaro RISU) ------------
SOFTFLOAT3_URL="https://github.com/ucb-bar/berkeley-softfloat-3/archive/a0c6494cdc11865811dec815d5c0049fba9d82a8.tar.gz"
SOFTFLOAT3_SHA256="1f719bcc8878be9627f6cfc44a0d6dbddf32bacc70ac81193bcbf2c62f97cbe9"
TESTFLOAT3_URL="https://github.com/ucb-bar/berkeley-testfloat-3/archive/a9c849f1b0eb0264b626d9686ffae167d996e3be.tar.gz"
TESTFLOAT3_SHA256="54852fd1d11f0109011e54d69952cda097d3c49709ce46e4800353a6e8c764c3"
FPGEN_URL="https://github.com/sergev/ieee754-test-suite/archive/12e883a0c7b826976a8f1243318ac4b7626a0ffc.tar.gz"
FPGEN_SHA256="176d02b796d1df2511642a4cfb1eb01b14a4785d1a9c5e256740c73660fdd8df"
RISU_URL="https://github.com/Xaltotun/risu/archive/4bc854b249d9375771a07e4f1f45618b2779a58e.tar.gz"
RISU_SHA256="6329f2e9d0f9407ca54454bb63a323b624375966931804e28b62b7f8fa25ee87"
FP_TOOLS_CACHE_ID="${SOFTFLOAT3_SHA256:0:12}-${TESTFLOAT3_SHA256:0:12}-${FPGEN_SHA256:0:12}-${RISU_SHA256:0:12}"
fetch_fp_tools() {
  local base="$CACHE/fp-tools"
  local stamp="$base/.fetched-$FP_TOOLS_CACHE_ID"
  if [ "$FORCE" = 1 ] || [ ! -f "$stamp" ] || [ ! -f "$base/softfloat3/source/include/softfloat.h" ] || [ ! -f "$base/testfloat3/source/testfloat_gen.c" ] || [ ! -f "$base/risu/aarch64.risu" ]; then
    fetch_archive "$SOFTFLOAT3_URL" "$SOFTFLOAT3_SHA256"
    local sf_tar="$ARCHIVE"
    fetch_archive "$TESTFLOAT3_URL" "$TESTFLOAT3_SHA256"
    local tf_tar="$ARCHIVE"
    fetch_archive "$FPGEN_URL" "$FPGEN_SHA256"
    local fp_tar="$ARCHIVE"
    fetch_archive "$RISU_URL" "$RISU_SHA256"
    local risu_tar="$ARCHIVE"
    mkdir -p "$base"
    unpack "$sf_tar" "$base/softfloat3"
    cp -f "$base/softfloat3/source/8086-SSE/s_bf16UIToCommonNaN.c" \
          "$base/softfloat3/source/8086-SSE/s_commonNaNToBF16UI.c" \
          "$base/softfloat3/source/ARM-VFPv2/"
    sed -i '/#define defaultNaNF32UI/i #define softfloat_isSigNaNBF16UI( uiA ) ((((uiA) \& 0x7FC0) == 0x7F80) \&\& ((uiA) \& 0x003F))\nvoid softfloat_bf16UIToCommonNaN( uint_fast16_t uiA, struct commonNaN *zPtr );\nuint_fast16_t softfloat_commonNaNToBF16UI( const struct commonNaN *aPtr );' \
          "$base/softfloat3/source/ARM-VFPv2/specialize.h"
    unpack "$tf_tar" "$base/testfloat3"
    unpack "$fp_tar" "$base/fpgen"
    unpack "$risu_tar" "$base/risu"
    touch "$stamp"
    log "fp-tools: verified and unpacked SoftFloat 3e, TestFloat 3e, IBM FPgen, and Linaro RISU"
  fi
  mkdir -p "$ROOT/third_party"
  ln -sfn "$base" "$ROOT/third_party/fp-tools"
  [ "$PRINT_ENV" = 1 ] && echo "FP_TOOLS_DIR=$base"
  return 0
}

run_release_target() {
  case "$1" in
    musl|musl-string) ensure_musl ;;
    hashbrown) fetch_hashbrown ;;
    sail-arm) fetch_sail_arm ;;
    fp-tools) fetch_fp_tools ;;
    *) return 1 ;;
  esac
}

if [ "${FETCH_UPSTREAM_LIB_ONLY:-0}" = 1 ]; then
  return 0
fi

ORIG_ARGS=("$@")
NEED_CAMPAIGN_SCRIPT=0
SAW_ALL=0

while [ $# -gt 0 ]; do
  case "$1" in
    --force) FORCE=1 ;;
    --print-env) PRINT_ENV=1 ;;
    --tree-sha256) tree_sha256 "$2"; exit 0 ;;
    -h|--help) sed -n '2,/^set -euo/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 0 ;;
    all) SAW_ALL=1 ;;
    -*) die "unknown option \`$1\`" ;;
    musl|musl-string|hashbrown|sail-arm|fp-tools) TARGETS+=("$1") ;;
    *)
      NEED_CAMPAIGN_SCRIPT=1
      TARGETS+=("$1")
      ;;
  esac
  shift
done

CAMPAIGN_SCRIPT="$ROOT/scripts/dev/fetch-campaign-sources.sh"
if [ "$SAW_ALL" = 1 ] || [ ${#TARGETS[@]} -eq 0 ] || [ "$NEED_CAMPAIGN_SCRIPT" = 1 ]; then
  if [ -x "$CAMPAIGN_SCRIPT" ]; then
    exec "$CAMPAIGN_SCRIPT" "${ORIG_ARGS[@]}"
  fi
  if [ "$NEED_CAMPAIGN_SCRIPT" = 1 ]; then
    for t in "${TARGETS[@]}"; do
      case "$t" in
        musl|musl-string|hashbrown|sail-arm|fp-tools) ;;
        *) die "unknown target \`$t\`" ;;
      esac
    done
  fi
  DEFAULT_TARGETS=(musl hashbrown sail-arm fp-tools)
  TARGETS=("${DEFAULT_TARGETS[@]}")
fi

main() {
  local t
  for t in "${TARGETS[@]}"; do
    run_release_target "$t" || die "unknown target \`$t\`"
  done
}

lock_and main
