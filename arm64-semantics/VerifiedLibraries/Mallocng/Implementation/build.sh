#!/bin/sh
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

# Extract unmodified musl 1.2.5 mallocng object code from the pinned Rust 1.98.1
# aarch64-unknown-linux-musl sysroot's bundled self-contained/libc.a via partial
# relocatable linking (rust-lld -r), resolving the five SHN_COMMON tentative
# globals via common_bss.s without modifying or recompiling any musl C source.
set -eu

PINNED_RUSTC_PREFIX="rustc 1.98.1"
PINNED_LIBCA_SHA256="b03473b6f1efb72f700f561b4407a88885b37e0edb5cdb2a64de0df5499e813f"

RUSTC_BIN="${RUSTC:-rustc}"
RUSTC_VER="$("$RUSTC_BIN" --version 2>/dev/null || true)"
case "$RUSTC_VER" in
  "$PINNED_RUSTC_PREFIX"*)
    SYSROOT="$("$RUSTC_BIN" --print sysroot)"
    HOST_TRIPLE="$("$RUSTC_BIN" -vV | sed -n 's/^host: //p')"
    ;;
  *)
    if command -v rustup >/dev/null 2>&1; then
      RUSTC_BIN="$(rustup which --toolchain 1.98.1 rustc)"
      RUSTC_VER="$("$RUSTC_BIN" --version)"
      case "$RUSTC_VER" in
        "$PINNED_RUSTC_PREFIX"*) ;;
        *)
          echo "error: expected $PINNED_RUSTC_PREFIX, got $RUSTC_VER" >&2
          exit 1
          ;;
      esac
      SYSROOT="$("$RUSTC_BIN" --print sysroot)"
      HOST_TRIPLE="$("$RUSTC_BIN" -vV | sed -n 's/^host: //p')"
    else
      echo "error: expected $PINNED_RUSTC_PREFIX on PATH (got '$RUSTC_VER') and rustup is unavailable" >&2
      exit 1
    fi
    ;;
esac

LIBC_A="$SYSROOT/lib/rustlib/aarch64-unknown-linux-musl/lib/self-contained/libc.a"
if [ ! -f "$LIBC_A" ]; then
  echo "error: missing $LIBC_A (install target aarch64-unknown-linux-musl for rustc 1.98.1)" >&2
  exit 1
fi

ACTUAL_SHA256="$(sha256sum "$LIBC_A" | awk '{print $1}')"
if [ "$ACTUAL_SHA256" != "$PINNED_LIBCA_SHA256" ]; then
  echo "error: SHA-256 mismatch on $LIBC_A: expected $PINNED_LIBCA_SHA256, got $ACTUAL_SHA256" >&2
  exit 1
fi

LLD_BIN="$SYSROOT/lib/rustlib/$HOST_TRIPLE/bin/gcc-ld/ld.lld"
if [ ! -x "$LLD_BIN" ]; then
  echo "error: missing bundled rust-lld wrapper at $LLD_BIN" >&2
  exit 1
fi

ZIG_BIN="${ZIG:-zig}"
mkdir -p build

"$ZIG_BIN" cc -target aarch64-linux-musl -c common_bss.s -o build/common_bss.o

"$LLD_BIN" -r \
  -u malloc \
  -u __libc_malloc \
  -u free \
  -u __libc_free \
  -u calloc \
  -u __libc_calloc \
  -u realloc \
  -u __libc_realloc \
  -u reallocarray \
  -u aligned_alloc \
  -u memalign \
  -u posix_memalign \
  -u malloc_usable_size \
  "$LIBC_A" \
  build/common_bss.o \
  -o build/mallocng_libca.o
