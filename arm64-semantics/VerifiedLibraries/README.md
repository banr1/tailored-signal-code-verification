# `VerifiedLibraries/` — Standalone Placeable Verified Libraries Package

`VerifiedLibraries/` (`package «verified-libraries»` in `VerifiedLibraries/lakefile.lean`) is the standalone Lake package for reusable, placement-generic (`Obj.PlacedLib` / `Obj.MultiPlacedLib`, zero concrete link addresses) machine-code specifications and proofs of standard C and Rust runtime libraries consumed across `CaseStudies/*` and downstream repositories.

## Package Layering & Isolation Invariant

```text
Arm64 < ProofLib < VerifiedLibraries < CaseStudies/<Name>
```

- `VerifiedLibraries/lakefile.lean` sets `srcDir := ".."` and depends **only** on `ProofLib` (`require prooflib from "../ProofLib"`), so Lake's `LEAN_PATH` makes it structurally impossible for `VerifiedLibraries` to import `CaseStudies/*`.
- Standalone case studies under `CaseStudies/` (e.g. [`CaseStudies/Hashbrown/`](../CaseStudies/Hashbrown/README.md)) may depend on `Arm64`, `ProofLib`, and `VerifiedLibraries`, **and are otherwise strictly pairwise independent of all other case studies** (`no CaseStudies.<A>.* -> CaseStudies.<B>.*` for `A != B`).

## Libraries in `VerifiedLibraries/`

1. **`VerifiedLibraries.Mallocng`** (`VerifiedLibraries/Mallocng/`):
   - Unmodified stock `musl` v1.2.5 `mallocng` allocator (`malloc`, `free`, `calloc`, `realloc`, `aligned_alloc`, `posix_memalign`) as the 24-block `VerifiedLibraries.mallocngLib : Obj.MultiPlacedLib`.
2. **`VerifiedLibraries.Musl`** (`VerifiedLibraries/Musl/`):
   - Placement-generic `musl` v1.2.5 AArch64 memory/string primitives (`memcpy`, `memset`, `memmove`, `memcmp`, `bcmp`, `memchr`, `memrchr` / `__memrchr`, `memccpy`, `mempcpy`, `memmem` extracted directly from `rustc 1.98.1`'s bundled `aarch64-unknown-linux-musl/lib/self-contained/libc.a` via `rust-lld -r`, plus `strlen`), compiler-rt outline atomics (`__aarch64_cas4_acq`, `__aarch64_swp4_rel`), and thread-local `errno` / syscall blocks (`___errno_location`, `__syscall_ret`, `__sccp`, `__syscall_cp`, `__aio_close`, `close`, `read`, `write`, `open`, `fstat`, `fstatat`).
3. **`VerifiedLibraries.RustStd`** (`VerifiedLibraries/RustStd/`):
   - Placement-generic Rust `core` / `alloc` / `std` runtime contracts, `Allocator` / `Vec<u8>` hook contracts & header/frame bridges, `OsString` / `argv` / `RawVec::grow_one` helpers, and compiled `aarch64-unknown-linux-musl` `std::io` / `std::fs` blocks (`is_interrupted`, `<Stderr as Write>::write_all`, `File::open_c`, `small_probe_read::<File>`, `run_with_cstr_allocating::<File>`).
4. **`VerifiedLibraries.SwissTable`** (`VerifiedLibraries/SwissTable/`):
   - Binary-free, untrusted pure SwissTable math shared by verified hash tables: control tags, `bucket_mask` capacity accounting, triangular probing over a 64-bit hash, NEON `v.8b` group-matching lemmas, and the generic `SwissTableInv` over a slot type `α` (see [`SwissTable/README.md`](./SwissTable/README.md)).

## Building & Checking

```bash
# Build all exported VerifiedLibraries targets standalone:
timeout 900 lake -d VerifiedLibraries build --no-ansi
```

