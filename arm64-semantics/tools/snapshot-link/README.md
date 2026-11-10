# `snapshot-link`: link an exported image into a runnable executable (`[OUTSIDE TCB]`)

`snapshot-link` builds the static AArch64 executable that [`proc-snapshot`](../proc-snapshot/README.md)
runs. Its image part is the `Arm64.Obj.LinkedImage` that `rust-obj2lean` exports for the same
`translation.toml`, loaded at `--base`. Nothing it produces is trusted. The snapshot records
whatever the loader actually mapped, and Lean proofs compare those bytes with the exported image.

## Usage

```bash
cargo run --release --locked --manifest-path tools/Cargo.toml --bin snapshot-link -- \
  --config Implementation/<lib>/translation.toml --out-dir out --stubs zero \
  [--branch-stubs memcpy,memset,memmove,memcmp,bcmp] \
  [--musl-string | --native-objects Implementation/<rt>/translation.toml] \
  [--native-only memcpy,memset,memmove,memcmp,bcmp] \
  [--page-separate-data] [--base 0x400000] [--main-c main.c | --main-rust Cargo.toml] \
  [--strip-runtime-debug] [--check-std-toolchain] \
  [--expect-code Examples/Generated/<Obj>.code.bin --expect-data Examples/Generated/<Obj>.data.bin]
```

The command writes `out/prog` and `out/link.json`, which records the section addresses, the stub
addresses and the extern each stub stands for.

### Several images in one executable

Repeat `--config` to link several pre-verified images into one executable, for example a runtime
image and a library image that calls it:

```bash
snapshot-link \
  --config Implementation/my_rt/translation.toml  --base 0x400000 \
  --config Implementation/my_lib/translation.toml --base 0x480000 \
  --main-rust Implementation/my_cli/Cargo.toml --out-dir out
```

- `--base`, `--expect-code` and `--expect-data` pair with the `--config` at the same position
  (give them in the same order; a trailing image may omit `--base`). An image without a `--base`
  is placed automatically: the first at `0x400000`, a later one at the first page boundary after
  every earlier image. Images must not overlap, and every base must be page aligned and at least
  one page above zero. The ELF and program headers go in the page below the lowest image.
- Each image keeps the exact bytes `rust-obj2lean` exported for it, at `base + offset`. Image 0
  uses the same section and symbol names as a single-image link, so a one-image link is unchanged;
  image `k > 0` uses `.img<k>.*` sections and its own `PT_LOAD` segments.
- An extern function of one image that another image exports branches to that definition (with
  `--stubs branch` or `--branch-stubs`); the remaining externs go to `main`, native objects, and
  the C runtime as usual. A global symbol defined by two images, an extern function that another
  image defines as data, and an extern data object that another image defines are errors.
- `main` (`--main-c` or `--main-rust`), optional native objects (`--native-objects` /
  `--musl-string`), and the C runtime are linked after the highest image and can call any image's
  global symbols. The runtime is probed by linking `main` alone, so a `--main-c` driver declares
  the image functions it calls `__attribute__((weak))`.
- `link.json` keeps the single-image top-level fields (`config`, `base`, `image`, `stubs`) for
  image 0 and adds `images`: per image, `config`, `base`, `image` (lengths and SHA-256s),
  `sections` (`text`, `data`, `got`, `end` addresses, plus `rodata` when `page_separate_data` is
  enabled), `stubs` (`extern`, `off`, `addr`, `definedBy`: the defining image's index or
  `"runtime"`, and the branch `target`) and `extData`. A one-image link has no `images` field.

### Ordinary Rust `std` binary crates

When `--main-rust <Cargo.toml>` points to an ordinary safe Rust `std` binary crate (`src/main.rs`
or `[[bin]]`, rather than a `[lib] crate-type = ["staticlib"]` driver), `--config` may specify `0`
or more pre-verified `translation.toml` images:

```bash
snapshot-link --check-std-toolchain
snapshot-link --main-rust Implementation/my_app/Cargo.toml --out-dir out --name my_app.elf
```

- **Pinned toolchain & runtime:** verifies `rustc 1.98.1` (`48a229ceaefd4985c50990b14116b6d856af0985`,
  LLVM `22.1.8`), `rust-src`, bundled `rust-lld`, and exact SHA-256 digests of the bundled
  `aarch64-unknown-linux-musl` `self-contained` files (`crt1.o`, `crti.o`, `crtbegin.o`, `libc.a`,
  `libunwind.a`, `crtend.o`, `crtn.o`), then stages stripped deterministic copies into `work/runtime/`.
- **Manifest & source guards:** rejects `[patch]`, `.cargo/config*`, `build.rs`, native `.c`/`.h`/`.s`/`.S`
  files (excluding `vendor/`), `#![no_std]`, and missing `#![forbid(unsafe_code)]`, and requires
  `[profile.release]` with `opt-level = 2`, `codegen-units = 1`, and `lto = "fat"` (or `true`).
- **Build & link:** compiles a single LTO object under `-Zbuild-std=std,panic_abort`,
  `-Cpanic=immediate-abort`, `-Crelocation-model=static`, deterministic codegen flags, and host-path
  remaps; weakens any symbol already exported by `--config` images; bridges internalized
  `___rustc::__rust_*` global-allocator shims to `libc.a` when linking `#![no_std]` + `alloc`
  images; links page-disjoint W^X segments with `rust-lld`; and checks `Arm64.Process.ElfImage.parse`
  invariants plus zero `gimli` / `_Unwind_Backtrace` / `sigaltstack` symbols (`verify::check_std_elf`),
  recording `"stdProfile"` in `link.json`.

## Recipe

1. Extract and link the objects exactly as `rust-obj2lean` does (same `.o` files, no recompilation).
2. Rename each extern reference to a per-stub symbol (`llvm-objcopy --redefine-sym`), and
   assemble one 4-byte stub per extern with the pinned `zig cc`. `--stubs zero` gives `.word 0`,
   which is byte-identical to the exported image; `--stubs branch` gives `b <real function>`;
   `--stubs mixed` (or `--stubs zero --branch-stubs <names>`) emits `b <real function>` only for
   the selected externs (rejected if any name is absent from the image's extern stubs) and `.word 0`
   for the rest. When `--native-objects` is passed, selected `[[native_objects]]` are compiled with
   the `rust-obj2lean` compiler and flag pipeline; when `--musl-string` is passed, selected `.lo`
   members (`memcpy,memset,memmove,memcmp,bcmp` by default, or any `--native-only` subset of the 10
   `VerifiedLibraries/Musl` members) are extracted directly from the pinned Rust 1.98.1 bundled
   `aarch64-unknown-linux-musl` `self-contained/libc.a` (`SHA-256 = b03473b6...`) without `zig cc`
   and linked before the runtime archives (failing if any strong global symbol collides with
   `--main-c`).
3. Compile a minimal `main.c` with `zig cc` and take musl's crt objects and archives from its
   link line. With `--strip-runtime-debug` (off by default so committed ELF fixtures do not
   change), stage copies of those `.o`/`.a` inputs with debug sections stripped via `llvm-objcopy`
   before linking: with a cold cache, `zig` compiles `crt1.o` and its runtime archives with DWARF
   whose `DW_AT_comp_dir` depends on the working directory, leaving a CWD-length-dependent local
   `$d` symbol value in `.symtab` after `ld.lld --strip-debug`, and writes full cache paths in
   the `//` string table of its runtime `.a` archives. Staging strips `.debug_*` and normalizes
   archive member names to basenames before linking so both the linked executable and all staged
   `inputs[].sha256` entries are independent of `zig`'s cache location/state and CWD.
4. Link with `ld.lld -static -no-pie --no-gc-sections --icf=none --no-relax -z norelro` and a
   generated linker script. By default (`page_separate_data = false`), the script pins every image
   section at `base + offset` in 2 `PT_LOAD` segments (`imgtext` `r-x`, `imgdata` `r--`/`rw-`).
   When `page_separate_data = true` in `translation.toml` (or `--page-separate-data` on the CLI),
   the script places image sections on page-disjoint `PT_LOAD` segments (`PF_R | PF_X` code, `PF_R`
   read-only data, `PF_R | PF_W` writable data / bss / extern data, and `PF_R` GOT, with explicit
   file zero-fill on read-only and GOT pages) and places native objects and musl after the image.
5. Check the result with `verify.rs` (`check_images`, for every image at its base):
   - code bytes (a branch stub must encode `B <target>` to the address of the image that defines
     its extern, or else of the extern's definition outside every image, preferring a global or
     weak symbol; a same-named symbol inside an image is never the target), relocated data, bss,
     GOT, and symbol addresses;
   - segment permissions (and, when `page_separate_data` is enabled, exact `PF_R | PF_X` / `PF_R` /
     `PF_R | PF_W` flags, `p_filesz` zero-fill coverage, zero mixed `ro`/`rw` pages, and
     page-disjoint `PT_LOAD` segments), non-overlap with runtime sections, and non-overlapping
     images.

## Stock link and relocation-site census

`--stock` links the objects with plain `ld.lld` defaults instead of pinning a layout. It produces the
kind of executable a layout-generic proof is checked against.

```bash
snapshot-link --stock [--stock-keep-library] [--stock-lld-arg=<arg>]... \
  [--stock-native-object <obj.o>]... \
  --config <translation.toml>... \
  (--main-c <main.c> | --main-rust <staticlib Cargo.toml> \
   | --main-rust <std binary Cargo.toml> [--stock-self-contained-dir <dir>]) \
  --out-dir <dir> --name <exe>
```

- **Inputs.** The library objects are the exact relocatable objects `rust-obj2lean` extracts for
  each `--config`, unrenamed and with no stubs, linked in `--config` order. With `--main-c` or a
  `staticlib` `--main-rust`, they are combined with `main` and the musl runtime of a `zig cc`
  link.
- **Rust `std` binary `--main-rust`.** An ordinary safe Rust `std` binary crate is compiled to
  `work/main_rust.o` + `work/compiler_builtins.a`. The crate guards and the pinned
  `-Zbuild-std=std,panic_abort` profile are the same as in
  [Ordinary Rust `std` binary crates](#ordinary-rust-std-binary-crates). It is linked against
  **rustc's own musl `self-contained` runtime**, not `zig`'s musl. That runtime is `crt1.o`,
  `crti.o`, `crtbegin.o`, `libc.a`, `libunwind.a`, `crtend.o` and `crtn.o`, taken from the pinned
  sysroot's `lib/rustlib/aarch64-unknown-linux-musl/lib/self-contained/` or from
  `--stock-self-contained-dir <dir>`.
  - Before anything is built, each file must match its pinned SHA-256
    (`std_profile::SELF_CONTAINED_CHECKSUMS`). It is then copied unmodified to
    `work/self-contained/`.
  - Globals that `main_rust.o` and a `--config` object both define are weakened in `main_rust.o`,
    so the extracted definitions are the ones linked. The set is computed from the objects as
    emitted into `work/` (a trimmed sysroot object as its trim, not the whole member).
    `stock-link.json` lists them under `stdBin.weakenedInMain`.
  - `ld.lld` also writes `work/why-extract.tsv` (`--why-extract=`) and `work/link.map` (`-Map=`),
    and reports removed sections (`--print-gc-sections`). From them `stock-link.json` records
    `stdBin.archiveMembers`: every archive member lld extracted, the reference and symbol that
    extracted it, its input sections that survive `--gc-sections` with their sizes (`retained`),
    and those `--gc-sections` removed (`removed`).
  - The parser fails closed (`stock_std_audit::parse_members`). Both headers must match exactly,
    every map line must be an output-section, input-section or symbol line, at least one member
    must be extracted and at least one archive section retained, and every extracted member must
    retain or have removed at least one section. A changed `ld.lld` output format is an error,
    never an empty (vacuously passing) retained set.
  - **Unwind audit (fails closed).** `libunwind.a` members may be extracted (`rust_eh_personality`
    references `_Unwind_*`), but none of their sections may survive `--gc-sections`, and every
    `.symtab` name other than `STT_FILE` source names matching `stock_std_audit::UNWIND_DENY` (`_Unwind_*`, `__register_frame*`,
    `__deregister_frame*`, `unw_*`, `libunwind`) must be an entry of `UNWIND_ALLOW` in its allowed
    form. The only allowed entries are crtbegin.o's weak undefined `__register_frame_info` /
    `__deregister_frame_info`, which link no code. `stdBin.unwindAudit.allowed` lists those
    present, with the reason.
  - For the hooked-extern check of trimmed sysroot objects, `compiler_builtins.a` counts as a Rust
    archive, not as part of the C runtime.
  - Link order:
    1. `crt1.o crti.o crtbegin.o`;
    2. native objects;
    3. library objects;
    4. `--start-group main_rust.o libc.a compiler_builtins.a libunwind.a --end-group`;
    5. `crtend.o crtn.o`.
- **`--stock-native-object <obj.o>` (repeatable).** A relocatable little-endian AArch64 ELF64
  object, for example an assembled `.S` shim. It is checked and copied to
  `work/native/<file name>`; file names must be distinct. It is linked after the startup objects
  and a C `main`, before the library objects. A strong symbol that collides with `main` or a
  library object is a link error. For the hooked-extern check of trimmed sysroot objects, a native
  object is a stub object: it may define a hooked extern (for example a hand-written shim).
- **Hooked externs of trimmed sysroot objects** (`stock_hooks.rs`). These are the externs of a
  `--config` that has a trimmed `[[sysroot_objects]]` entry.
  - Before the link, no non-runtime archive may define one. The single exception is an
    `STB_WEAK` archive definition of a name that a stub object defines `STB_GLOBAL`: an object's
    global definition always wins over a weak one. A weak stub never qualifies.
    `trimmedSysrootObjects.weakArchiveShadowed` lists these archive definitions.
  - A sibling `--config` image may define a hooked extern only under two conditions. The defining
    symbol must be one of that image's declared exports (`[placed] exports` or
    `[[sysroot_objects]] roots`, raw or demangled). Each export must resolve to exactly one
    defined symbol of the image. And the image must not list the name as an extern itself.
  - After the link, the `--trace-symbol` output must have exactly one `definition of` line per
    hooked extern, and it must come from a stub object, the C runtime, or the allowed sibling
    object.
  - A sibling-defined extern's executable address must equal the sibling's placed export address,
    which is the `-Map` address of its input section plus the symbol's offset.
    `trimmedSysrootObjects.siblingDefinedExterns` lists each one with its export, its image and
    its address.
  - `--stock-lld-arg` may not allow multiple definitions (`--allow-multiple-definition`,
    `-z muldefs`).
- **Flags.** `ld.lld` gets the flags in `stock::LLD_FLAGS`:
  `-static -no-pie --entry _start --gc-sections --eh-frame-hdr -z now --build-id=none --strip-debug`.
  Each flag is documented there.
- **Defaults kept.** There is no linker script, relaxation stays on, `--icf=none`, the page size is
  64 KiB, and the optimization level is `-O1`. With `-O2`, lld enables `--branch-to-branch` (a
  `bl f` becomes `bl g` when `f` starts with `b g`) and string tail merging.
- **`--stock-keep-library`.** Adds `--undefined=<sym>` for every global function or object the
  library defines. The whole library survives `--gc-sections` as one contiguous block, while
  unused runtime code is still dropped.
- **Output check.** The output must satisfy the trusted loader's static-ELF constraints
  (`verify::check_std_elf`).

The command writes three files:
- `stock-link.json`: provenance, input hashes, the lld version and arguments, segments and
  sections. It is reproducible. Every linked file is an `inputs[]` entry with its `sha256`.
  Native objects add `"kind": "nativeObject"`. rustc's self-contained runtime files add
  `"kind": "selfContained"` and `"pinnedSha256"`. A `std` binary link also records `stdBin`
  (`rustc`, `commit`, `llvm`, `selfContainedDir`, `weakenedInMain`, `archiveMembers`,
  `unwindAudit`).
- `timing.json`: the lld wall time.
- `census.json`: the census, built by `census.rs`. It places every library input section in the
  executable using `.symtab` anchors, masked content search and `SHF_MERGE` pieces. It then
  classifies every relocation site against the targets resolved from `.symtab`:
  - `exact`: the unrelaxed patched word;
  - `adrpAddToNopAdr`, `gotToAdrpAdd`, `gotToNopAdr`, `gotUnrelaxed`: lld relaxations of
    `adrp` + `add` / GOT `ldr` pairs;
  - `branchViaThunk`, `branchToBranch`, `weakUndefBranch`;
  - `unresolved`, `unmatched`.

  It also reports function survival and symbol visibility, ICF folds, the contiguity of library
  text and data, GOT slots, thunks and `.eh_frame`. Finally it checks whether the library text
  keeps the `rust-obj2lean` trusted-linker layout: one address delta for all text sections, and no
  differences in non-relocated bytes.

`scripts/dev/stock-link-fixture [--check]` regenerates or drift-checks committed stock-link fixtures across `CaseStudies/<Campaign>/`.

## Tests

```bash
cargo test --locked --manifest-path tools/Cargo.toml -p snapshot-link
```
