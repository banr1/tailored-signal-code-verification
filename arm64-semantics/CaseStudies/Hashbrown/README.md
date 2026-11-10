# `CaseStudies/Hashbrown`: Rust `hashbrown` v0.17.1 Whole-Binary CLI Verification

**Proof Version:** `v0.39.0`

Standalone Lake package (`casestudy-hashbrown`) proving end-to-end whole-binary functional correctness and memory safety of a static Linux AArch64 safe-Rust `std` command-line executable ([`Implementation/hashbrown_cli.elf`](Implementation/hashbrown_cli.elf), compiled by `cargo +1.98.1 build --release --locked --target aarch64-unknown-linux-musl` from a single [`Implementation/Cargo.toml`](Implementation/Cargo.toml) hosting [`Implementation/src/main.rs`](Implementation/src/main.rs) with `#![forbid(unsafe_code)]`, [`Implementation/src/lib.rs`](Implementation/src/lib.rs), and [`Implementation/build.rs`](Implementation/build.rs), and linked by `rust-lld` against prebuilt Rust `std` and `musl` 1.2.5 `crt1.o` + `libc.a` `mallocng` with `vmlock.lo`'s unused `__vm_wait` renamed so single-threaded weak `__vm_wait` `ret` wins) built on Rust's [`hashbrown`](https://github.com/rust-lang/hashbrown) v0.17.1 SwissTable hash map (`c62a63a61b7caf2de8f9ecb7b06a66b0ab6bdf3d`, the exact crate vendored by `std::collections::HashMap` in our pinned Rust 1.98.1 toolchain), with **zero external hooks, zero instruction overrides, and `0 sorry`**.

## Quick Start

```bash
# Rebuild the static AArch64 musl CLI executable from the single Cargo.toml:
(cd CaseStudies/Hashbrown/Implementation && cargo build --release --locked --target aarch64-unknown-linux-musl)

# Build all specifications, checked examples, proofs, and trusted end-to-end theorems:
timeout 600 lake -d CaseStudies/Hashbrown build --no-ansi CaseStudies.Hashbrown Testing Theorems

# Audit the top-level theorem axiom & TCB closure:
./scripts/axiom-audit --strict --batch CaseStudies.Hashbrown.Theorems
```

---

## 1. Headline Theorem: Whole-Binary `hashbrown_cli.elf` (`Spec/Top.lean`)

`Spec/Top.lean` is the **sole trusted specification** for `CaseStudies/Hashbrown`. Read [`Spec/Top.lean`](Spec/Top.lean) alongside [`SpecExamples.lean`](SpecExamples.lean) (concrete `:= by decide` examples covering all 8 CLI commands, whitespace/overflow/`MaxWithCapacity` edge cases, error output, and whole-run `stdin` → `stdout`/`stderr`/exit-code behaviour):

```lean
theorem hashbrownCliUniversal_ok : HashbrownCliUniversalStmt
```

For **every** `inputs : ProcessInputs` satisfying `inputs.Valid` and `HashbrownStdinBudget inputs` (`inputs.stdin.length ≤ HashbrownCliMaxStdin = 10 GiB` and `8 * 2 ^ 20 + 8 * inputs.stdin.length ≤ inputs.init.physMemAvail`), executing `hashbrownCliBytes` (`hashbrown_cli.elf`) from `_start` (`0x224e00`) through `SYS_exit_group` over `Program.pureMem`:
- never faults, panics, or triggers undefined behaviour (`signal = none`);
- rejects the whole run before executing any command (`exitCode = 1`, `stdout = []`, `stderr = "error: line too long\n"`) if any `\n`-delimited line exceeds `MaxLineLen` (`4096` bytes); and
- otherwise initializes the SwissTable via `hashbrown_new`, folds `insert <u64> <u64>`, `get <u64>`, `remove <u64>`, `contains <u64>`, `with_capacity <u64>` (`≤ MaxWithCapacity = 4096`), `len`, `is_empty`, and `clear` over a pure association list (`evalLines (splitLines inputs.stdin)`), drops the final table via `hashbrown_drop`, writes query outputs to `stdout`, logs `"error: invalid command\n"` on `stderr` for malformed lines while continuing, and exits with `exitCode = 0`.

There is no bound on command count, distinct keys, deletion tombstones, or SwissTable table doublings/in-place rehashes beyond `inputs.stdin.length ≤ 10 GiB`.

### Trust Notes
- **Dynamic allocation (`mallocng`) & OOM safety:** The binary uses unmodified stock `musl` 1.2.5 `mallocng` (`malloc`/`free`/`realloc`/`calloc`) over `SYS_brk` and `SYS_mmap`/`SYS_mremap`/`SYS_munmap`/`SYS_mprotect`, with virtual-address and physical-memory consumption bounded across `10 GiB` inputs (`(hbStdLimits inputs.stdin.length).FitsVaSpace = true` and `8 MiB + 8 * inputs.stdin.length ≤ inputs.init.physMemAvail`).
- **Deterministic `SYS_read`:** `SYS_read(0, …)` in `Arm64.Trusted.Process` returns `min(count, remaining)` bytes per call; `std::io::Read::read_to_end` loops cleanly across short reads until EOF (`0`).
- **Zero hooks / overrides:** `_start`, `__libc_start_main`, Rust `std` `lang_start`, `malloc`, `free`, `realloc`, `memcpy`, `memset`, `memmove`, and all `hashbrown` v0.17.1 routines run as real linked AArch64 instructions in a single `R E` `.text` segment.
- **End-to-end relocatability (`Obj.MultiPlacedLib` & placement-generic `StdCli`):** Both `hashbrown` v0.17.1 (`hashbrownLib : Obj.MultiPlacedLib` in `Generated/HashbrownPlacedObj.lean`) and the safe-Rust `StdCli` driver (`Proofs/StdCli/*.lean`) are verified placement-generically with zero hardcoded binary addresses. [`Proofs/Top.lean`](Proofs/Top.lean) (`hashbrownFunctionalCorrectness_ok`) proves all ten `hashbrownLib` exports for **every** multi-block placement `mpl` satisfying `hashbrownLib.Placeable mpl` and any `HbExterns` (`HbAlloc.ofGlobalAlloc` under `HbSep mpl` in [`Proofs/Externs.lean`](Proofs/Externs.lean), or `HbAlloc.ofMallocng`). Concrete `hashbrown_cli.elf` virtual addresses appear solely in the thin final bridge [`Proofs/CliProof.lean`](Proofs/CliProof.lean) (`hashbrownCliUniversal_ok`).

---

## 2. Relocatable Library Contracts (`Proofs/InternalTop.lean` & `Proofs/Top.lean`)

Underneath `hashbrownCliUniversal_ok`, the CLI proof steps through placement-generic `MultiPlacedLib.subroutineOk` contracts in [`Proofs/InternalTop.lean`](Proofs/InternalTop.lean) (against the finite-map model `Map64` in [`Proofs/Model.lean`](Proofs/Model.lean) and representation predicate `U64MapRep` in [`Proofs/Defs.lean`](Proofs/Defs.lean)) for `U64Map = HashMap<u64, u64, FxBuildHasher>`, bundled as `HashbrownPlacedContracts` and proved in [`Proofs/Top.lean`](Proofs/Top.lean) (`hashbrownFunctionalCorrectness_ok`, `hashbrownGlobalAlloc_ok`). Because [`Spec/Top.lean`](Spec/Top.lean) is the sole trusted spec, `Proofs/Model.lean`, `Proofs/Defs.lean`, `Proofs/InternalTop.lean`, and `Proofs/Top.lean` are untrusted internal proof modules outside the TCB.

---

## 3. Package Layout

```text
CaseStudies/Hashbrown.lean                         (Role::Proof — package umbrella)
CaseStudies/Hashbrown/
  ├── Spec.lean                                    (Role::Spec  — trusted specification umbrella)
  ├── Spec/
  │     └── Top.lean                               (Role::Spec  — sole trusted spec: whole-binary CLI ELF)
  ├── SpecExamples.lean                            (Role::Proof — checked `by decide` CLI spec examples)
  ├── Theorems.lean & Theorems/Top.lean            (Role::Theorems — trusted end-to-end theorem: 1 / 1)
  ├── Implementation/
  │     ├── Cargo.toml, Cargo.lock, .cargo/config.toml, build.rs, translation.toml
  │     ├── src/lib.rs, src/main.rs
  │     └── hashbrown_cli.elf                      (cargo +1.98.1 musl static ELF)
  ├── Generated/HashbrownPlaced{Obj,Witness}.lean  (MultiPlacedLib & stock-link ELF witness)
  ├── Generated/HashbrownElfObj.lean               (pinned hashbrown_cli.elf bytes)
  ├── Proofs/
  │     ├── Model.lean, Externs.lean, Defs.lean    (Map64/FxHash math, HbAlloc/HbExterns, SwissTableInv)
  │     ├── PlacedCode.lean & InternalTop.lean     (multi-block decode reflection & library Spec contracts)
  │     ├── Probe.lean, Simple.lean, Lookup.lean   (NEON group probe & leaf operations: new/len/get/clear/drop)
  │     ├── WithCapacity.lean & Remove.lean        (with_capacity & tombstone/group-aware erase)
  │     ├── RehashInPlace{Prep,}.lean              (in-place tombstone stripping & re-insertion)
  │     ├── Resize{Pure,Copy}.lean & ReserveRehash.lean (power-of-two table doubling & reserve_rehash)
  │     ├── Insert.lean & Top.lean                 (fast/slow insert & HashbrownPlacedContracts)
  │     ├── StdCli/*.lean                          (placement-generic safe-Rust std + mallocng CLI driver)
  │     └── CliProof.lean                          (thin final hashbrown_cli.elf instantiation)
  └── Testing/
        ├── SpecAudit.lean                         (CLI spec non-vacuity & CliMap algebraic laws)
        ├── StdCliExecCheck.lean                   (concrete machine execution tests on hashbrown_cli.elf)
        └── PlacedWitness.lean                     (`#eval` smoke test: MultiPlacedLib vs. hashbrown_cli.elf)
```

---

## 4. Which File to Read for What

- **Whole-binary CLI contract (`Start Here`)**: Read [`Spec/Top.lean`](Spec/Top.lean) and [`SpecExamples.lean`](SpecExamples.lean).
- **Whole-binary bridge & placement-generic `StdCli` driver (`_start` → `main` → `SYS_exit_group`)**: Read [`Proofs/CliProof.lean`](Proofs/CliProof.lean), [`Proofs/StdCli/Top.lean`](Proofs/StdCli/Top.lean), [`Proofs/StdCli/Layout.lean`](Proofs/StdCli/Layout.lean), [`Proofs/StdCli/Lib.lean`](Proofs/StdCli/Lib.lean), [`Proofs/StdCli/MallocngBridge.lean`](Proofs/StdCli/MallocngBridge.lean), and [`Testing/StdCliExecCheck.lean`](Testing/StdCliExecCheck.lean).
- **Relocatable `hashbrown` v0.17.1 library contracts & SwissTable invariant**: The generic SwissTable control-byte, probing, NEON group, and invariant math lives in [`VerifiedLibraries/SwissTable`](../../VerifiedLibraries/SwissTable/README.md) (re-exported by `Model.lean` and `Probe.lean`; `SwissTableInv.toGeneric` bridges to it). Read [`Proofs/Model.lean`](Proofs/Model.lean), [`Proofs/Externs.lean`](Proofs/Externs.lean), [`Proofs/Defs.lean`](Proofs/Defs.lean), [`Proofs/InternalTop.lean`](Proofs/InternalTop.lean), and [`Proofs/Top.lean`](Proofs/Top.lean).
- **CLI spec non-vacuity & `CliMap` laws**: Read [`Testing/SpecAudit.lean`](Testing/SpecAudit.lean) and [`Testing/PlacedWitness.lean`](Testing/PlacedWitness.lean).

---

## 5. Memory Bound (`HashbrownStdinBudget` & `mallocng` Cost Model)

### 5.1 Dynamic Allocation Census of `hashbrown_cli.elf` (`L = inputs.stdin.length ≤ 10 GiB`)

Across a full execution from `_start` (`0x224e00`) through `SYS_exit_group`, the binary holds at most **5 simultaneously live `mallocng` blocks** (`maxPeakBlocks = 5`; at entry to any `malloc` call, `liveCount ≤ 4`):

| Subsystem | Call Pattern | User Request (`req`) | Peak Live Blocks | Real `mallocng` Backing (Size Class / `mmap`) | Tight Block Cost (`max req 65536`) |
|---|---|---:|---:|---|---:|
| **0. Pre-`userMain` altstack** ([`StartupPreTop.lean`](Proofs/StdCli/StartupPreTop.lean)) | Direct `SYS_mmap` + `SYS_mprotect` (`0` `mallocng` calls), unmapped before exit | `altRawSz + 4096 ≤ 528,384` B (`16 KiB` on default `AT_MINSIGSTKSZ`) | `0` | Tracked in `staticIvs` alongside `[0, brkBase)` (`brkBase = 0x295000 = 2,707,456` B `≤ 3 MiB`) and initial stack (`≤ 3,674,559` B static startup gap) | `0` (in `staticIvs`) |
| **1. `STDIN` `BufReader`** ([`StdinInit.lean`](Proofs/StdCli/StdinInit.lean)) | `malloc(8192)` on first `io::stdin().lock()` | `8,192` B (fixed, never freed) | `1` | `sc = 32` (`584 × 16 = 9,344` B/slot; `3`-slot `28,672` B `mmap` group on a fresh heap; worst-case slab `≤ 64 KiB`) | `65,536` B |
| **2. `input : Vec<u8>`** ([`StdinAndVec.lean`](Proofs/StdCli/StdinAndVec.lean), [`MainRead.lean`](Proofs/StdCli/MainRead.lean)) | `0` if `L = 0`; `malloc(max(L, 8))` if `1 ≤ L ≤ 32`; else `malloc(32)` then `realloc` doubling `64, 128, …, vecCap ≤ 2·L + 32` | Peak during `read_to_end` `realloc`: `oldCap + newCap ≤ 3·L + 32` B. Post-read steady state: `vecCap ≤ 2·L + 32` B (freed at end of `main`) | `≤ 2` during `realloc`, `≤ 1` after | Small slab (`sc ≤ 47`) for `vecCap ≤ 131,052` B; `sc = 63` individual `mmap` of `pageAlignUp(vecCap + 20) ≤ 2·L + 4,148` B for `vecCap > 131,052` B | Post-read: `≤ 2·L + 65,536` B |
| **3. `STDOUT` `LineWriter`** ([`StdoutInit.lean`](Proofs/StdCli/StdoutInit.lean), [`StartupPostCleanup.lean`](Proofs/StdCli/StartupPostCleanup.lean)) | Lazy `malloc(1024)` on first query output, `free` in `std::rt::cleanup` | `≤ 1,024` B | `≤ 1` | `sc = 20` (`72 × 16 = 1,152` B/slot; on a fresh heap carved as a nested sub-group inside `STDIN`'s unused `sc = 32` slot for `0` new pages) | `≤ 65,536` B |
| **4a. `U64Map` `with_capacity <n>`** (`n ≤ 4096`, [`WithCapacity.lean`](Proofs/WithCapacity.lean)) | Drops old table (`free`) **before** `malloc(17·B + 8)` (`B ≤ 8,192`) | `17·B + 8 ≤ 139,272` B | `≤ 1` | `sc ≤ 47` (`≤ 128 KiB` slab) for `B ≤ 4,096`; `sc = 63` `mmap` of `143,360` B (`140 KiB`) for `B = 8,192` | `≤ 139,272` B |
| **4b. `U64Map` `insert` doubling** (`resize_inner`, [`ReserveRehash.lean`](Proofs/ReserveRehash.lean)) | `malloc(34·B + 8)` while old table (`17·B + 8`) is live, then `free` old table | With tombstone-aware `U64MapRep` (`m.length + tombstones = bucketMaskToCapacity bm ≤ k_ins` when `growthLeft = 0`, `11·(k_ins + 1) ≤ L + 1` ⇒ `77·B ≤ 8·L + 308`): old + new = `51·B + 16 ≤ (408·L)/77 + 220` B (`≈ 5.30·L`) | `≤ 2` during resize, `≤ 1` steady | `sc ≤ 47` for `B ≤ 4,096`; `sc = 63` `mmap` (`pageAlignUp(req + 20) ≤ req + 4,115` B) for `B ≥ 8,192` | `≤ (408·L)/77 + 131,072` B |
| **Whole-run peak** | `STDIN` + `Vec<u8>` + `STDOUT` + old/new `U64Map` | `(562·L)/77 + 148,520` B (`≈ 7.30·L + 145 KiB`) | `peakCount ≤ 5` | Fresh-heap real peak: `≤ 256 KiB + (562·L)/77` (`≈ 7.30·L ≤ 8·L`) | `maxPeakCost = (562·L)/77 + 336,000` B |

### 5.2 Empirical Peak Memory Measurements on `hashbrown_cli.elf`

Running `Implementation/hashbrown_cli.elf` through the concrete AArch64 machine simulator ([`Testing/StdCliExecCheck.lean`](Testing/StdCliExecCheck.lean)) from `_start` to `SYS_exit_group` confirms the exact `SYS_brk` and `SYS_mmap`/`SYS_munmap` behaviour:

| Workload | `stdin` Bytes (`L`) | Instructions | `brk` Growth (`meta_area`) | Peak `physMemAvail` Delta | End `physMemAvail` Delta | VM Syscall Summary |
|---|---:|---:|---:|---:|---:|---|
| Empty `stdin` (`""`) | `0` | `3,804` | `8,192` B (`4 KiB` guard + `4 KiB` meta) | **`49,152` B (`48 KiB`)** | `36,864` B (`36 KiB`) | `16 KiB` altstack (`12 KiB` RW + `4 KiB` guard, unmapped at exit) + `8 KiB` `brk` + `28 KiB` `sc = 32` `STDIN` slab |
| `1-insert-get` | `18` | `9,853` | `8,192` B | **`57,344` B (`56 KiB`)** | `36,864` B (`36 KiB`) | Above + `4 KiB` `sc = 1` `Vec` slab + `4 KiB` `sc = 4` `U64Map` slab (`STDOUT` `sc = 20` sub-group carved inside `STDIN` slab for `0` new pages; both `4 KiB` slabs unmapped at exit) |
| `16-inserts` (`0..15`, `2` table doublings) | `214` | `23,018` | `8,192` B | **`57,344` B (`56 KiB`)** | `36,864` B (`36 KiB`) | `Vec` (`32 → 64 → 128 → 256` B) and `U64Map` (`4 → 8 → 16` buckets) reuse/unmap `4 KiB` slabs in place |
| `10-op-suite` (all 8 commands + `with_capacity 64`) | `214` | `29,376` | `8,192` B | **`65,536` B (`64 KiB`)** | `36,864` B (`36 KiB`) | Above + `8 KiB` `sc = 23` slab for `with_capacity 64` (`128` buckets = `2,184` B), unmapped at exit |

### 5.3 Comparison of Memory Bounds (`c0 + c1·L`)

| Bound Regime | Base Constant `c0` | Per-Byte Slope `c1` | Source of Overhead |
|---|---:|---:|---|
| **Previous headline (`v0.39.0`)** | `2 ^ 26 = 64 MiB` (`hbDynPhysBudget = 61.44 MB`) | `13 · L` | `40.04 MiB` from loose `2 × allocSlotPlacedByteBound` (`40 MiB + 8 KiB·pc`) in `MallocngTightTotalBound` + `18.25 MiB` `mallocngHeap_ivs_tight_bound` (`14.23 MiB` for 32 worst-case cached empty slabs + `4 × 1 MiB` live-block slack) + `3.50 MiB` static ELF/altstack gap |
| **Intermediate (`mallocngTightCostModel` + shrunk step reserve)** | `25 * 2 ^ 20 = 25 MiB` (`hbDynPhysBudget = 21,602,432 + (970·L)/77`) | `13 · L` (`⌈970 / 77⌉ · L`, `970/77 ≈ 12.60`) | Replaces the `40 MiB` step reserve with the actual `alloc_slot` + `alloc_meta` step bound (`≤ 2.03 MiB` + `pageAlignUp(req + 8192)`), without tombstone tracking or per-class retained-group bounds |
| **Current (`HashbrownStdinBudget`, D1.B)** | **`8 * 2 ^ 20 = 8 MiB`** (`hbDynPhysBudget = 4,185,665 + 8·L` ≥ `3,344,868 + 8·L` `tight2_hb_budget` peak) | **`8 · L`** (`⌈562 / 77⌉ · L`, `562/77 ≈ 7.30`) | Tombstone-aware `U64MapRep` (`m.length + tombstones = bucketMaskToCapacity bm ≤ k_ins` at `growthLeft = 0`) + per-class retained-group (`tight2Footprint`) and tight step-reserve bounds (`mallocngRootGroupBoundAt`) in `VerifiedLibraries.Mallocng` |

---

## 6. Campaign Plan & Phases

<a id="phase-1"></a>

## Phase 1: Relocatable SwissTable Library Proofs

- **Pure model, allocator parameterization & SwissTable invariant**: [`Proofs/Model.lean`](Proofs/Model.lean), [`Proofs/Externs.lean`](Proofs/Externs.lean), [`Proofs/PlacedCode.lean`](Proofs/PlacedCode.lean), [`Proofs/Defs.lean`](Proofs/Defs.lean), and [`Proofs/InternalTop.lean`](Proofs/InternalTop.lean) formalize `Map64`, `FxHasher64`, `SwissTableInv` (`U64MapRep` / `U64MapRepReady`), `HbAlloc` (`ofGlobalAlloc` and `ofMallocng`), and multi-block relocatable instruction decoding over `hashbrownLib.Placeable mpl`.
- **NEON probing, leaf operations, `rehash_in_place`, `resize_inner`, and `insert`**: [`Proofs/Probe.lean`](Proofs/Probe.lean), [`Proofs/Simple.lean`](Proofs/Simple.lean), [`Proofs/WithCapacity.lean`](Proofs/WithCapacity.lean), [`Proofs/Lookup.lean`](Proofs/Lookup.lean), [`Proofs/Remove.lean`](Proofs/Remove.lean), [`Proofs/RehashInPlacePrep.lean`](Proofs/RehashInPlacePrep.lean), [`Proofs/RehashInPlace.lean`](Proofs/RehashInPlace.lean), [`Proofs/ResizePure.lean`](Proofs/ResizePure.lean), [`Proofs/ResizeCopy.lean`](Proofs/ResizeCopy.lean), [`Proofs/ReserveRehash.lean`](Proofs/ReserveRehash.lean), [`Proofs/Insert.lean`](Proofs/Insert.lean), and [`Proofs/Top.lean`](Proofs/Top.lean) prove all ten `hashbrownLib` exports (`hashbrownFunctionalCorrectness_ok` and `hashbrownGlobalAlloc_ok`) with zero concrete virtual addresses.

<a id="phase-2"></a>

## Phase 2: Placement-Generic Safe-Rust StdCli Driver and Whole-Binary Bridge

- **Placement-generic runtime, `mallocng` bridge, and `hashbrownLib` extern realization**: [`Proofs/StdCli/Layout.lean`](Proofs/StdCli/Layout.lean), [`Proofs/StdCli/MemOps.lean`](Proofs/StdCli/MemOps.lean), [`Proofs/StdCli/MallocngBridge.lean`](Proofs/StdCli/MallocngBridge.lean) (via [`ProofLib/MallocngBridge.lean`](../../ProofLib/MallocngBridge.lean)), [`Proofs/StdCli/Shims.lean`](Proofs/StdCli/Shims.lean), [`Proofs/StdCli/Lib.lean`](Proofs/StdCli/Lib.lean), and [`Proofs/StdCli/StartupAndExit.lean`](Proofs/StdCli/StartupAndExit.lean) verify relocatable `memcpy`/`memset`/`memmove`, lift `VerifiedLibraries.Mallocng` (`mallocngTop_ok`) to `MallocngIface` with `10 GiB` VA/physical-memory budgets, discharge `HbExterns` directly in `.text`, and verify `_start` → `userMain` → `SYS_exit_group` via `ProofLib.StdStartup`.
- **Safe-Rust `std` I/O, formatting, command loop, and thin `hashbrown_cli.elf` instantiation**: [`Proofs/StdCli/MainReadAndScan.lean`](Proofs/StdCli/MainReadAndScan.lean), [`Proofs/StdCli/MainCmdLoop.lean`](Proofs/StdCli/MainCmdLoop.lean), [`Proofs/StdCli/MainEpilogue.lean`](Proofs/StdCli/MainEpilogue.lean), [`Proofs/StdCli/Stdout.lean`](Proofs/StdCli/Stdout.lean), [`Proofs/StdCli/Fmt.lean`](Proofs/StdCli/Fmt.lean), and [`Proofs/StdCli/Top.lean`](Proofs/StdCli/Top.lean) prove placement-generic `hbCli_runsTo`; [`Proofs/CliProof.lean`](Proofs/CliProof.lean) instantiates the concrete `hashbrown_cli.elf` layout once to close `hashbrownCliUniversal_ok : HashbrownCliUniversalStmt`.

<a id="phase-3"></a>

## Phase 3: Single-Cargo Stock musl Consolidation and 10-Op CLI

- **Single `Implementation/Cargo.toml` (`[lib]` + `[[bin]]`) & stock `cargo +1.98.1` musl ELF**: Consolidates `src/lib.rs` and `src/main.rs` (`#![forbid(unsafe_code)]`) into [`Implementation/Cargo.toml`](Implementation/Cargo.toml) (`hashbrown_cli.elf`, single `R E` `.text` segment, prebuilt `CsiKaSbYLw9fL_3std`, `0` upward symlinks, `0` veneers) with optional `target = "aarch64-unknown-linux-musl"` in `translation.toml`.
- **`Obj.MultiPlacedLib` (`[placed] multi = true`) & 10-operation CLI**: Exercises all 10 verified SwissTable exports (`new`, `with_capacity`, `insert`, `get`, `remove`, `len`, `is_empty`, `contains_key`, `clear`, and `drop` on exit) end-to-end in [`Spec/Top.lean`](Spec/Top.lean), porting `Proofs/` to `MultiPlacedLib` block projections and shared `VerifiedLibraries.{RustStd,Mallocng,Musl}`.

<a id="phase-4"></a>

## Phase 4: Tight Memory Bound (`Mallocng` Cost Model)

- **Phase 4.0 — Allocation census, empirical RSS check & spec gate**: Enumerate all dynamic allocations in `hashbrown_cli.elf` as a function of `L = inputs.stdin.length`, measure concrete peak `physMemAvail` deltas (`48–64 KiB` on the [`Testing/StdCliExecCheck.lean`](Testing/StdCliExecCheck.lean) test suites), and tighten `HashbrownStdinBudget` in [`Spec/Top.lean`](Spec/Top.lean) from `2 ^ 26 + 13 * inputs.stdin.length` (`64 MiB + 13·L`) to `8 * 2 ^ 20 + 8 * inputs.stdin.length` (`8 MiB + 8·L`).
- **Phase 4.1 — Tombstone-aware SwissTable representation (`Proofs/*.lean` & `Proofs/StdCli/Main*.lean`)**: Track tombstone count `t : Nat` (`m.length + t = bucketMaskToCapacity bm - growthLeft.toNat ≤ k_ins`) in `U64MapRep` / `HbCanInsertOne`, proving `77 * (bm.toNat + 1) ≤ 8 * L + 308` at resize and tightening the linear user-request peak from `(970 * L) / 77` (`12.60·L`) to `(562 * L) / 77` (`7.30·L ≤ 8·L`).
- **Phase 4.2 — Cost-model-parametric bridge & per-class `mallocng` bound (`Proofs/StdCli/MallocngBridge.lean`, `Layout.lean`, `StartupPreTop.lean`)**: Consume `VerifiedLibraries.Mallocng` cost-model and per-class retained-group/step-reserve bounds to close `hashbrownCliUniversal_ok : HashbrownCliUniversalStmt` under `8 * 2 ^ 20 + 8 * inputs.stdin.length ≤ inputs.init.physMemAvail`.
