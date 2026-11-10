# `sail-aarch64` — Safe Rust Interface to the Sail Armv9.4-A Simulator

`sail-aarch64` provides a safe, pointer-free Rust API over the official ASL-derived [Sail Armv9.4-A (`rems-project/sail-arm`)](https://github.com/rems-project/sail-arm/tree/master/arm-v9.4-a) AArch64 instruction-set simulator (`[TEST ONLY]`).

It is designed so that differential test runners (such as [`tools/run-trusted-tests`](../run-trusted-tests)) can treat Sail as an ordinary, idiomatic Rust library without `unsafe` blocks, `extern "C"` declarations, or linker `--wrap` plumbing.

---

## What This Crate Wraps

| Component | Upstream Source / Version | Role |
|---|---|---|
| `armv9.c` (`5,356,337` lines) | [`rems-project/sail-arm`](https://github.com/rems-project/sail-arm/tree/1bf2e55) commit `1bf2e55` (`arm-v9.4-a/snapshots/c/armv9.c.gz`, generated from ARM's machine-readable A64 ASL via `asl_to_sail` + `sail -c`) | Complete Armv9.4-A instruction decode and operational semantics (`zstep_model`, `z__InitSystem`, architectural registers `zR0..zR30`, `z_Z[0..31]`, `zSP_EL0`, `z_PC`, `zPSTATE`, `zFPCR`, `zFPSR`). |
| `sail.c`, `rts.c`, `sail_failure.c` | [`rems-project/sail`](https://github.com/rems-project/sail) `0.17.1` C runtime (`lib/*.c`) | Arbitrary-precision bitvectors (`lbits` via GNU MP `mpz_t`), sparse page-table physical memory (`write_mem`, `read_mem`, `kill_mem`), and runtime initialization (`model_init`). |
| [`csrc/sail_ffi.c`](csrc/sail_ffi.c) & [`csrc/Makefile`](csrc/Makefile) | This crate (`473` lines of C + `65`-line Makefile) | Configures flat user-space (`EL0`) execution (`SCTLR_EL1.{M=0, SA=1, SA0=1, DZE=1}`, `CPACR_EL1.{FPEN=3, ZEN=3}`, `DCZID_EL0=4`) and links 4 symbol overrides into a self-contained static archive (`libsail_aarch64_ffi.a`) via `objcopy -W` + `ld -r`. |

### Symbol Overrides Baked into `libsail_aarch64_ffi.a`

[`csrc/Makefile`](csrc/Makefile) weakens 4 symbols in `libsail_armv9-<hash>.a` via `objcopy -W` and links them with strong definitions in [`csrc/sail_ffi.c`](csrc/sail_ffi.c) via `ld -r` when building `libsail_aarch64_ffi.a`, so downstream Rust crates do not need any special `cargo:rustc-link-arg` flags:

1. **`sail_assert` & `sail_match_failure`**: Convert Sail assertion/match failures into `have_exception = true` (returned as [`SailError::ModelFault`](src/lib.rs)) instead of calling `abort()`, and bypass a known upstream `v8_base.sail:30795` `Reduce()` assertion typo that omitted slice width `8` from `{16..2048}`.
2. **`z_get_SCTLR_EL1_Type_EE` & `z_get_HCR_EL2_Type_DC`**: Force Stage-1 flat memory (`SCTLR_EL1.M=0`) to use `MemType_Normal` (write-back cacheable) instead of `MemType_Device_nGnRnE` inside `AArch64_S1TTWParamsEL10` while keeping `HCR_EL2.DC=0` everywhere else so Stage-2 translation stays disabled and both unaligned general-purpose accesses and `DC ZVA` succeed at `EL0`.

---

## Build Requirements

- **C toolchain & binutils:** `cc`, `ar`, `ld`, `make`
- **GNU MP (`libgmp-dev`):** `gmp.h` and `libgmp` (`-lgmp`) required by Sail's `lbits` runtime.
- **Upstream Sail C snapshot:** Fetched and SHA-256 verified automatically by [`build.rs`](build.rs) via `../../scripts/fetch-upstream-sources.sh sail-arm` into `$ARM64_UPSTREAM_CACHE/sail-armv9/` (or overridden via `$SAIL_ARMV9_SRC_DIR`).
  - The compiled `armv9.o` + runtime archive is cached at `$ARM64_UPSTREAM_CACHE/sail-armv9/libsail_armv9-<hash>.a` across worktrees (`~2.5 min` cold build with `-O0`, `< 3 s` incremental rebuild).

---

## Safety & Threading Invariants

The Sail C compiler (`sail -c`) emits process-global C variables (`zR0..zR30`, `z_Z`, `z_PC`, `zSP_EL0`, `zPSTATE`, and a global sparse memory tree). `sail-aarch64` enforces memory and thread safety in safe Rust:

1. **Process-global mutex serialization:** [`Simulator::new`](src/lib.rs) acquires a process-wide `Mutex<()>` and stores the `MutexGuard<'static, ()>` inside [`Simulator`](src/lib.rs). At most one [`Simulator`](src/lib.rs) instance (or [`run_batch`](src/lib.rs) call) can access the Sail C globals at a time; concurrent Rust test threads block cleanly until the lock is released.
2. **Automatic physical memory cleanup on `Drop`:** Both [`Simulator::reset`](src/lib.rs) and `<Simulator as Drop>::drop` invoke `kill_mem()`, freeing all sparse physical memory pages allocated during a simulation run so consecutive tests never observe stale memory.
3. **No raw pointers in the public API:** All register arrays, memory writes/reads, and batch buffers use safe Rust slices and value types.

---

## Usage Example

```rust
use sail_aarch64::{CpuState, Simulator};

const CODE_BASE: u64 = 0x0001_0000;
const STACK_BASE: u64 = 0x0002_8000;
const EXIT_PC: u64 = 0x0004_0000;

let mut init = CpuState::new(CODE_BASE, STACK_BASE);
init.set_x(0, 20);
init.set_x(1, 22);
init.set_x(30, EXIT_PC); // LR = EXIT_PC

let mut sim = Simulator::new(&init)?;
sim.write_code(
    CODE_BASE,
    &[
        0x8b01_0000, // add x0, x0, x1
        0xd65f_03c0, // ret
    ],
);

let final_state = sim.run_to_exit(EXIT_PC, 10)?;
assert_eq!(final_state.x(0), 42);
assert_eq!(final_state.pc, EXIT_PC);
# Ok::<(), sail_aarch64::SailError>(())
```

Run the crate's unit and doc tests with:

```bash
cargo test --locked --manifest-path tools/Cargo.toml -p sail-aarch64
```
