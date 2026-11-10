# `tools/isa-oracle` — Common AArch64 ISA Oracle Interface (`[TEST ONLY]`)

`isa-oracle` is a zero-dependency crate defining the common Rust trait (`Arm64Oracle`), typed architectural state (`CpuState`), test input (`TestInput`), execution outcome (`Outcome`), and differential comparison policy (`Policy`, `diff`) shared across all three AArch64 ISA evaluators:

1. **Official ARM Sail Armv9.4-A (`rems-project/sail-arm`)**: [`tools/sail-aarch64`](../sail-aarch64/README.md) (`SailOracle`)
2. **Unicorn Engine (`UC_ARCH_ARM64` / `UC_CPU_ARM64_MAX`)**: [`tools/unicorn-aarch64`](../unicorn-aarch64/README.md) (`UnicornOracle`)
3. **Lean 4 `Arm64.Step` / `Arm64.execInst` (`diff_eval --serve`)**: [`tools/run-trusted-tests`](../run-trusted-tests/src/lib.rs) (`LeanOracle` backed by `Arm64/Testing/Harness/Serve.lean`)

## Key Exports

| Item | Description |
| :--- | :--- |
| [`CpuState`](src/lib.rs) | Complete user-space (`EL0`) AArch64 register and flag state (`gprs: [u64; 31]`, `vregs: [u128; 32]`, `sp`, `pc`, `nzcv`, `fpcr`, `fpsr`, `tpidr_el0`). |
| [`TestInput`](src/lib.rs) | Canonical single- or multi-instruction test input (`state`, `code`, `mem`, `mapped`, `watch`, `exit_pc`, `max_steps`). |
| [`Outcome`](src/lib.rs) / [`FaultKind`](src/lib.rs) | Typed execution result (`Ok { state, mem, steps }`, `Unmodeled { pc, word }`, `Fault { pc, kind }`, `StepLimit { pc }`, `OracleError(String)`). |
| [`Arm64Oracle`](src/lib.rs) | Common oracle trait (`name`, `load`, `step`, default `run`, default `run_batch`). |
| [`Policy`](src/lib.rs) / [`diff`](src/lib.rs) | Differential comparison and adjudication rules (NOP-neutralization of unmodeled and non-NOP `HINT` encodings, Sail adjudication of Unicorn QEMU 5.0 FP/SIMD quirks, optional `fpsr`/`fpcr`/`tpidr_el0` comparison). |

## Running Tests

```bash
cargo test --locked --manifest-path tools/Cargo.toml -p isa-oracle
```
