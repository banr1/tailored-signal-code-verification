# `unicorn-aarch64` — Typed AArch64 ISA Oracle over Unicorn Engine (`[TEST ONLY]`)

`unicorn-aarch64` wraps the [`unicorn-engine`](https://crates.io/crates/unicorn-engine) crate (`UC_ARCH_ARM64`, `UC_CPU_ARM64_MAX`) behind [`isa_oracle::Arm64Oracle`] so that Unicorn participates in differential testing through the same typed [`CpuState`], [`TestInput`], and [`Outcome`] interface as Sail (`tools/sail-aarch64`) and Lean (`diff_eval --serve`).

## Which File to Read

| File | Description |
| --- | --- |
| `src/lib.rs` | `UnicornOracle` (`impl Arm64Oracle`), register tables (`UC_X_REGS`, `UC_V_REGS`), 4 KiB page mapping from `TestInput::mapped`, and unit tests |
