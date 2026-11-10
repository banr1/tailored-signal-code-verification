# `proc-snapshot` — AArch64 process snapshots under qemu-user (`[CASE-STUDIES TCB]`)

`proc-snapshot` runs a static non-PIE AArch64 Linux ELF under **qemu-aarch64 user mode** and
dumps the guest process state over qemu's GDB stub. A snapshot is the initial machine state
that optional process-snapshot proofs start from, so this tool belongs to `[case-studies-tcb]`
(trusted only for snapshot-based proofs, not for the core engine `[tcb]`). It is kept
small; read [`src/snapshot.rs`](./src/snapshot.rs) for the schema and checks,
[`src/rsp.rs`](./src/rsp.rs) for the wire protocol, and [`src/elf.rs`](./src/elf.rs) for ELF
parsing.

## Usage

```bash
QEMU="$(scripts/fetch-qemu-aarch64)"          # pinned, sha256-verified Debian qemu-user build
cargo run --release --locked --manifest-path tools/Cargo.toml --bin proc-snapshot -- \
  snapshot --elf path/to/prog --qemu "$QEMU" --out-dir out [--stop-symbol main] \
  [--entry-only] [--argv0 prog] [--arg ARG]... [--env KEY=VAL]... [--input data.bin]...
```

This writes `out/entry.snapshot.{json,bin}` (first guest instruction, `pc == e_entry`) and,
unless `--entry-only` is passed, `out/<stop>.snapshot.{json,bin}` (breakpoint on the stop
symbol, default `main`).

## How it runs

- qemu is started as `qemu-aarch64 -g <port> -seed 0 -0 <argv0> <elf>` with an empty
  environment and host ASLR disabled (`personality(ADDR_NO_RANDOMIZE)`). The exec-entry
  snapshot is byte-identical from run to run. Before `main`, libc stores the host thread id,
  so a few bytes of the `main` snapshot can differ between runs.
- Memory is only read through the gdbstub (`m addr,len`). qemu's `/proc/<pid>/mem` and the
  guest's emulated `/proc/self/maps` are never consulted.

## Regions

| kind | extent | perm |
| :--- | :--- | :--- |
| `load` | every PT_LOAD with `p_memsz > 0`, rounded out to 4 KiB pages (overlap after rounding is an error) | from `p_flags` |
| `stack` | `[pagefloor(sp) - 16 KiB, top)`, `top` = first unreadable page above `sp` (≤ 1 MiB) | `rw-` |
| `brk` | only if `brkStart` (page-ceil of the highest PT_LOAD end) is readable | `rw-` |

## Checks (fail loudly)

- entry `pc == e_entry`; stop `pc ==` symbol address; both stops report SIGTRAP;
- entry stack holds `argc == 1`, `argv == [argv0]`, `envp == []` (so qemu applied `-0` and the
  empty environment);
- same stack top at both stops; regions pairwise disjoint;
- a non-zero `tpidr_el0` points into some region (otherwise TLS memory would be missing);
- every non-writable region is byte-identical between the entry and stop snapshots. The tool
  also prints how many bytes of each writable region changed.

[`Arm64/Testing/ElfLoaderDiff/README.md`](../../Arm64/Testing/ElfLoaderDiff/README.md) and
[`scripts/elf-loader-diff`](../../scripts/elf-loader-diff) use `proc-snapshot --entry-only` to
differentially test `ElfImage.loadState` against `qemu-aarch64` user mode across the static ELF
corpus.

## Schema `arm64-proc-snapshot/1`

All addresses and sizes are JSON integers; keys are written in a fixed order, pretty-printed
with a trailing newline. `regions[].binOff` indexes into the `.bin` file, which concatenates
region bytes in ascending address order. `regs.tpidr_el0` comes from qemu's system-register
target description (`TPIDR_EL0`); it is `null` only when the stub exposes no such register.

## Tests

```bash
cargo test --locked --manifest-path tools/Cargo.toml -p proc-snapshot
```

The unit tests cover RSP framing, checksums, escapes, run-length decoding, stop replies,
target-XML parsing, and page rounding. The integration test builds a tiny static ELF with
`zig cc`, snapshots it twice, and checks the snapshot against the ELF file, run-to-run
reproducibility, and qemu's real `sbrk(0)`. It is skipped when qemu or zig is missing;
set `REQUIRE_PROC_SNAPSHOT=1` to make that a failure. qemu is looked up in
`$QEMU_AARCH64`, then the `scripts/fetch-qemu-aarch64` cache, then `PATH`.
