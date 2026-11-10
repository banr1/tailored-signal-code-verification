# Static Rust Whole-ELF Process Differential Suite (`Arm64/Testing/ProcessE2E`)

End-to-end differential test suite comparing real Linux user-mode execution (`qemu-aarch64` with
`-strace` syscall census capture) against the formal static ELF64 process semantics
(`Arm64/Trusted/Process/` + `ProofLib/Process.lean` `runElf` / `runElfByteArray`) across **26**
reproducibly linked `aarch64-unknown-linux-musl` `ET_EXEC` Rust binaries and **99** test cases.

## Directory Layout

- `src/common.rs` — Shared `#![no_main]` guest support:
  - `BrkMmapAlloc`: `#[global_allocator]` backed exclusively by `SYS_brk` (`214`), anonymous
    private `PROT_READ | PROT_WRITE` `SYS_mmap` (`222`), and `SYS_munmap` (`215`).
  - `read_args` / `read_envp`: safe readers over `argc`, `argv`, and musl `environ`.
  - `open_read_no_cloexec` / `open_write_trunc_no_cloexec`: optional raw `SYS_openat` (`56`)
    helpers without `O_CLOEXEC` (stock `std::fs::read` / `std::fs::write` also run directly now
    that `execFcntl` models `F_SETFD`, as exercised in `session_store` and `unmodified_std_probe`).
- `src/bin/*.rs` — Guest Rust binaries:
  1. `nostd_minimal.rs` — `#![no_std]` custom `_start` assembly entry point (`brk`, `read`, `write`,
     `exit_group`).
  2. `exit_codes.rs` — Exit status propagation (`0`, `1`, `2`, `42`, `255`).
  3. `echo_cat.rs` — Binary and multi-page `stdin` -> `stdout` streaming.
  4. `word_count.rs` — Line, ASCII word, and byte counter (`writeln!`).
  5. `argv_envp.rs` — `argc`, `argv`, and `environ` inspector.
  6. `arith_sort.rs` — Signed `i64`/`i128` arithmetic, `slice::sort`, FNV-1a digest, and `stderr`
     error reporting (`exit 2`).
  7. `btreemap_vec.rs` — Hashbrown-free `BTreeMap<String, Vec<u8>>` mutations + 32 KiB `SYS_mmap` /
     `SYS_munmap` scratch allocation.
  8. `stderr_stdio.rs` — Interleaved `stdout` (`fd 1`) and `stderr` (`fd 2`) streams, plus
     heap-formatted `panic!` and flushed-`stdout` `abort()` probes under `BrkMmapAlloc`.
  9. `getrandom_use.rs` — `SYS_getrandom` (`278`) flag/fault validation and raw 16-byte hex mode.
  10. `session_store.rs` — Multi-step stateful pre-key session store CLI (`keygen`, `init`, `send`,
      `recv`) with staged atomic `BTreeMap` directory stores, `coins` randomness stream, `0`-byte
      file truncation for pre-key deletion, and VFS edge-case probes.
  11. `std_startup_probe.rs` — Standard `fn main()` (`std::rt::lang_start`) runtime startup census.
  12. `unmodified_std_probe.rs` — Zero-shim `#![no_main]` `std` binary isolating stock `std::fs`
      (`fcntl`), stock musl `mallocng` (`mmap PROT_NONE`), `panic!`, `abort()`, `udf #0`, `udf #1`,
      `brk #1`, and `brk #0`.

  Workload binaries (real CLI-style programs using only modeled syscalls; every case is `match`,
  declared in `tools/run-trusted-tests/src/process_e2e/cases_workloads.rs`):

  13. `base64_codec.rs` — RFC 4648 encode (76-column wrap) / whitespace-tolerant decode with
      offset-reporting errors (`exit 1`).
  14. `hexdump.rs` — `hexdump -C` canonical rows with `*` squeezing and `-v`.
  15. `sha256sum.rs` — Crate-free SHA-256 of `stdin` plus `-c <hex>` verification (`exit 1` on
      mismatch).
  16. `rle_codec.rs` — `(count, byte)` run-length compress / decompress / in-memory roundtrip with
      corrupt-stream detection.
  17. `sort_uniq.rs` — `sort | uniq -c` with `-r`, `-n` (by count), and `-d` (duplicates only).
  18. `grep_lite.rs` — Fixed-string `grep` with `-i`/`-v`/`-n`/`-c` and POSIX exit status
      (`0`/`1`/`2`).
  19. `rpn_calc.rs` — Per-line RPN `i64` calculator with checked arithmetic and error exit
      (`exit 1`).
  20. `file_copy.rs` — Stock `std::fs` copy / uppercase transform with read-back verification
      (`O_TRUNC` over a longer file) and multi-file `cat` with `ENOENT` reporting.
  21. `json_lint.rs` — Non-recursive JSON tokenizer and bracket matcher with error offsets.
  22. `bignum.rs` — Base-`10^9` factorial, Fibonacci, and `2^N` decimal printing.
  23. `matrix_mul.rs` — LCG-seeded `N x N` `i64` matrix product with trace, checksum, and identity
      self-check.
  24. `env_lookup.rs` — `std::env::var_os` (musl `getenv`) lookups and sorted raw-`environ` listing.
  25. `rot_cipher.rs` — ROT13, signed Caesar, Atbash, and letter-frequency modes selected by `argv`.
  26. `collatz_stats.rs` — Collatz chain statistics over an `argv` range with `u64` overflow checks,
      median, and `BTreeMap` histogram.
- `bin/*.elf` — Committed reproducibly built static AArch64 `ET_EXEC` binaries.
- `expected_vectors.json` — Checked-in QEMU outcomes, post-run file snapshots, and `-strace`
  syscall censuses consumed by [ProcessE2E.lean](../Regression/ProcessE2E.lean).

## Commands

```bash
# Rebuild all 26 static AArch64 ELFs reproducibly and regenerate QEMU -strace vectors:
./scripts/process-e2e all --report-out /tmp/process-e2e-report.md

# Verify byte-for-byte ELF build reproducibility + zero drift against live QEMU:
./scripts/process-e2e build --check
./scripts/process-e2e regen --check

# Run all 99 differential cases through Lean's ELF loader and instruction semantics:
timeout 600 lake -d Arm64/Testing build --no-ansi unit_tests
Arm64/Testing/.lake/build/bin/unit_tests --process-e2e
```
