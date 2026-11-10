/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import Arm64.Trusted.Spec.AsciiNum

/-!
# Whole-Binary CLI Specification for `hashbrown` v0.17.1 (`CaseStudies.Hashbrown.Spec.Top`)

- **Role:** `Role::Spec` (trusted top-level specification, 0 theorems; concrete checked `example`s
  live right next door in [`CaseStudies/Hashbrown/SpecExamples.lean`](../SpecExamples.lean)).
- **Binary under verification (`hashbrownCliBytes`):** Static Linux AArch64 (`ET_EXEC`) safe-Rust
  `std` executable ([`Implementation/hashbrown_cli.elf`](../Implementation/hashbrown_cli.elf),
  embedded via `file_bytes%` with SHA-256 pin and parsed via `ElfImage.parse`), compiled by stock
  `cargo +1.98.1 build --release --locked --target aarch64-unknown-linux-musl` from the single
  package [`Implementation/Cargo.toml`](../Implementation/Cargo.toml) hosting both
  [`Implementation/src/main.rs`](../Implementation/src/main.rs) (`#![forbid(unsafe_code)]`) and
  [`Implementation/src/lib.rs`](../Implementation/src/lib.rs) (`hashbrown` v0.17.1
  `HashMap<u64, u64, FxBuildHasher>`), and [`Implementation/build.rs`](../Implementation/build.rs),
  and linked by `rust-lld` (`ld.lld`) against prebuilt Rust `std` and `musl` 1.2.5 (`crt1.o` +
  `libc.a` `mallocng`) into a single `R E` `.text` segment (`0x224e00`). There are **zero hooks and
  zero instruction overrides** (`Program.pureMem`, `oom := fun _ _ => False`).

## Summary of CLI Behaviour

For every `inputs : ProcessInputs` satisfying `inputs.Valid` and `HashbrownStdinBudget inputs`
(`inputs.stdin.length ≤ HashbrownCliMaxStdin`, `10 GiB`, and
`8 * 2 ^ 20 + 8 * inputs.stdin.length ≤ inputs.init.physMemAvail`):

| Input | Behaviour | `stdout` | `stderr` | Exit |
|---|---|---|---|---:|
| Empty `stdin` (`[]`) | nothing to do | `""` | `""` | `0` |
| `insert <k> <v>` | insert or overwrite `(k, v)` | `""` | `""` | `0` |
| `get <k>` | look up `k` | `"<v>\n"` or `"none\n"` | `""` | `0` |
| `remove <k>` | erase `k` (missing key is a no-op) | `""` | `""` | `0` |
| `contains <k>` | membership query | `"true\n"` or `"false\n"` | `""` | `0` |
| `with_capacity <n>` (`n ≤ MaxWithCapacity = 4096`) | reset to an empty map | `""` | `""` | `0` |
| `len` | current key count | `"<n>\n"` | `""` | `0` |
| `is_empty` | emptiness query | `"true\n"` or `"false\n"` | `""` | `0` |
| `clear` | erase all entries | `""` | `""` | `0` |
| Malformed line (unknown verb, wrong arity, non-digit, empty number, value `≥ 2^64`, `with_capacity` `> 4096`, stray spaces, `\r`, blank line) | skip line and continue | `""` | `"error: invalid command\n"` | `0` |
| Any line strictly longer than `MaxLineLen` (`4096` bytes) | reject entire input before executing any command | `""` | `"error: line too long\n"` | `1` |

`HashbrownCliPost` specifies pure whole-process input/output behaviour (`exitCode`, `signal`,
`stdout`, `stderr`); as informational background on binary structure, `src/main.rs` implements the
stateful map with `hashbrown_new`, `hashbrown_with_capacity`, `hashbrown_insert`, `hashbrown_get`,
`hashbrown_remove`, `hashbrown_contains_key`, `hashbrown_len`, `hashbrown_is_empty`,
`hashbrown_clear`, and `hashbrown_drop`.

Lines are split on `\n` (`0x0a`), ignoring one optional trailing `\n` (`splitLines [] = []`).
Fields are separated by a single ASCII space (`0x20`). Keys, values, and capacities are 64-bit
unsigned integers written in non-empty ASCII decimal (`0`..`18446744073709551615`, parsed via
`Arm64.parseDecimalU64` and formatted via `Arm64.formatDecimalNat`; leading zeros are allowed;
`with_capacity <n>` requires `n ≤ MaxWithCapacity`). There is no cap on the number of commands,
distinct keys, tombstones, or SwissTable resizes beyond the `10 GiB` total `stdin` length bound.

## Trust Model Notes

1. **Dynamic allocation (`mallocng`) & OOM-free execution (`oom := fun _ _ => False`):** The binary
   uses unmodified stock `musl` 1.2.5 `mallocng` (`malloc`/`free`/`realloc`/`calloc`) over `SYS_brk`
   and `SYS_mmap`/`SYS_mremap`/`SYS_munmap`/`SYS_mprotect`. Under `HashbrownStdinBudget inputs`
   (`inputs.stdin.length ≤ 10 GiB` and `8 MiB + 8 * inputs.stdin.length ≤ inputs.init.physMemAvail`),
   neither virtual address space nor physical memory is exhausted (`oom := fun _ _ => False`), and
   every run terminates in a state satisfying `HashbrownCliPost inputs.stdin`.
2. **Deterministic `SYS_read`:** In `Arm64.Trusted.Process`, `SYS_read(0, buf, count)` returns
   `min(count, MAX_RW_COUNT, remaining)` bytes per call; `std::io::Read::read_to_end` loops over
   arbitrary positive short reads cleanly until `0` (EOF).
3. **Zero hooks or stubs (`Program.pureMem`):** `ElfRunsTo` uses the default `prog := Program.pureMem`
   with zero external symbol hooks or instruction overrides, so the ARM64 semantics steps directly
   over the machine instructions loaded from `hashbrown_cli.elf`.
-/

@[expose] public section

namespace CaseStudies.Hashbrown

open Arm64 Arm64.Process

/-! ## 1. Raw ELF Binary Bytes & Input Bounds -/

set_option maxRecDepth 2000000 in
/-- Raw ELF64 (`ET_EXEC`) file bytes of the static safe-Rust `std` + stock `musl` `mallocng` AArch64
    CLI binary (`hashbrown_cli.elf`, linked by stock `rust-lld`). -/
noncomputable def hashbrownCliBytes : List (BitVec 8) :=
  file_bytes% "../Implementation/hashbrown_cli.elf" sha256 "9c0415743bb4bfd56f8166494597606ec6682f063f31acb02f27749c10089d92"

/-- `10 GiB` maximum `stdin` length (`10 * 2 ^ 30 = 10,737,418,240` bytes). -/
def HashbrownCliMaxStdin : Nat := 10 * 2 ^ 30

/-- Maximum byte length of a single `\n`-stripped line in `stdin` (`4096` bytes). If any line is
    strictly longer than `MaxLineLen`, the binary rejects the whole run with exit code `1` before
    executing any command. -/
def MaxLineLen : Nat := 4096

/-- Maximum requested element capacity accepted by `with_capacity <n>` (`4096`, allocating up to
    `8192` SwissTable buckets). Larger values are rejected as invalid commands. -/
def MaxWithCapacity : Nat := 4096

/-! ## 2. Command Syntax & Line Splitting -/

/-- Parsed CLI command on 64-bit unsigned keys, values, and bounded initial capacities. -/
inductive CliCmd where
  | insert       (k v : BitVec 64)
  | get          (k : BitVec 64)
  | remove       (k : BitVec 64)
  | contains     (k : BitVec 64)
  | withCapacity (cap : BitVec 64)
  | len
  | isEmpty
  | clear
  deriving DecidableEq, Repr

/-- Strip an exact byte prefix `pfx` from `bs`, returning the remaining suffix when it matches. -/
def stripBytePrefix : List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))
  | [], bs => some bs
  | p :: ps, b :: bs => if p == b then stripBytePrefix ps bs else none
  | _ :: _, [] => none

/-- Split `bs` at the first occurrence of byte `sep`, returning `(before, after)`. -/
def splitFirstByte (sep : BitVec 8) : List (BitVec 8) → Option (List (BitVec 8) × List (BitVec 8))
  | [] => none
  | b :: bs =>
    if b == sep then some ([], bs)
    else (splitFirstByte sep bs).map fun (lhs, rhs) => (b :: lhs, rhs)

/-- Parse one `\n`-stripped line:
    `insert <u64> <u64>` | `get <u64>` | `remove <u64>` | `contains <u64>` |
    `with_capacity <u64>` (`≤ MaxWithCapacity`) | `len` | `is_empty` | `clear`,
    separated by single ASCII spaces (`0x20`). -/
def parseCommand (line : List (BitVec 8)) : Option CliCmd := do
  if let some rest := stripBytePrefix (bytesOfString "insert ") line then
    let (ks, vs) ← splitFirstByte 0x20#8 rest
    return .insert (← parseDecimalU64 ks) (← parseDecimalU64 vs)
  if let some rest := stripBytePrefix (bytesOfString "remove ") line then
    return .remove (← parseDecimalU64 rest)
  if let some rest := stripBytePrefix (bytesOfString "get ") line then
    return .get (← parseDecimalU64 rest)
  if let some rest := stripBytePrefix (bytesOfString "contains ") line then
    return .contains (← parseDecimalU64 rest)
  if let some rest := stripBytePrefix (bytesOfString "with_capacity ") line then
    let cap ← parseDecimalU64 rest
    guard (cap.toNat ≤ MaxWithCapacity)
    return .withCapacity cap
  if line == bytesOfString "len" then return .len
  if line == bytesOfString "is_empty" then return .isEmpty
  if line == bytesOfString "clear" then return .clear
  none

/-- Split a byte list on every occurrence of `sep` (`splitOnByte sep [] = [[]]`). -/
def splitOnByte (sep : BitVec 8) : List (BitVec 8) → List (List (BitVec 8))
  | [] => [[]]
  | b :: bs =>
    if b == sep then
      [] :: splitOnByte sep bs
    else
      match splitOnByte sep bs with
      | [] => [[b]]
      | l :: ls => (b :: l) :: ls

/-- Split `stdin` on `\n` (`0x0a`), ignoring one optional trailing `\n`; returns `[]` on `[]`. -/
def splitLines (bs : List (BitVec 8)) : List (List (BitVec 8)) :=
  if bs.isEmpty then []
  else
    let core := if bs.getLast? == some 0x0a#8 then bs.dropLast else bs
    splitOnByte 0x0a#8 core

/-! ## 3. Pure Finite-Map Semantics & Output Specification -/

/-- Pure association-list finite map reference model for the stock-linked `hashbrown_cli.elf`. -/
abbrev CliMap := List (BitVec 64 × BitVec 64)

/-- Look up key `k` in `CliMap`. -/
def cliMapLookup (k : BitVec 64) : CliMap → Option (BitVec 64)
  | [] => none
  | (k', v') :: rest => if k' == k then some v' else cliMapLookup k rest

/-- Erase all entries with key `k` from `CliMap`. -/
def cliMapErase (k : BitVec 64) : CliMap → CliMap
  | [] => []
  | (k', v') :: rest => if k' == k then cliMapErase k rest else (k', v') :: cliMapErase k rest

/-- Insert or overwrite `(k, v)` in `CliMap`. -/
def cliMapInsert (k v : BitVec 64) (m : CliMap) : CliMap :=
  (k, v) :: cliMapErase k m

/-- Format the output of `get <k>` as `"<v>\n"` (decimal) if found, or `"none\n"` if absent. -/
def formatGetResult : Option (BitVec 64) → List (BitVec 8)
  | some v => formatDecimalNat v.toNat ++ bytesOfString "\n"
  | none   => bytesOfString "none\n"

/-- Format the output of a boolean query (`contains <k>` or `is_empty`) as `"true\n"` or `"false\n"`. -/
def formatBoolResult (b : Bool) : List (BitVec 8) :=
  bytesOfString (if b then "true\n" else "false\n")

/-- Pure left fold over `lines` starting from an empty map, accumulating `(stdout, stderr)`. -/
def evalLines (lines : List (List (BitVec 8))) : List (BitVec 8) × List (BitVec 8) :=
  let step := fun ((m, o, e) : CliMap × List (BitVec 8) × List (BitVec 8)) line =>
    match parseCommand line with
    | none                   => (m, o, e ++ bytesOfString "error: invalid command\n")
    | some (.insert k v)     => (cliMapInsert k v m, o, e)
    | some (.remove k)       => (cliMapErase k m, o, e)
    | some (.get k)          => (m, o ++ formatGetResult (cliMapLookup k m), e)
    | some (.contains k)     => (m, o ++ formatBoolResult (cliMapLookup k m).isSome, e)
    | some (.withCapacity _) => ([], o, e)
    | some .len              => (m, o ++ formatDecimalNat m.length ++ bytesOfString "\n", e)
    | some .isEmpty          => (m, o ++ formatBoolResult m.isEmpty, e)
    | some .clear            => ([], o, e)
  let (_, o, e) := lines.foldl step ([], [], [])
  (o, e)

/-- Observable termination postcondition for `hashbrownCliBytes` on `stdin`:
    - if any line in `splitLines stdin` has byte length `> MaxLineLen` (`4096`), rejects the entire
      input before executing any command (`exitCode = 1#64`, `signal = none`, `stdout = []`,
      `stderr = "error: line too long\n"`);
    - otherwise runs `evalLines (splitLines stdin)` and exits cleanly (`exitCode = 0#64`,
      `signal = none`, `stdout = o`, `stderr = e`). -/
def HashbrownCliPost (stdin : List (BitVec 8)) (out : ProcessOutcome) : Prop :=
  if (splitLines stdin).any (·.length > MaxLineLen) then
    out.exitCode = 1#64 ∧ out.signal = none ∧
    out.stdout = [] ∧ out.stderr = bytesOfString "error: line too long\n"
  else
    let (o, e) := evalLines (splitLines stdin)
    out.exitCode = 0#64 ∧ out.signal = none ∧ out.stdout = o ∧ out.stderr = e

/-! ## 4. Top-Level Whole-Binary Verification Statement -/

/-- Input-size and physical-memory budget for the stock-linked `hashbrown_cli.elf`:
    `inputs.stdin` is at most `HashbrownCliMaxStdin` (`10 GiB`) and at least
    `8 MiB + 8 * inputs.stdin.length` (`8 * 2 ^ 20 + 8 * inputs.stdin.length`) of physical
    memory is available for the `mallocng` allocator. -/
def HashbrownStdinBudget (inputs : ProcessInputs) : Prop :=
  inputs.stdin.length ≤ HashbrownCliMaxStdin ∧
  8 * 2 ^ 20 + 8 * inputs.stdin.length ≤ inputs.init.physMemAvail

/-- Headline end-to-end theorem statement for `hashbrown_cli.elf`: the binary parses, and for every
    `inputs : ProcessInputs` satisfying `inputs.Valid` and `HashbrownStdinBudget inputs`, the static
    AArch64 safe-Rust `std` + stock `musl` `mallocng` binary parses and loads cleanly, never faults,
    panics, or OOMs (`oom := fun _ _ => False`), and terminates in a state satisfying
    `HashbrownCliPost inputs.stdin` with zero external hooks or instruction overrides. -/
noncomputable def HashbrownCliUniversalStmt : Prop :=
  ElfRunsTo hashbrownCliBytes
    (fun inputs => inputs.Valid ∧ HashbrownStdinBudget inputs)
    (fun inputs => HashbrownCliPost inputs.stdin)

end CaseStudies.Hashbrown
