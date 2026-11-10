/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.Process
public import LibsignalBinary.Specifications.SignalSession.Run
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon

@[expose] public section

set_option autoImplicit false

/-!
# One engine process of the `libsignal-cli` CLI: the extern hook contracts

**Trusted in part.** The headlines of `Computational/Theorems/Main.lean`
(`libsignal_cli_pq_secure_elf_binary_placed` and `libsignal_cli_pq_binary_correct_placed`, see
`Computational/docs/TRUSTED_BASE.md`), together with the symbolic binary headlines
`signal_session_secure_placed` (`Symbolic/Theorems/Security.lean`) and `comp_refines_cli_placed`
(`Symbolic/Theorems/Refinement.lean`), use `17` of the `22` definitions in this file via the
`37`-row relocatable hook table `cliHookTablePlaced` and `Placed.cliRunPlacedSig`
(`CliBinaryPq.lean`): `CliHooks`, `PathOk`, `Utf8Ok`, `ancestors`, `blockingAncestor?`,
`cliBcmpHook`, `durationSinceExactHook`, `fromUtf8Hook`, `isUnmodelledPathComponent`, `memrchrHook`,
`pathComps`, `readPath`, `strlenHook`, `unitResult`, `unmodelled`, `writeFileHook`, and
`writeStdoutHook`. The remaining `5` definitions—`readFileHook`, `readStdinHook`, `vecEmptyOk`,
`vecErr`, and `vecOk`—left the headline closure when F3 + IO.6b de-hooked `lsReadFileSym` and
`lsReadStdinSym` (`cliDehookedSymsPlaced` in `CliBinaryPq.lean`) so the linked `libsignal-cli-io`
ELF code executes; they are kept here outside the headline cone for fixed-image/legacy proofs and
read-loop correspondence. A reader who trusts those theorems trusts, from here:

* `PathOk` (with `readPath`, `pathComps`, `isUnmodelledPathComponent`, `ancestors`,
  `blockingAncestor?`): the file paths the I/O specifications model (relative, canonical, no NUL,
  not a stdio name).
* `unitResult`, `unmodelled` (in the headline closure), and `vecErr`, `vecEmptyOk`, `vecOk`
  (outside the headline closure; kept for fixed-image/legacy read-hook proofs): hook return and
  result helpers.
* `writeFileHook`, `writeStdoutHook` (active in `cliHookTablePlaced` until `W-DIS0`), and
  `readFileHook`, `readStdinHook` (de-hooked under F3 in `cliDehookedSymsPlaced`, outside the
  headline closure, kept for fixed-image/legacy proofs): the contracts of the four I/O functions of
  `libsignal-cli-io`.
* `strlenHook`, `memrchrHook`, `fromUtf8Hook` (with `Utf8Ok`), `durationSinceExactHook`,
  `cliBcmpHook`: the other CLI-specific extern contracts.
* `CliHooks`: what a run is quantified over: the abstract primitives and two unobservable choices.

## How hooks are found

`Step prog` fetches every instruction from memory, so `prog.code` plays no part in a run. Under a
multi-block placement `mpl` (`Placed.cliProgPlacedSig mpl mmpl W` in `CliBinaryPq.lean`), at `pc`,
`Program.externAt?` looks up whether `pc` is the placed address `mpl.ρ name` of a hooked extern or
panic symbol (`cliExternsPlacedSig mmpl W`); if so, the step is the hook (`Step.extern`), which may
change any state except frozen memory and the symbol table; otherwise the instruction in memory
runs. Unhooked zero-word stubs decode to `udf #0` and halt (fail closed), and `overrides` are `none`
so compiled code runs for every defined symbol.

## The I/O functions: compiled read paths and the write hook boundary

The CLI does all of its I/O in four `#[inline(never)]` functions of its own I/O crate,
`libsignal-cli-io` (`third_party/libsignal/libsignal-session/cli/io/`, Rust path
`libsignal_cli_io`). `libsignal-session/translation.toml` keeps `libsignal-cli-io` out of
`libsignalSessionMultiLib` (which has a symbol for each: `lsReadFileSym`, `lsWriteFileSym`,
`lsReadStdinSym`, `lsWriteStdoutSym` in `CliBinaryPq.lean`) and `cli/io/translation.toml` translates
it separately into `GeneratedLean.SignalSessionIoPlacedObj` (`signalSessionIoMultiLib`). At the F3 +
IO.6b re-link (`10` trusted hook removals across `M2-1b`: `B2-TLIT` `−2` `RawVec::grow_one` `49 → 47`,
and F3 `−8` rows `47 → 39`, `cliHookTablePlaced_length_guard`—`7` de-hooked in
`cliDehookedSymsPlaced` (`2` read, `5` `__rust_*` onto `VerifiedLibraries.mallocngLib`) plus
`<String as Clone>::clone` as an intra-library block under SC-1 route (I)), `read_file` and
`read_stdin` are de-hooked and execute the linked `libsignal-cli-io` ELF bytes (bounded C-ABI musl
`open`/`read`/`close`/`__errno_location` loops in `SignalSessionIoPlacedObj`, proved in
`LibsignalBinary/Proofs/SignalSession/CliIo/`); `readFileHook`, `readStdinHook`, `vecEmptyOk`,
`vecErr`, and `vecOk` remain in this file outside the headline closure for fixed-image/legacy proofs
(with retired fixed-image `cliHookTable`, `cliExterns`, `cliBase`, and the demangled I/O stub-name
constants proof-side in `LibsignalBinary/Proofs/SpecLemmas/SignalSession/CliRunFixed.lean`). On the
write side, `cli/io/src/lib.rs` implements `write_file` and `write_stdout` as 0-allocation C-ABI
musl `open`/`write`/`close`/`__errno_location` loops (`< 4096`-B NUL-free stack path check,
`O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC` mode `0o666`, `EINTR` retry, `n == 0` treated as `Err`,
and `EBADF` on `fd = 1` treated as `Ok(())` matching `std`'s `handle_ebadf` and `read_stdin`), which
remain zero stubs and disclosed trusted hooks (`writeFileHook`, `writeStdoutHook`) in
`cliHookTablePlaced` until `W-DIS0` proves their compiled blocks (DEV-CLI4, DEV-CLI8, DEV-CLI21,
DEV-CLI19). Paths are relative to the party's directory and looked up by their canonical form
(`FsState.files`), as `Process.lean` describes.

**Only `write_file` changes the files, and it says so in the trace.** Of all the hooks of
`cliExternsPlaced mmpl W` (`CliBinaryPq.lean`), only `writeFileHook` changes `fs.files`, and every
other active hook leaves `fs` alone (legacy `readStdinHook`, like compiled `read_stdin`, changes
only file descriptor 0's offset). `writeFileHook` also appends one
`TraceEvent.fileChanged path` event on every `PathOk` `< 4096`-byte path call that reaches `openat`
(written or not; paths with an interior NUL or `len ≥ 4096` return `Err` before `openat`), the event the
engine's `openat` appends when it creates or truncates a file, so a run segment whose trace has no
such event did not call `write_file` on a valid path and left `fs.files` as it was. The event is not output:
stdout keeps only `writeByte` events (`traceStreamBytes`), so it changes neither `outcomeOf` nor
the run's `Outcome`.

**DEV-CLI4 (machine model): I/O does not fail except as specified.** The I/O specifications
fail only where Linux / the bounded I/O crate fails on the engine's file system for these calls: a
path of `4096` bytes or more (`ENAMETOOLONG`) or containing an interior NUL byte, a path through a
regular file (`ENOTDIR`), a missing parent directory on write (`ENOENT`), a directory where a file is
expected (`EISDIR`), a regular file above `fileCapBytes` (`2^21`) on `read_file`, standard input
above `stdinCapBytes` (`2^20`) on `read_stdin`, and an out-of-memory allocation failure on a read
buffer (DEV-CLI15, DEV-CLI21; `vecOk` in the legacy hook model). On the linked compiled read paths
(`cli/io/src/lib.rs`, de-hooked in `cliDehookedSymsPlaced` at F3's `47 → 39` cutover,
`cliHookTablePlaced_length_guard`, and proved in `LibsignalBinary/Proofs/SignalSession/CliIo/`),
`read_stdin` and `read_file` enforce those same
`stdinCapBytes = 2^20`, `fileCapBytes = 2^21`, and `< 4096`-byte NUL-free stack-path bounds (mapping
`ENOENT` to `Ok([])` and `EBADF` on `fd 0` to `Ok(out)`), while `write_file` and `write_stdout` are
0-allocation C-ABI musl `open`/`write`/`close`/`__errno_location` loops (`< 4096`-byte NUL-free stack
path check, `O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC` mode `0o666`, `EINTR` retry, `n == 0` treated
as `Err`, `close` on every exit after `open`, and `EBADF` on closed `fd 1` treated as `Ok(())`
matching `std`'s `handle_ebadf` and `read_stdin`; in `processInputs` `fd 1` is open `.stdio` stdout)
and remain trusted disclosed hooks in `cliHookTablePlaced` until `W-DIS0` proves their compiled
blocks (DEV-CLI19). At the `write_file` / `write_stdout` hook boundary no file descriptors are
opened or closed and no write system calls are executed until `W-DIS0`. A real
kernel can also fail for other reasons (`EMFILE`, `ENOSPC`, `EIO`, a denied permission (`EACCES`; no
mode bits), a short write, a full disk
mid-commit); such a failure gives exit 2 in the real CLI, possibly after a partial commit. Effect:
the theorems say nothing about runs on which the kernel fails an I/O call in another way; the run
otherwise ends as the real one does (same exit code, stdout and files).

**DEV-CLI8 (machine model): the hooked I/O model omits real read `Vec`-growth allocations.**
Compiled `libsignal-cli-io` (`read_stdin`, `read_file`, executed directly in the binary theorems)
reads through `4096`-B stack buffers and grows output `Vec<u8>`s on a doubling schedule up to
`stdinCapBytes` / `fileCapBytes` (DEV-CLI21), whereas the legacy read hooks (`readFileHook`,
`readStdinHook`, outside the headline closure) allocate a single exact-size block via `vecOk` and
`write_file` / `write_stdout` perform zero heap allocations. Legacy hook-form theorems make no claim
when a doubling allocation fails where `vecOk`'s exact-size block fits.

**DEV-CLI19 (machine model): write I/O hooks in `cliHookTablePlaced` (`write_file`/`write_stdout` until `W-DIS0`; `read_file`/`read_stdin` de-hooked at F3).**
At the F3 + IO.6b re-link (`10` trusted hook removals across `M2-1b`: `B2-TLIT` `−2`
`RawVec::grow_one` `49 → 47`, and F3 `−8` rows `47 → 39`, `cliHookTablePlaced_length_guard`—`7`
de-hooked in `cliDehookedSymsPlaced` (`2` read, `5` `__rust_*`) plus `<String as Clone>::clone` as
an intra-library block under SC-1 route (I)), `read_file` and `read_stdin` left `cliHookTablePlaced`
and execute compiled `SignalSessionIoPlacedObj` blocks proved against musl
`open`/`read`/`close`/`__errno_location` in `LibsignalBinary/Proofs/SignalSession/CliIo/`, while the
`2` write functions `write_file` and `write_stdout` (`0`-allocation C-ABI musl
`open`/`write`/`close`/`__errno_location` loops in `SignalSessionIoPlacedObj`, with `0` GNU-`std` /
`core::io` undefineds and `0` allocator or panic relocations in `write_*`) remain zero stubs in the
ELF and disclosed trusted hooks (`writeFileHook`, `writeStdoutHook`, and budget-threaded
`WriteFileEnv` / `WriteStdoutEnv` in `LibsignalBinary/Heap/SpecBudget.lean` with `0`
`withVmPreserved`/`liftVm` wrappers at call sites) in `cliHookTablePlaced` until `W-DIS0` proves
their compiled blocks.

Paths outside the modelled set (`PathOk`: non-canonical, a NUL byte, a component that `fsView`
hides) and
caller buffers that are not readable / writable make the hooks fail closed (`.Exception`), as do
the other CLI-specific hooks on bad inputs. The shared hooks (`memmove`, `bcmp`, the primitives)
check no permissions.

## Free choices

`W : CliHooks` holds the abstract primitives (`C`, `Q`) and two
free choices that the CLI cannot observe: `bcmp`'s nonzero value and `from_utf8`'s `Err` payload.
The binary theorem must show that the exit code, stdout and files do not depend on them; the CLI
tests only `w0 = 0` after `bcmp`, and only `is_ok` after `from_utf8` (argv parsing: `.ok()`; the
`address` file: `map_err`).

## Notable rows of `cliHookTablePlaced` (`CliBinaryPq.lean`)

* not hooked: `std::sys::random::linux::hashmap_random_keys` (the CLI builds no `HashMap`) and
  `libsignal_session_rng_fill` (the CLI's coins are plain Rust, `cli/src/coins.rs`); reaching
  either halts (fail closed by design);
* not hooked since the stock `ld.lld` cutover: `memset` and `memcpy` (in `cliDehookedSymsPlaced`;
  the run executes the linked `VerifiedLibraries.mallocngLib` blocks `21` / `20`). `memmove` is
  still hooked: its row is `hookMemmove`, an `abbrev` of `hookMemcpy`
  (`ProofLib/Hoare/LibcHooks.lean`), so `hookMemcpy` stays trusted through that row;
* `duration_since`: the exact `std` result (`durationSinceExactHook`), not a free choice;
  the CLI's clock is the constant `SystemTime::UNIX_EPOCH` (`cli/src/lib.rs`), so the stored
  `pending_pre_key.timestamp` is determined;
* `bcmp`: `cliBcmpHook W.bcmp`, the `bcmp` hook with its nonzero value taken from `W`;
* CLI-specific: `strlen` (argv), `core::slice::memchr::memrchr` (`rsplit_once('.')` on an address),
  `core::str::converts::from_utf8` (argv; the `address` file), and `write_file` / `write_stdout`
  (above; `read_file` and `read_stdin` are de-hooked in `cliDehookedSymsPlaced`).
* `core::fmt::write` (`Ok`, nothing written) and `format_inner`
  (an empty `String`). Their results reach no stdout byte, path or file of the CLI: the CLI's own
  code (`cli/src/`, the I/O crate) uses no `format!` / `write!` / `to_string` (it builds decimal
  numbers and address text by hand, `stores.rs`), so a `core::fmt` call can come only from library
  code whose text the CLI never prints or stores.

Names: sret = the result buffer whose address the caller passes in `x8`.
-/


namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib

/-! ## Paths -/

/-- The path argument `(ptr, len)` of an I/O function as an `FsState.files` key: one character per
byte (`Char.ofNat`), as the engine reads a path of `openat` (`readCString`, `ISA/Eval.lean`). -/
def readPath (m : Memory) (ptr len : BitVec 64) : String :=
  String.ofList ((m.readBytes ptr len.toNat).map fun b => Char.ofNat b.toNat)

/-- The components of path `p`: its characters split at `/` (`List.splitOn`). On a `PathOk` path
they are the segments of the engine's canonical form (`Arm64.normalizePath`). -/
def pathComps (p : String) : List (List Char) := p.toList.splitOn '/'

/-- A component the specifications do not model: empty (a leading, trailing or doubled `/`, or the
empty path), `.` or `..`. -/
def isUnmodelledPathComponent (c : List Char) : Bool := c.isEmpty || c == ['.'] || c == ['.', '.']

/-- **The paths the I/O specifications model**: relative and canonical (every component non-empty
and neither `.` nor `..`), no NUL byte (Rust's `CString` would reject it), and no component that
`fsView` hides (`stdioPaths`, `Run.lean`), so every file a hook reads or writes is observable. The
standard streams themselves are not in the file system (`FsState.files`): the loader opens file
descriptors 0, 1, 2 as `.stdio` descriptors, and stdin's bytes are `FsState.stdin`.
On such paths the engine's canonical lookup (`FsState.files`) agrees with the way Linux resolves
them. -/
def PathOk (p : String) : Bool :=
  (pathComps p).all fun c =>
    !isUnmodelledPathComponent c && !c.contains '\x00' && !(stdioPaths.contains (String.ofList c))

/-- The proper ancestors of `p`, shallowest first: `"a/b/c"` gives `["a", "a/b"]`; a single
component has none (its parent is the party's directory, which exists). -/
def ancestors (p : String) : List String :=
  let cs := pathComps p
  (List.range (cs.length - 1)).map fun i => String.ofList (['/'].intercalate (cs.take (i + 1)))

/-- **The first proper ancestor of `p` that is not a directory**, with what is there: `some
(some (.file _))` (Linux: `ENOTDIR`) or `some none` (missing: `ENOENT`); `none` if every proper
ancestor is a directory. This is Linux's walk of the path's directories (`link_path_walk`). -/
def blockingAncestor? (fs : FsState) (p : String) : Option (Option FsEntry) :=
  ((ancestors p).find? fun q => match fs.files q with | some .dir => false | _ => true).map
    fs.files

/-! ## Results -/

/-- `Err(IoError)` of a `Result<Vec<u8>, IoError>` at sret `x8` (capacity niche
`0xFFFF_FFFF_FFFF_FFFF` at `[x8]`, then return; legacy read-hook helper). -/
def vecErr : State → State :=
  retHook fun s => s.setMem (s.mem.write64 (s.readReg64 .x8) 0xFFFFFFFFFFFFFFFF#64)

/-- `Ok(Vec::new())` at sret `x8` (`{cap = 0, ptr = 1, len = 0}` via `E2E.writeVecHeader`, then
return; legacy read-hook helper). -/
def vecEmptyOk : State → State :=
  retHook fun s => s.setMem (E2E.writeVecHeader s.mem (s.readReg64 .x8) 0#64 1#64 0#64)

/-- `Ok(bs)` at the sret (legacy read-hook model, outside the `Computational/Theorems/` headline
closure since F3 de-hooked `read_file` and `read_stdin` in `cliDehookedSymsPlaced`; kept for
fixed-image/legacy proofs): `vecEmptyOk` for empty `bs`; otherwise a lowest-fit heap block of
`bs.length` bytes (`E2E.bumpThen`, the allocator hooks' block), `bs` copied in, the header
`{len, block, len}`. If no block fits: `E2E.allocPanicHook` (log `allocFailedEvent`, then
`.Panicked`), as for every other failed allocation of the legacy hook-allocator CLI. Why: compiled
`libsignal_cli_io::{read_file, read_stdin}` (`cli/io/src/lib.rs`) grow their output `Vec<u8>` via
`Vec::reserve_exact` (`4096 * 2^j` up to `1 MiB` / `2 MiB`), which calls `handle_alloc_error`
(abort) on OOM rather than returning `Err`.
**Modelling choice: capacity = length.** Compiled `read_stdin` / `read_file` return a power-of-two
capacity `4096 * 2^j >= bs.length` (`CliIo.ReadLoopCommon.cliIoFinalCap`). The CLI
never grows these vectors, `__rust_dealloc` is a no-op hook in the legacy hook model (DEV-E6), and
nothing the CLI prints or writes depends on a capacity or a heap address, so the run's exit code,
stdout and files are the same. Hooks are functions of the state (`Program.externs`), so a range of
capacities would need one more free choice in `CliHooks`.
This argument is about runs in which every allocation succeeds: a larger real power-of-two capacity
within `stdinCapBytes` / `fileCapBytes` can fail where `vecOk`'s exact-size block fits (DEV-CLI8). -/
noncomputable def vecOk (bs : List (BitVec 8)) : State → State :=
  if bs.isEmpty then vecEmptyOk
  else
    E2E.bumpThen bs.length 1
      (fun s p => retHook (fun s =>
        let n := BitVec.ofNat 64 bs.length
        s.setMem (E2E.writeVecHeader (s.mem.writeBytes p bs) (s.readReg64 .x8) n p n)) s)
      E2E.allocPanicHook

/-- Return `Ok(())` (`x0 := 0`) or `Err(IoError)` (`x0 := 1`) of a `Result<(), IoError>`
(measured on the compiled `write_file` / `write_stdout`: `cset w0, ne`). -/
def unitResult (ok : Bool) : State → State :=
  retHook fun s => s.writeReg64 .x0 (if ok then 0#64 else 1#64)

/-- Stop with an `.Exception` (`outcomeOf` is then `none`): the hook's inputs are outside what it
models. -/
def unmodelled (msg : String) (s : State) : State := s.setStatus (.Exception msg)

/-! ## The four I/O functions (the I/O crate `libsignal-cli-io`), at their stubs -/


/-- Legacy hook contract for `libsignal_cli_io::read_file(path: &str = (x0, x1)) -> Result<Vec<u8>, IoError>`
(sret `x8`), de-hooked under F3 (`lsReadFileSym` in `cliDehookedSymsPlaced`, outside the headline
closure): bounded read (`≤ fileCapBytes = 2^21`) with missing paths/ancestors mapped to `Ok([])`,
paths with `len ≥ cliPathMaxBytes` (`4096`), interior NUL, non-directory ancestor, directory target,
or size `> fileCapBytes` mapped to `Err` (`vecErr`), and non-`PathOk` or inaccessible memory mapped
to `.Exception`. -/
noncomputable def readFileHook (s : State) : State :=
  let ptr := s.readReg64 .x0
  let len := s.readReg64 .x1
  if !(s.mem.canRead ptr len.toNat && s.mem.canWrite (s.readReg64 .x8) 24) then
    unmodelled "read_file: unreadable path or unwritable result" s
  else
    let raw := s.mem.readBytes ptr len.toNat
    if cliPathMaxBytes ≤ len.toNat || raw.contains 0#8 then
      vecErr s
    else
      let p := readPath s.mem ptr len
      if !PathOk p then unmodelled "read_file: path outside the model" s
      else
        match blockingAncestor? s.fs p with
        | some (some _) => vecErr s
        | some none => vecEmptyOk s
        | none =>
          match s.fs.files p with
          | some (.file bs) =>
            if bs.length ≤ fileCapBytes then vecOk bs s else vecErr s
          | some .dir => vecErr s
          | none => vecEmptyOk s

/-- `libsignal_cli_io::write_file(path: &str = (x0, x1), bytes: &[u8] = (x2, x3))
-> Result<(), IoError>` (`x0`): 0-allocation C-ABI musl `open`/`write`/`close`/`__errno_location`
loop (`O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC`, mode `0o666`, `< 4096`-byte NUL-free stack path
copy, `EINTR` retry on `open` and `write`, `n == 0` treated as `Err`, `close` on every exit after
`open`), i.e. create or truncate, then write all of `bytes`.
* `.Exception` if the path or the bytes are not readable, or (after the length / interior-NUL
  check) the path is not `PathOk`;
* path byte length `≥ cliPathMaxBytes` (`4096`, `PATH_MAX`) or containing an interior `0` byte:
  `Err` (`unitResult false`, before `openat` and before emitting `TraceEvent.fileChanged`);
* a proper ancestor is not a directory (a regular file: `ENOTDIR`; missing: `ENOENT`, the CLI
  never creates a directory): `Err`, nothing changes in `fs.files`;
* `fs.files path` is a directory: `Err` (`EISDIR`), nothing changes in `fs.files`;
* otherwise (a regular file, or nothing): `fs.files path := file bytes`, `Ok`.
In the three `PathOk` `< 4096`-byte cases it first appends the event `TraceEvent.fileChanged p` to
the trace (not output; module docstring). -/
def writeFileHook (s : State) : State :=
  let ptr := s.readReg64 .x0
  let len := s.readReg64 .x1
  let buf := s.readReg64 .x2
  let n := s.readReg64 .x3
  if !(s.mem.canRead ptr len.toNat && s.mem.canRead buf n.toNat) then
    unmodelled "write_file: unreadable path or bytes" s
  else
    let raw := s.mem.readBytes ptr len.toNat
    if cliPathMaxBytes ≤ len.toNat || raw.contains 0#8 then
      unitResult false s
    else
      let p := readPath s.mem ptr len
      if !PathOk p then unmodelled "write_file: path outside the model" s
      else
        let s := s.appendTrace [.fileChanged p]
        match blockingAncestor? s.fs p, s.fs.files p with
        | some _, _ => unitResult false s
        | none, some .dir => unitResult false s
        | none, _ =>
          unitResult true (s.setFs (s.fs.setFile p (some (.file (s.mem.readBytes buf n.toNat)))))

/-- Legacy hook contract for `libsignal_cli_io::read_stdin() -> Result<Vec<u8>, IoError>` (sret
`x8`), de-hooked under F3 (`lsReadStdinSym` in `cliDehookedSymsPlaced`, outside the headline
closure): bounded read (`≤ stdinCapBytes = 2^20`) on readable `.stdio` `fd 0`, advancing `offset` by
`rest.length` on `Ok(rest)` (`vecOk`) or by `stdinCapBytes + 1` on over-cap `Err` (`vecErr`), and
stopping with `.Exception` otherwise. -/
noncomputable def readStdinHook (s : State) : State :=
  if !s.mem.canWrite (s.readReg64 .x8) 24 then unmodelled "read_stdin: unwritable result" s
  else
    match s.fs.fds 0#64 with
    | some e =>
      if e.kind == .stdio && e.accMode.canRead then
        let rest := s.fs.stdin.drop e.offset
        if rest.length ≤ stdinCapBytes then
          vecOk rest (s.setFs (s.fs.setFd 0#64 (some { e with offset := e.offset + rest.length })))
        else
          vecErr (s.setFs (s.fs.setFd 0#64 (some { e with offset := e.offset + (stdinCapBytes + 1) })))
      else unmodelled "read_stdin: file descriptor 0 is not readable standard input" s
    | none => unmodelled "read_stdin: file descriptor 0 is closed" s

/-- `libsignal_cli_io::write_stdout(bytes: &[u8] = (x0, x1)) -> Result<(), IoError>` (`x0`):
0-allocation C-ABI musl `write(1, …)` / `__errno_location` loop (`EINTR` retry, `n == 0` treated
as `Err`, and `EBADF` on a closed file descriptor 1 treated as `Ok(())` matching `std`'s
`handle_ebadf` and `read_stdin`; in `processInputs` file descriptor 1 is open `.stdio` stdout),
i.e. the engine's `write(1, …)`, which appends the bytes to the trace as stdout events
(`TraceEvent.ofBytes .stdout`) and leaves the file system unchanged. `Ok`.
`.Exception` if the bytes are not readable. -/
def writeStdoutHook (s : State) : State :=
  let buf := s.readReg64 .x0
  let n := s.readReg64 .x1
  if !s.mem.canRead buf n.toNat then unmodelled "write_stdout: unreadable bytes" s
  else unitResult true (s.appendTrace (TraceEvent.ofBytes .stdout (s.mem.readBytes buf n.toNat)))

/-! ## CLI-specific extern hooks -/

open Classical in
/-- `strlen(s = x0) -> size_t` (`x0`): the least `n` such that the bytes `[s, s + n]` are readable
and byte `s + n` is `0`. `.Exception` if there is none (a real `strlen` faults or runs on). Caller:
`CStr::from_ptr` on each argument of `argv`, which the loader writes NUL-terminated. -/
noncomputable def strlenHook (s : State) : State :=
  let p := s.readReg64 .x0
  if h : ∃ n, s.mem.canRead p (n + 1) = true ∧ s.mem.read8 (p + BitVec.ofNat 64 n) = 0#8 then
    retHook (fun s => s.writeReg64 .x0 (BitVec.ofNat 64 (Nat.find h))) s
  else unmodelled "strlen: no readable NUL" s

/-- `core::slice::memchr::memrchr(x: u8 = w0, text: &[u8] = (x1, x2)) -> Option<usize>`
(`x0` = tag, `x1` = value): `Some(i)` (`x0 := 1`, `x1 := i`) for the largest `i < len` with
`text[i] = x` (`x`: the low byte of `x0`), else `None` (`x0 := 0`, `x1` unchanged). `.Exception`
if the bytes are not readable. Caller: `rsplit_once('.')` in `address` (`cli/src/lib.rs`), which
tests `x0 = 1`. -/
def memrchrHook (s : State) : State :=
  let x := (s.readReg64 .x0).setWidth 8
  let ptr := s.readReg64 .x1
  let len := s.readReg64 .x2
  if !s.mem.canRead ptr len.toNat then unmodelled "memrchr: unreadable bytes" s
  else
    let bs := s.mem.readBytes ptr len.toNat
    match ((List.range bs.length).filter fun i => bs[i]? == some x).getLast? with
    | some i => retHook (fun s => (s.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s
    | none => retHook (fun s => s.writeReg64 .x0 0#64) s

/-- **`bs` is well-formed UTF-8**: the UTF-8 encoding (`String.utf8EncodeChar`, shortest form) of
some list of Unicode scalar values (`Char`: no surrogates, at most U+10FFFF). This is Rust's
definition (`core::str::from_utf8`); equivalently `∃ s : String, s.toUTF8.toList = bs` up to
`UInt8.toBitVec`. -/
def Utf8Ok (bs : List (BitVec 8)) : Prop :=
  ∃ cs : List Char, (cs.flatMap String.utf8EncodeChar).map UInt8.toBitVec = bs

open Classical in
/-- `core::str::converts::from_utf8(v: &[u8] = (x0, x1)) -> Result<&str, Utf8Error>` (sret `x8`,
24 bytes): if the bytes are well-formed UTF-8 (`Utf8Ok`), `Ok(v)`: tag `0` @0, `x0` @8, `x1` @16.
Otherwise `Err`: tag `1` @0, then `err bs = (valid_up_to, error_len)`, a free choice, as the word
@8 and the 16-bit field @16. `.Exception` if the bytes are not readable or the sret not writable.
(Measured on the compiled `from_utf8`: `str xzr, [x8]; stp x0, x1, [x8, #8]` and
`str x9(=1), [x8]; str x9, [x8, #8]; strb, strb [x8, #16..17]`.) -/
noncomputable def fromUtf8Hook (err : List (BitVec 8) → BitVec 64 × BitVec 16) (s : State) :
    State :=
  let ptr := s.readReg64 .x0
  let len := s.readReg64 .x1
  let r := s.readReg64 .x8
  if !(s.mem.canRead ptr len.toNat && s.mem.canWrite r 24) then
    unmodelled "from_utf8: unreadable bytes or unwritable result" s
  else
    let bs := s.mem.readBytes ptr len.toNat
    if Utf8Ok bs then
      retHook (fun s => s.setMem (((s.mem.write64 r 0#64).write64 (r + 8#64) ptr).write64
        (r + 16#64) len)) s
    else
      retHook (fun s => s.setMem (((s.mem.write64 r 1#64).write64 (r + 8#64) (err bs).1).write16
        (r + 16#64) (err bs).2)) s

/-- `<SystemTime>::duration_since(&self = x0, earlier = (x1 = tv_sec, w2 = tv_nsec))
-> Result<Duration, SystemTimeError>` (sret `x8`), exactly `std`'s `Timespec::sub_timespec`. With
`t1` = `self` (`tv_sec: i64` @0, `tv_nsec: u32` @8) and `t2` = `earlier`, each read as
`tv_sec · 10^9 + tv_nsec` nanoseconds (an integer), and `d = |t1 - t2|`: tag @0 = `0` (`Ok`) if
`t1 ≥ t2`, else `1` (`Err`); the `Duration` `(d / 10^9, d % 10^9)` as `secs: u64` @8 and
`nanos: u32` @16. `.Exception` if `self`'s 12 bytes are not readable, the 24 sret bytes are not
writable, or a `tv_nsec` is `≥ 10^9` (not a `Timespec`: undefined behaviour in Rust). (Measured on
the compiled `duration_since` / `sub_timespec`: `ldr x9, [x1]; ldr w12, [x1, #8]` with `self` in
`x1` after `mov x1, x9(=x0)`, `earlier` stored from `x1` / `w2`; `stp xzr, x9, [x19];
str w8, [x19, #16]` for `Ok`, the tag XOR-ed with `1` for `Err`.) Every call site passes
`UNIX_EPOCH` as `earlier`. -/
def durationSinceExactHook (s : State) : State :=
  let a := s.readReg64 .x0
  let r := s.readReg64 .x8
  if !(s.mem.canRead a 12 && s.mem.canWrite r 24) then
    unmodelled "duration_since: unreadable self or unwritable result" s
  else
    let ns1 := (s.mem.read32 (a + 8#64)).toNat
    let ns2 := ((s.readReg64 .x2).setWidth 32).toNat
    if ns1 < 1000000000 ∧ ns2 < 1000000000 then
      let t1 : Int := (s.mem.read64 a).toInt * 1000000000 + ns1
      let t2 : Int := (s.readReg64 .x1).toInt * 1000000000 + ns2
      let d := (t1 - t2).natAbs
      let tag : BitVec 64 := if t2 ≤ t1 then 0#64 else 1#64
      retHook (fun s => s.setMem (((s.mem.write64 r tag).write64 (r + 8#64)
        (BitVec.ofNat 64 (d / 1000000000))).write32 (r + 16#64)
        (BitVec.ofNat 32 (d % 1000000000)))) s
    else unmodelled "duration_since: tv_nsec out of range" s

/-! ## The free choices and the table -/

/-- **What a CLI run is quantified over** (the `W` of `cliRunOf elf W` and `cliRunAbortOnPanic elf W`): the
abstract primitives and two results the CLI cannot observe. -/
structure CliHooks where
  /-- SHA-256 compression, AES-256-CBC, X25519 (`CryptoGames.LibsignalSession.Crypto`). -/
  C : CryptoGames.LibsignalSession.Crypto
  /-- SHA-512, the Ed25519 curve core, Kyber1024, SPQR's ML-KEM-768 (`E2E.PqxdhPrims`). -/
  Q : E2E.PqxdhPrims
  /-- `bcmp`'s `x0` on the two compared byte strings. -/
  bcmp : List (BitVec 8) → List (BitVec 8) → BitVec 64
  /-- On equal lengths, the low 32 bits are zero exactly when the strings are equal (C's
  contract). -/
  bcmp_ok : ∀ a b, a.length = b.length → ((bcmp a b).setWidth 32 = 0#32 ↔ a = b)
  /-- `from_utf8`'s `Err` payload `(valid_up_to, error_len)` on ill-formed bytes. -/
  utf8Err : List (BitVec 8) → BitVec 64 × BitVec 16

/-- `bcmp(a = x0, b = x1, n = x2) -> int`: `x0 := bcmp (n bytes at a) (n bytes at b)`, return:
the function-level (C-ABI) `bcmp` contract with the value function `bcmp`. Unlike the
CLI-specific hooks above it checks no permission (it does not fail closed): on unreadable bytes it
over-approximates, reading them anyway, as the function-level contract does, so that the
function-level proofs' `bcmp` facts transfer unchanged. -/
def cliBcmpHook (bcmp : List (BitVec 8) → List (BitVec 8) → BitVec 64) : State → State :=
  retHook fun s =>
    let n := (s.readReg64 .x2).toNat
    s.writeReg64 .x0 (bcmp (s.mem.readBytes (s.readReg64 .x0) n)
      (s.mem.readBytes (s.readReg64 .x1) n))


end CryptoVerification.SignalSession
