/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import VerifiedLibraries.RustStd.Spec.IoCommon
public import VerifiedLibraries.RustStd.Spec.CoreMemrchr

/-!
# Specifications of Compiled `std::io` Standard Streams

Machine-level specifications for compiled `std::io` standard-stream routines (Rust 1.98.1,
`std/src/io/stdio.rs`):
- `std::io::stdio::stdin() -> Stdin`: no arguments; returns `x0 = &INSTANCE`
  (`std::io::stdio::stdin::INSTANCE`, a `OnceLock<Mutex<BufReader<StdinRaw>>>`), allocating the
  8192-byte read buffer on first call.
- `<Stdin as Read>::read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize>`:
  `x0 = &mut Stdin` (a slot holding `&INSTANCE`), `x1 = &mut Vec<u8>` (24-byte header
  `{cap, ptr, len}`); returns `(x0, x1) = (0, n)` for `Ok(n)` and `(1, repr)` for `Err`.
- `std::io::stdio::stdout() -> Stdout`: no arguments; returns `x0 = &STDOUT`
  (`std::io::stdio::STDOUT`, a `OnceLock<ReentrantLock<RefCell<LineWriter<StdoutRaw>>>>`),
  allocating the 1024-byte line buffer on first call.
- `<Stdout as Write>::write_all(&mut self, buf: &[u8]) -> io::Result<()>`:
  `x0 = &mut Stdout` (a slot holding `&STDOUT`), `x1 = buf`, `x2 = len`; returns `x0 = 0`.
- `<Stdout as Write>::flush(&mut self) -> io::Result<()>`: `x0 = &mut Stdout`; returns `x0 = 0`.

## Model Assumptions and Footprints

- Single-threaded execution: fd 0 is open, of kind `.stdio`, and readable (`read_to_end`); the
  stream objects, `GLOBAL_PANIC_COUNT`, and the thread-id counter are accessed only through these
  entry points with locks free at entry (no reentrant calls).
- Panic and exit paths (`RefCell` borrow failure, `ReentrantLock` count overflow, `ThreadId::new`
  exhaustion, `GLOBAL_PANIC_COUNT` slow path, slice index failure) are unreachable under the
  preconditions (`onPanic` and `onExit` default to `⌜False⌝`). Only allocating calls (`stdin`,
  `stdout` on first initialization, and `read_to_end`) may stop with `.OutOfMemory`.
- Footprints:
  - Every routine requires its stream object (`StdinAt` / `StdoutAt`), `haveLseAtomics ↦₈ᵣ haveLse`
    (read by outline atomics `__aarch64_{cas4_acq, cas8_relax, swp4_acq, swp4_rel}`),
    `RustStdStdioAddrs.Aligned`, and `stackBytes` bytes of stack (`stackFrameAt`).
  - `stdin` and `stdout` additionally take the `Once` closure vtable `+0x20` slot, `StdErrnoCell`,
    and the allocator pool.
  - `read_to_end`, `write_all`, and `flush` additionally take `StdErrCells` and `StdioRoCells`.
  - `read_to_end` takes the `&mut Stdin` slot, the `Vec` header, `GLOBAL_PANIC_COUNT ↦₆₄ᵣ 0`, and
    the allocator pool; `write_all` and `flush` take the `&mut Stdout` slot and `StdThreadIdCells`
    (plus `stdoutBytesAt` for `write_all`).
- Consumer obligations:
  - Tie each field of `RustStdStdioAddrs` and `RustStdIoAddrs` to its placed symbol address
    (`stdinInitFn` / `stdoutInitFn` are the relocated words at `.Lanon.7 + 0x20` / `.Lanon.3 + 0x20`;
    `tlsIdOff` is the TLSDESC-to-local-exec thread-pointer offset for `std::thread::current::id::ID`).
  - Freeze writable startup cells (`haveLseAtomics`, `panicCount = 0`, and the two vtable slots)
    to read-only points-to assertions before the first call (`pointsTo8_freeze_ro` /
    `pointsTo64_freeze_ro`), and initialize stream objects as `StdinAt A saddrs false` and
    `StdoutAt A saddrs none`.
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64

/-! ## Statics -/

/-- Placed addresses of the statics the standard-stream routines use (beyond `RustStdIoAddrs`):
    - `stdinInst`: `std::io::stdio::stdin::INSTANCE` (56 bytes, 8-aligned, `.data`);
    - `stdoutInst`: `std::io::stdio::STDOUT` (64 bytes, 8-aligned, `.data`);
    - `stdinOnceVtbl`, `stdinInitFn`: the `Once` closure vtable of `stdin` (`.Lanon.7`) and the
      code address in its `+0x20` slot (the `call_once_force` closure that initializes
      `INSTANCE`);
    - `stdoutOnceVtbl`, `stdoutInitFn`: the same for `stdout` (`.Lanon.3`);
    - `panicCount`: `std::panicking::panic_count::GLOBAL_PANIC_COUNT` (8 bytes, `.bss`);
    - `threadIdCounter`: `<std::thread::id::ThreadId>::new::COUNTER` (8 bytes, `.bss`);
    - `tlsIdOff`: the offset from the thread pointer of the thread-local
      `std::thread::current::id::ID` (8 bytes, `0` = no id yet);
    - `haveLseAtomics`: `__aarch64_have_lse_atomics` (1 byte, `.bss` of `compiler_builtins`). -/
structure RustStdStdioAddrs where
  stdinInst : BitVec 64
  stdoutInst : BitVec 64
  stdinOnceVtbl : BitVec 64
  stdinInitFn : BitVec 64
  stdoutOnceVtbl : BitVec 64
  stdoutInitFn : BitVec 64
  panicCount : BitVec 64
  threadIdCounter : BitVec 64
  tlsIdOff : BitVec 64
  haveLseAtomics : BitVec 64

/-- The alignment the atomic accesses need (`ldar` / `ldaxr` / `cas` fault on an unaligned
    address): the two stream objects and the thread-id counter are 8-aligned (the futex words at
    `+0x00` / `+0x08` and the `Once` words at `+0x30` / `+0x38` are then 4-aligned). -/
def RustStdStdioAddrs.Aligned (saddrs : RustStdStdioAddrs) : Prop :=
  saddrs.stdinInst.toNat % 8 = 0 ∧ saddrs.stdoutInst.toNat % 8 = 0 ∧
    saddrs.threadIdCounter.toNat % 8 = 0

/-! ## Stream Objects -/

variable {oom : State → State → Prop}

/-- `stdin::INSTANCE` at `saddrs.stdinInst`, bytes `[0, 0x34)` (the 4 padding bytes
    `+0x34..+0x37` are not owned):
    - `init = false` (`Once` `INCOMPLETE`): `+0x30 ↦₃₂ 3` and 48 bytes of unspecified contents;
    - `init = true` (`Once` `COMPLETE`, the `Mutex` free, the `BufReader` empty): futex `0` at
      `+0x00`, the poison flag and padding `+0x04..+0x07` (unspecified; read and discarded),
      the buffer pointer `buf` at `+0x08`, capacity `8192` at `+0x10`, `pos = 0` at `+0x18`,
      `filled = 0` at `+0x20`, the `initialized` count and padding `+0x28..+0x2f` (unspecified),
      `Once = 0` at `+0x30`, and the live 8192-byte buffer block at `buf` (contents
      unspecified). -/
def StdinAt (A : RustStdAlloc oom) (saddrs : RustStdStdioAddrs) (init : Bool) : SepProp :=
  let i := saddrs.stdinInst
  if init then
    ∃∗ buf : BitVec 64,
      (i ↦₃₂ 0#32) ∗ memRegion (i + 0x04#64) 4 ∗ ((i + 0x08#64) ↦₆₄ buf) ∗
        ((i + 0x10#64) ↦₆₄ 8192#64) ∗ ((i + 0x18#64) ↦₆₄ 0#64) ∗ ((i + 0x20#64) ↦₆₄ 0#64) ∗
        memRegion (i + 0x28#64) 8 ∗ ((i + 0x30#64) ↦₃₂ 0#32) ∗
        A.live buf 8192 1 ∗ memRegion buf 8192
  else
    memRegion i 0x30 ∗ ((i + 0x30#64) ↦₃₂ 3#32)

/-- The `BufWriter<StdoutRaw>` inside `STDOUT`, at `bw = STDOUT + 0x18`, holding the pending
    bytes `p` (`p.length ≤ 1024`): capacity `1024` at `+0x00`, the buffer pointer at `+0x08`, the
    length `p.length` at `+0x10`, `panicked = 0` at `+0x18`, and the live 1024-byte buffer block
    holding `p` followed by spare capacity. -/
def stdoutBufWriterAt (A : RustStdAlloc oom) (bw : BitVec 64) (p : List (BitVec 8)) : SepProp :=
  ∃∗ bufPtr : BitVec 64,
    ⌜p.length ≤ 1024⌝ ∗
      ((bw ↦₆₄ 1024#64) ∗ ((bw + 8#64) ↦₆₄ bufPtr) ∗
        ((bw + 16#64) ↦₆₄ BitVec.ofNat 64 p.length) ∗ ((bw + 24#64) ↦₈ 0#8) ∗
        A.live bufPtr 1024 1 ∗ (bufPtr ↦ₛ p) ∗
        memRegion (bufPtr + BitVec.ofNat 64 p.length) (1024 - p.length))

/-- `STDOUT` at `saddrs.stdoutInst`, bytes `[0, 0x31)` and `[0x38, 0x3c)` (the padding
    `+0x31..+0x37` and `+0x3c..+0x3f` is not owned):
    - `none` (`Once` `INCOMPLETE`): `+0x38 ↦₃₂ 3` and 49 bytes of unspecified contents;
    - `some p` (`Once` `COMPLETE`, the lock free, the `RefCell` not borrowed): owner `0` at
      `+0x00`, futex `0` at `+0x08`, lock count `0` at `+0x0c`, borrow flag `0` at `+0x10`, the
      `BufWriter` holding the pending bytes `p` at `+0x18` (`stdoutBufWriterAt`), and `Once = 0`
      at `+0x38`. -/
def StdoutAt (A : RustStdAlloc oom) (saddrs : RustStdStdioAddrs) :
    Option (List (BitVec 8)) → SepProp
  | none =>
    memRegion saddrs.stdoutInst 0x31 ∗ ((saddrs.stdoutInst + 0x38#64) ↦₃₂ 3#32)
  | some p =>
    let o := saddrs.stdoutInst
    (o ↦₆₄ 0#64) ∗ ((o + 0x08#64) ↦₃₂ 0#32) ∗ ((o + 0x0c#64) ↦₃₂ 0#32) ∗
      ((o + 0x10#64) ↦₆₄ 0#64) ∗ stdoutBufWriterAt A (o + 0x18#64) p ∗
      ((o + 0x38#64) ↦₃₂ 0#32)

/-! ## Thread IDs and Read-Only Cells -/

/-- The thread's id after a `ReentrantLock` owner check, from the TLS id `tid` and the counter
    `ctr`: a thread without an id (`tid = 0`) takes `ctr + 1` and the counter becomes `ctr + 1`
    (`ThreadId::new`); otherwise both are unchanged. Returns `(tid', ctr')`. -/
def nextThreadId (tid ctr : BitVec 64) : BitVec 64 × BitVec 64 :=
  if tid = 0#64 then (ctr + 1#64, ctr + 1#64) else (tid, ctr)

/-- The thread-id cells for thread pointer `tp`: the thread-local id at `tp + tlsIdOff` holding
    `tid` and `ThreadId::new::COUNTER` holding `ctr`. -/
def StdThreadIdCells (saddrs : RustStdStdioAddrs) (tp tid ctr : BitVec 64) : SepProp :=
  ((tp + saddrs.tlsIdOff) ↦₆₄ tid) ∗ (saddrs.threadIdCounter ↦₆₄ ctr)

/-- The read-only image cell that `read_to_end`, `write_all` and `flush` load: `rust_std_io`'s
    GOT slot for `OS_FUNCTIONS` (never relaxed) holding `addrs.osFunctions`, loaded at
    `<unix::Stdout as Write>::write_all+0x024..0x030` (on every non-empty raw write) and on the
    failed-`read` / failed-`write` paths. As for `IoImageRoCells`, that the slot holds
    `addrs.osFunctions` is a consumer-bridge obligation (the loader makes the GOT read-only but does
    not say what a slot holds). -/
def StdioRoCells (addrs : RustStdIoAddrs) : SepProp :=
  addrs.osFunctionsGot ↦₆₄ᵣ addrs.osFunctions

/-! ## `read_to_end` Capacity Sequence

`read_to_end` on `Stdin` with an empty `Vec` (capacity `0`) runs `default_read_to_end` with no
size hint. With `r` bytes of standard input left:
- `r = 0`: the first probe read returns `0`; no allocation.
- `r > 0`: the probe read takes `n = min 32 r` bytes and `extend_from_slice` allocates capacity
  `max 8 n` (`alloc`, the minimum non-zero capacity of `Vec<u8>` is 8). From then on, whenever the
  buffer is full (length = capacity `c`), `try_reserve(32)` grows it to `max (2 * c) (c + 32)`
  (`realloc`). The loop stops at the first read that returns `0`, which is the first read with
  free capacity after all `r` bytes are in, so the final capacity is the first one above `r`. -/

/-- The `i`-th capacity requested by `read_to_end` with `r` bytes of input (`r > 0`):
    `rteCap r 0 = max 8 (min 32 r)`, `rteCap r (i + 1) = max (2 * c) (c + 32)` with
    `c = rteCap r i`. -/
def rteCap (r : Nat) : Nat → Nat
  | 0 => max 8 (min 32 r)
  | i + 1 => max (2 * rteCap r i) (rteCap r i + 32)

/-- The capacities `read_to_end` requests with `r` bytes of input, in order: `[]` for `r = 0`,
    else `rteCap r 0, ..., rteCap r J` with `J` the least index with `r < rteCap r J` (each request
    after the first is made because the previous capacity was filled, `rteCap r (i - 1) ≤ r`).
    `rteCap` grows by at least 32 per step, so `J ≤ r` and `List.range (r + 1)` covers it. -/
def rteCaps (r : Nat) : List Nat :=
  if r = 0 then []
  else ((List.range (r + 1)).filter fun i => i = 0 ∨ rteCap r (i - 1) ≤ r).map (rteCap r)

/-- The final capacity of the `Vec` after a successful `read_to_end` of `r` bytes: the last
    requested capacity (`0` when nothing was requested). -/
def rteFinalCap (r : Nat) : Nat :=
  (rteCaps r).getLast?.getD 0

/-- The allocator budget and live-block count after one buffer (alignment `align`) has been
    allocated with the capacities `cs` in order from `(lb, lk)`: the first is an `alloc`
    (`(lb + cost c, lk + 1)`), each later one a `realloc` from the previous capacity
    (`lb + cost c - cost prev`, `lk` unchanged); `(lb, lk)` for `cs = []`. Matches
    `AllocSeqFits`. -/
def allocSeqPool {oom : State → State → Prop} (A : RustStdAlloc oom) (align : Nat)
    (lb lk : Nat) : List Nat → Nat × Nat
  | [] => (lb, lk)
  | c :: cs => go (lb + A.cost c align) (lk + 1) c cs
where
  /-- After the first allocation: `prev` is the current capacity. -/
  go (lb lk prev : Nat) : List Nat → Nat × Nat
    | [] => (lb, lk)
    | c :: cs => go (lb + A.cost c align - A.cost prev align) lk c cs

/-- `k` is the number of input bytes `read_to_end` (with `r` bytes of input) has consumed when one
    of its allocation requests is made: `r` itself for the first request when `0 < r < 8`, else a
    capacity `rteCap r i ≤ r` (the first request when `r ≥ 8`, and every growth request, made when
    the buffer is full). -/
def RteOomPt (r k : Nat) : Prop :=
  (0 < r ∧ r < 8 ∧ k = r) ∨ ∃ i, k = rteCap r i ∧ rteCap r i ≤ r

/-! ## Stream Specifications -/

/-- `std::io::stdio::stdin()`. Ghost: `(init, lb, lk, haveLse)` (whether `INSTANCE` is already
    initialized, allocator budget and live-block count, the `have_lse_atomics` byte).
    - Pre: `StdinAt A saddrs init`, the vtable slot `stdinOnceVtbl + 0x20 ↦₆₄ᵣ stdinInitFn`,
      `haveLseAtomics ↦₈ᵣ haveLse`, the pool, musl's `errno` cell (`StdErrnoCell`, given back
      with any value), `stackBytes` bytes of stack; when `init = false`, the 8192-byte request
      fits (`CanAlloc`).
    - Post: `IoCallFrame`, file system and trace unchanged, `x0 = stdinInst`, `StdinAt A saddrs true`;
      the pool at `(lb + cost 8192 1, lk + 1)` when `init = false`, else unchanged.
    - Out of memory: only when `init = false`, with the file system unchanged. -/
def stdinSpec (A : RustStdAlloc oom) (saddrs : RustStdStdioAddrs) (stackBytes : Nat) :
    Spec (Bool × Nat × Nat × BitVec 8) where
  pre := fun (init, lb, lk, haveLse) s =>
    ⌜saddrs.Aligned ∧ (init = false → A.CanAlloc lb lk 8192 1)⌝ ∗
      A.pool lb lk s ∗ StdinAt A saddrs init ∗
      ((saddrs.stdinOnceVtbl + 0x20#64) ↦₆₄ᵣ saddrs.stdinInitFn) ∗
      (saddrs.haveLseAtomics ↦₈ᵣ haveLse) ∗ StdErrnoCell s.tpidrEl0 ∗ stackFrameAt s.sp stackBytes
  post := fun (init, lb, lk, haveLse) s0 sf =>
    ⌜IoCallFrame s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
      sf.readReg64 .x0 = saddrs.stdinInst⌝ ∗
      (if init then A.pool lb lk sf else A.pool (lb + A.cost 8192 1) (lk + 1) sf) ∗
      StdinAt A saddrs true ∗
      ((saddrs.stdinOnceVtbl + 0x20#64) ↦₆₄ᵣ saddrs.stdinInitFn) ∗
      (saddrs.haveLseAtomics ↦₈ᵣ haveLse) ∗ StdErrnoCell s0.tpidrEl0 ∗
      stackFrameAt s0.sp stackBytes
  onOom := fun (init, _, _, _) s0 sf =>
    ⌜init = false ∧ ∃ sm, IoFrame s0 sm ∧ sm.fs = s0.fs ∧ oom sm sf⌝

/-- The outcome part of `stdinReadToEndSpec`'s post. Let `rem = s0.fs.stdin.drop d0.offset` and
    `r = rem.length`.
    - `none` (`Ok(r)`): `x0 = 0`, `x1 = r`, fd 0's offset `d0.offset + r`, the pool after all of
      `rteCaps r`, and the `Vec` holds `rem` with capacity `rteFinalCap r`.
    - `some i` (`Err(OutOfMemory)`): request `i + 1` exists and may return null
      (`NullAllowed (rteCap r (i + 1)) 1`); `x0 = 1`, `x1 = IoErr.outOfMemory.repr addrs`, fd 0's
      offset `d0.offset + rteCap r i`, the pool after the first `i + 1` requests, and the `Vec`
      holds `rem.take (rteCap r i)` with capacity `rteCap r i`. -/
def stdinReadToEndResult (A : RustStdAlloc oom) (addrs : RustStdIoAddrs) (vec : BitVec 64)
    (d0 : FdEntry) (lb lk : Nat) (s0 sf : State) : Option Nat → SepProp
  | none =>
    let rem := s0.fs.stdin.drop d0.offset
    let r := rem.length
    ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = BitVec.ofNat 64 r ∧
      sf.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + r })⌝ ∗
    A.pool (allocSeqPool A 1 lb lk (rteCaps r)).1 (allocSeqPool A 1 lb lk (rteCaps r)).2 sf ∗
    (∃∗ ptr : BitVec 64, ioResultVecOk A vec (BitVec.ofNat 64 (rteFinalCap r)) ptr rem)
  | some i =>
    let rem := s0.fs.stdin.drop d0.offset
    let r := rem.length
    ⌜i + 1 < (rteCaps r).length ∧ NullAllowed (rteCap r (i + 1)) 1 ∧
      sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = IoErr.outOfMemory.repr addrs ∧
      sf.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + rteCap r i })⌝ ∗
    A.pool (allocSeqPool A 1 lb lk ((rteCaps r).take (i + 1))).1
      (allocSeqPool A 1 lb lk ((rteCaps r).take (i + 1))).2 sf ∗
    (∃∗ ptr : BitVec 64,
      ioResultVecOk A vec (BitVec.ofNat 64 (rteCap r i)) ptr (rem.take (rteCap r i)))

/-- `<Stdin as Read>::read_to_end(self = x0, buf = x1)` into an empty `Vec`. Ghost:
    `(self, vec, ptr0, d0, lb, lk, haveLse)` (the `&mut Stdin` slot, the `Vec` header, its
    dangling pointer, fd 0's descriptor, allocator budget and live-block count, the
    `have_lse_atomics` byte). Let `rem = s0.fs.stdin.drop d0.offset` and `r = rem.length`.
    - Pre: `self ↦₆₄ stdinInst`, `StdinAt A saddrs true`, the `Vec` header `{0, ptr0, 0}` (`ptr0 ≠ 0`),
      the pool, `StdErrCells`, `StdioRoCells`, `panicCount ↦₆₄ᵣ 0`, `haveLseAtomics ↦₈ᵣ haveLse`,
      `stackBytes` bytes of stack (`s.sp.toNat ≤ USER_VA_LIMIT`); fd 0 is `d0`, of kind `.stdio`
      and readable; every capacity request fits
      (`AllocSeqFits A 1 lb lk (rteCaps r)`).
    - Post: `IoCallFrame`, trace unchanged, the cells and the stack given back, `StdinAt A saddrs true`,
      and either
      - `Ok(r)`: `x0 = 0`, `x1 = r`, the `Vec` holds `rem` with capacity `rteFinalCap r`, the
        pool after all of `rteCaps r`, fd 0's offset `d0.offset + r`; or
      - `Err(OutOfMemory)`: for some `i` with request `i + 1` existing and allowed to return null
        (`NullAllowed (rteCap r (i + 1)) 1`): `x0 = 1`, `x1 = IoErr.outOfMemory.repr addrs`, the
        `Vec` holds `rem.take (rteCap r i)` with capacity `rteCap r i`, the pool after the first
        `i + 1` requests, fd 0's offset `d0.offset + rteCap r i`.
    - Out of memory: some `k` with `RteOomPt r k`, the trace unchanged, and fd 0's offset
      `d0.offset + k`. -/
def stdinReadToEndSpec (A : RustStdAlloc oom) (addrs : RustStdIoAddrs)
    (saddrs : RustStdStdioAddrs) (stackBytes : Nat) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × Nat × Nat × BitVec 8) where
  pre := fun (self, vec, ptr0, d0, lb, lk, haveLse) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x1 = vec ∧ saddrs.Aligned ∧ ptr0 ≠ 0#64 ∧
      stackBytes ≤ s.sp.toNat ∧ s.sp.toNat ≤ Arm64.USER_VA_LIMIT ∧
      s.fs.fds 0#64 = some d0 ∧ d0.kind = .stdio ∧ d0.accMode.canRead = true ∧
      AllocSeqFits A 1 lb lk (rteCaps (s.fs.stdin.drop d0.offset).length)⌝ ∗
      A.pool lb lk s ∗ (self ↦₆₄ saddrs.stdinInst) ∗ StdinAt A saddrs true ∗
      vecHeader vec 0#64 ptr0 0#64 ∗ StdErrCells addrs s.tpidrEl0 ∗ StdioRoCells addrs ∗
      (saddrs.panicCount ↦₆₄ᵣ 0#64) ∗ (saddrs.haveLseAtomics ↦₈ᵣ haveLse) ∗
      stackFrameAt s.sp stackBytes
  post := fun (self, vec, _ptr0, d0, lb, lk, haveLse) s0 sf =>
    ⌜IoCallFrame s0 sf ∧ sf.trace = s0.trace⌝ ∗
      (self ↦₆₄ saddrs.stdinInst) ∗ StdinAt A saddrs true ∗ StdErrCells addrs s0.tpidrEl0 ∗
      StdioRoCells addrs ∗ (saddrs.panicCount ↦₆₄ᵣ 0#64) ∗
      (saddrs.haveLseAtomics ↦₈ᵣ haveLse) ∗ stackFrameAt s0.sp stackBytes ∗
      (∃∗ e : Option Nat, stdinReadToEndResult A addrs vec d0 lb lk s0 sf e)
  onOom := fun (_, _, _, d0, _, _, _) s0 sf =>
    ⌜∃ k sm, RteOomPt (s0.fs.stdin.drop d0.offset).length k ∧ IoFrame s0 sm ∧
      sm.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + k }) ∧ oom sm sf⌝

/-- `std::io::stdio::stdout()`. Ghost: `(pending, lb, lk, haveLse)` (`none` when `STDOUT` is not
    yet initialized, else the pending bytes; allocator budget and live-block count; the
    `have_lse_atomics` byte).
    - Pre: `StdoutAt A saddrs pending`, the vtable slot `stdoutOnceVtbl + 0x20 ↦₆₄ᵣ stdoutInitFn`,
      `haveLseAtomics ↦₈ᵣ haveLse`, the pool, musl's `errno` cell (`StdErrnoCell`, given back
      with any value), `stackBytes` bytes of stack; when `pending = none`, the 1024-byte request
      fits (`CanAlloc`).
    - Post: `IoCallFrame`, file system and trace unchanged, `x0 = stdoutInst`,
      `StdoutAt A saddrs (some (pending.getD []))`; the pool at `(lb + cost 1024 1, lk + 1)` when
      `pending = none`, else unchanged.
    - Out of memory: only when `pending = none`, with the file system unchanged. -/
def stdoutSpec (A : RustStdAlloc oom) (saddrs : RustStdStdioAddrs) (stackBytes : Nat) :
    Spec (Option (List (BitVec 8)) × Nat × Nat × BitVec 8) where
  pre := fun (pending, lb, lk, haveLse) s =>
    ⌜saddrs.Aligned ∧ (pending = none → A.CanAlloc lb lk 1024 1)⌝ ∗
      A.pool lb lk s ∗ StdoutAt A saddrs pending ∗
      ((saddrs.stdoutOnceVtbl + 0x20#64) ↦₆₄ᵣ saddrs.stdoutInitFn) ∗
      (saddrs.haveLseAtomics ↦₈ᵣ haveLse) ∗ StdErrnoCell s.tpidrEl0 ∗ stackFrameAt s.sp stackBytes
  post := fun (pending, lb, lk, haveLse) s0 sf =>
    ⌜IoCallFrame s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
      sf.readReg64 .x0 = saddrs.stdoutInst⌝ ∗
      (if pending.isSome then A.pool lb lk sf else A.pool (lb + A.cost 1024 1) (lk + 1) sf) ∗
      StdoutAt A saddrs (some (pending.getD [])) ∗
      ((saddrs.stdoutOnceVtbl + 0x20#64) ↦₆₄ᵣ saddrs.stdoutInitFn) ∗
      (saddrs.haveLseAtomics ↦₈ᵣ haveLse) ∗ StdErrnoCell s0.tpidrEl0 ∗
      stackFrameAt s0.sp stackBytes
  onOom := fun (pending, _, _, _) s0 sf =>
    ⌜pending = none ∧ ∃ sm, IoFrame s0 sm ∧ sm.fs = s0.fs ∧ oom sm sf⌝

/-- The caller's bytes `bs` at `buf` for `write_all`, read-write (`ro = false`) or read-only
    (`ro = true`). -/
def stdoutBytesAt (ro : Bool) (buf : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if ro then (buf ↦ᵣ bs) else (buf ↦ₛ bs)

/-- Pending bytes retained in a 1024-byte `BufWriter` after writing `bs` onto `p` (`p.length ≤ 1024`):
    appends `bs` in place when `p.length + bs.length ≤ 1024` and `bs.length < 1024`, flushes `p` and
    retains `bs` when `p.length + bs.length > 1024` and `bs.length < 1024`, or writes through leaving
    `[]` when `1024 ≤ bs.length`. -/
def bufWriterPending (p bs : List (BitVec 8)) : List (BitVec 8) :=
  if bs.length < 1024 then
    if p.length + bs.length ≤ 1024 then p ++ bs else bs
  else []

/-- Pending bytes retained in `LineWriter<StdoutRaw>` after writing `bs` onto `p` (`p.length ≤ 1024`):
    flushes `p` and `bs` through the last `'\n'` (`0x0a`) when `bs` contains `'\n'` and buffers the
    trailing suffix via `bufWriterPending []`, flushes `p` first when `bs` has no `'\n'` and `p` ends
    with `'\n'`, or delegates `p` and `bs` to `bufWriterPending`. -/
def lineWriterPending (p bs : List (BitVec 8)) : List (BitVec 8) :=
  match lastIndexOf 0x0a#8 bs with
  | some idx => bufWriterPending [] (bs.drop (idx + 1))
  | none =>
    if p.getLast? = some 0x0a#8 then bufWriterPending [] bs
    else bufWriterPending p bs

/-- `<Stdout as Write>::write_all(self = x0, buf = x1, len = x2)`. Ghost:
    `(self, ro, buf, bs, p, tid, ctr, haveLse)` (the `&mut Stdout` slot, whether the bytes are
    read-only, the bytes, the pending bytes, the thread's TLS id and the thread-id counter, the
    `have_lse_atomics` byte).
    - Pre: `self ↦₆₄ stdoutInst`, `StdoutAt A saddrs (some p)`, the bytes (`len = bs.length`,
      `buf.toNat + bs.length ≤ USER_VA_LIMIT`),
      `StdThreadIdCells saddrs s.tpidrEl0 tid ctr` (`ctr ≠ 2 ^ 64 - 1` when `tid = 0`), `StdErrCells`,
      `StdioRoCells`, `haveLseAtomics ↦₈ᵣ haveLse`, `stackBytes` bytes of stack.
    - Post: `IoCallFrame`, file system unchanged, `x0 = 0`; for `fl`, `p'` with
      `fl ++ p' = p ++ bs`, `p' = lineWriterPending p bs`, and `p'.length ≤ 1024`: the trace gets
      `fl` as `stdout` writes and `StdoutAt A saddrs (some p')`; the thread-id cells at
      `nextThreadId tid ctr`; the rest given back.
    - Out of memory: never (no allocation). -/
def stdoutWriteAllSpec (A : RustStdAlloc oom) (addrs : RustStdIoAddrs)
    (saddrs : RustStdStdioAddrs) (stackBytes : Nat) :
    Spec (BitVec 64 × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8) × BitVec 64 ×
      BitVec 64 × BitVec 8) where
  pre := fun (self, ro, buf, bs, p, tid, ctr, haveLse) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x1 = buf ∧ (s.readReg64 .x2).toNat = bs.length ∧
      buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT ∧
      saddrs.Aligned ∧ (tid = 0#64 → ctr ≠ 0xFFFFFFFFFFFFFFFF#64)⌝ ∗
      (self ↦₆₄ saddrs.stdoutInst) ∗ StdoutAt A saddrs (some p) ∗ stdoutBytesAt ro buf bs ∗
      StdThreadIdCells saddrs s.tpidrEl0 tid ctr ∗ StdErrCells addrs s.tpidrEl0 ∗
      StdioRoCells addrs ∗ (saddrs.haveLseAtomics ↦₈ᵣ haveLse) ∗ stackFrameAt s.sp stackBytes
  post := fun (self, ro, buf, bs, p, tid, ctr, haveLse) s0 sf =>
    ∃∗ fl : List (BitVec 8), ∃∗ p' : List (BitVec 8),
      ⌜IoCallFrame s0 sf ∧ sf.fs = s0.fs ∧ sf.readReg64 .x0 = 0#64 ∧ fl ++ p' = p ++ bs ∧
        p' = lineWriterPending p bs ∧ p'.length ≤ 1024 ∧
        sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout fl⌝ ∗
        (self ↦₆₄ saddrs.stdoutInst) ∗ StdoutAt A saddrs (some p') ∗ stdoutBytesAt ro buf bs ∗
        StdThreadIdCells saddrs s0.tpidrEl0 (nextThreadId tid ctr).1 (nextThreadId tid ctr).2 ∗
        StdErrCells addrs s0.tpidrEl0 ∗ StdioRoCells addrs ∗
        (saddrs.haveLseAtomics ↦₈ᵣ haveLse) ∗ stackFrameAt s0.sp stackBytes

/-- `<Stdout as Write>::flush(self = x0)`. Ghost: `(self, p, tid, ctr, haveLse)` (the
    `&mut Stdout` slot, the pending bytes, the thread's TLS id and the thread-id counter, the
    `have_lse_atomics` byte).
    - Pre: `self ↦₆₄ stdoutInst`, `StdoutAt A saddrs (some p)`,
      `StdThreadIdCells saddrs s.tpidrEl0 tid ctr` (`ctr ≠ 2 ^ 64 - 1` when `tid = 0`),
      `StdErrCells`, `StdioRoCells`, `haveLseAtomics ↦₈ᵣ haveLse`, `stackBytes` bytes of stack.
    - Post: `IoCallFrame`, file system unchanged, `x0 = 0`, the trace gets `p` as `stdout` writes,
      `StdoutAt A saddrs (some [])`, the thread-id cells at `nextThreadId tid ctr`, the rest given
      back.
    - Out of memory: never (no allocation). -/
def stdoutFlushSpec (A : RustStdAlloc oom) (addrs : RustStdIoAddrs)
    (saddrs : RustStdStdioAddrs) (stackBytes : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64 × BitVec 8) where
  pre := fun (self, p, tid, ctr, haveLse) s =>
    ⌜s.readReg64 .x0 = self ∧ saddrs.Aligned ∧ (tid = 0#64 → ctr ≠ 0xFFFFFFFFFFFFFFFF#64)⌝ ∗
      (self ↦₆₄ saddrs.stdoutInst) ∗ StdoutAt A saddrs (some p) ∗
      StdThreadIdCells saddrs s.tpidrEl0 tid ctr ∗ StdErrCells addrs s.tpidrEl0 ∗
      StdioRoCells addrs ∗ (saddrs.haveLseAtomics ↦₈ᵣ haveLse) ∗ stackFrameAt s.sp stackBytes
  post := fun (self, p, tid, ctr, haveLse) s0 sf =>
    ⌜IoCallFrame s0 sf ∧ sf.fs = s0.fs ∧ sf.readReg64 .x0 = 0#64 ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout p⌝ ∗
      (self ↦₆₄ saddrs.stdoutInst) ∗ StdoutAt A saddrs (some []) ∗
      StdThreadIdCells saddrs s0.tpidrEl0 (nextThreadId tid ctr).1 (nextThreadId tid ctr).2 ∗
      StdErrCells addrs s0.tpidrEl0 ∗ StdioRoCells addrs ∗
      (saddrs.haveLseAtomics ↦₈ᵣ haveLse) ∗ stackFrameAt s0.sp stackBytes

end VerifiedLibraries.RustStd
