/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet

/-!
# Common External-Call Hooks for `libsignal-cli`

**Trusted: the statement.** External-call hooks for the Rust global allocator over `[2^60, 2^61)`,
AES-256-CBC (`signal_crypto`), `String` cloning and formatting, `SystemTime` addition, and
image-local panic symbols. See `Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open Arm64 ProofLib CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ## The heap region and the lowest-fit bump -/

/-- Base of the heap region, `2^60`: far above the CLI's image (at `0x400000`), its
`mmap` slots (from `0x6000_0000_0000`) and its stack (top `0x7fff_ffff_0000`) (DEV-M6,
`SignalSession/CliBinaryPq.lean`). -/
def heapBase : BitVec 64 := BitVec.ofNat 64 (2 ^ 60)

/-- Size of the heap region: `2^60` bytes, so the region is `[2^60, 2^61)` (no wrap-around). -/
def heapSize : Nat := 2 ^ 60

/-- Offset `k` fits a block of `size` bytes with alignment `align` in `m`: `heapBase + k` is
`align`-aligned, the block lies inside the heap region, and every byte of it is unmapped. -/
def HeapBlockFitsAt (m : Memory) (size align k : Nat) : Prop :=
  0 < align ∧ (heapBase + BitVec.ofNat 64 k).toNat % align = 0 ∧ k + size ≤ heapSize ∧
    Unmapped m (heapBase + BitVec.ofNat 64 k) size

open Classical in
/-- **The lowest fit**: the block at the smallest offset that fits (`HeapBlockFitsAt`), `none` if no
offset does. It depends on `m` only through which bytes are mapped. (Classical: `Unmapped`
quantifies over all addresses of the block, which `Memory` cannot enumerate cheaply.) -/
noncomputable def bumpAddr? (m : Memory) (size align : Nat) : Option (BitVec 64) :=
  if h : ∃ k, HeapBlockFitsAt m size align k then some (heapBase + BitVec.ofNat 64 (Nat.find h))
  else none

/-- Map a fresh block of `size` bytes (alignment `align`) at the lowest fit and continue with
`ok` on the state with the block mapped read-write and the block's address; `fail s` if nothing
fits. -/
noncomputable def bumpThen (size align : Nat) (ok : State → BitVec 64 → State)
    (fail : State → State) (s : State) : State :=
  match bumpAddr? s.mem size align with
  | some p => ok (s.setMem (s.mem.mapFresh p size Perm.rw)) p
  | none => fail s

/-! ## The allocator -/

/-- The failure of `__rust_alloc` / `__rust_realloc` / `__rust_alloc_zeroed` (their contracts'
`x0 = 0` branch): one `allocFailedEvent`, `x0 = 0`, return. -/
def allocFail : State → State :=
  retHook fun s => (s.appendTrace [allocFailedEvent]).writeReg64 .x0 0#64

/-- A stub that panics after a failed allocation: appends `allocFailedEvent`, status `Panicked`,
memory and registers unchanged. -/
def allocPanicHook (s : State) : State :=
  (s.appendTrace [allocFailedEvent]).setStatus .Panicked

/-- The request of `__rust_alloc(size = x0, align = x1)` (and `__rust_alloc_zeroed`). -/
def allocReq (s : State) : Nat × Nat := ((s.readReg64 .x0).toNat, (s.readReg64 .x1).toNat)

/-- `__rust_alloc`: the lowest-fit block of `x0` bytes, alignment `x1`, its address in `x0`. -/
noncomputable def allocHook0 (s : State) : State :=
  bumpThen (allocReq s).1 (allocReq s).2 (fun s p => retHook (fun s => s.writeReg64 .x0 p) s)
    allocFail s

/-- The request of `__rust_realloc(ptr = x0, old = x1, align = x2, new = x3)`. -/
def reallocReq (s : State) : Nat × Nat := ((s.readReg64 .x3).toNat, (s.readReg64 .x2).toNat)

/-- `__rust_realloc`: a lowest-fit block of `new` bytes, the first `min old new` bytes of the old
block copied in, its address in `x0`; the old block is leaked (stays mapped). -/
noncomputable def reallocHook0 (s : State) : State :=
  let bs := s.mem.readBytes (s.readReg64 .x0) (min (s.readReg64 .x1).toNat (s.readReg64 .x3).toNat)
  bumpThen (reallocReq s).1 (reallocReq s).2
    (fun s q => retHook (fun s => (s.setMem (s.mem.writeBytes q bs)).writeReg64 .x0 q) s)
    allocFail s

/-- `__rust_alloc_zeroed`: as `allocHook0`, the block filled with `x0` zero bytes. -/
noncomputable def allocZeroedHook0 (s : State) : State :=
  bumpThen (allocReq s).1 (allocReq s).2
    (fun s p => retHook (fun s =>
      (s.setMem (s.mem.writeBytes p (List.replicate (allocReq s).1 0#8))).writeReg64 .x0 p) s)
    allocFail s

/-- `__rust_dealloc`: returns at once. Memory is never unmapped or reused.

**DEV-E6 (machine model): `__rust_dealloc` frees nothing.** The real allocator may hand a freed
block, with its old bytes, out again; here no block is reused within a call. A fresh block holds
the bytes its addresses held before it was mapped (`Memory.mapFresh`). Why: a simpler allocator.
Effect: w.l.o.g., argued: a reused block's old bytes are one more kind of residue, and outputs must
not depend on uninitialised bytes. No theorem checks this (no CLI theorem varies the initial
memory), so it rests on this argument alone. -/
def deallocHook : State → State := hookNoop

/-! ## Hooks returning a fresh `Vec<u8>` -/

/-- Write the `Vec<u8>` header `{cap, ptr, len}` at `v` (`vecHeader`). -/
def writeVecHeader (m : Memory) (v cap ptr len : BitVec 64) : Memory :=
  ((m.write64 v cap).write64 (v + 8#64) ptr).write64 (v + 16#64) len

/-- A hook returning a fresh `Vec<u8>` holding `bs` in the sret `x8`: a lowest-fit block of
`bs.length` bytes (alignment 1; for empty `bs` the block is empty and its address, non-null, is the
dangling pointer of a capacity-0 `Vec`), `bs` copied in, the header `{len, block, len}`. If nothing
fits: `allocPanicHook` (one `allocFailedEvent`, then a panic, as the contracts allow). -/
noncomputable def returnFreshVecU8 (bs : List (BitVec 8)) : State → State :=
  bumpThen bs.length 1
    (fun s p => retHook (fun s =>
      let n := BitVec.ofNat 64 bs.length
      s.setMem (writeVecHeader (s.mem.writeBytes p bs) (s.readReg64 .x8) n p n)) s)
    allocPanicHook

/-- The AES call's input bytes (`x0`, length `x1`). -/
def aesInput (s : State) : List (BitVec 8) := s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat

/-- The AES call's 32 key bytes (`x2`). -/
def aesKey (s : State) : List (BitVec 8) := s.mem.readBytes (s.readReg64 .x2) 32

/-- The AES call's 16 IV (initialization vector) bytes (`x4`). -/
def aesIv (s : State) : List (BitVec 8) := s.mem.readBytes (s.readReg64 .x4) 16

/-- The output of `aes_256_cbc_encrypt` on the call's arguments: the session model's
`aesCbcEncrypt`. -/
def aesEncOut (E : CBC.AesKey → CBC.Block → CBC.Block) (s : State) : List (BitVec 8) :=
  aesCbcEncrypt E (bytesToKey32 (aesKey s)) (CBC.bytesToBlock (aesIv s)) (aesInput s)

/-- The output of `aes_256_cbc_decrypt` on the call's arguments: the session model's
`aesCbcDecrypt`. -/
def aesDecOut (D : CBC.AesKey → CBC.Block → CBC.Block) (s : State) : Option (List (BitVec 8)) :=
  aesCbcDecrypt D (bytesToKey32 (aesKey s)) (CBC.bytesToBlock (aesIv s)) (aesInput s)

/-- `aes_256_cbc_encrypt(ptext = (x0, x1), key = (x2, x3), iv = (x4, x5))` with sret `x8`:
if `key.len != 32` (`x3`) or `iv.len != 16` (`x5`), writes `Err(BadKeyOrIv)` (`errTag` at `x8`,
zero allocations); else if `2 ^ 63 ≤ (x1.toNat / 16 + 1) * 16`, panics (`RawVec` capacity
overflow); else returns `Ok(aesEncOut E s)` in a fresh `Vec<u8>` at `x8`. -/
noncomputable def aesEncHook0 (E : CBC.AesKey → CBC.Block → CBC.Block) (s : State) : State :=
  if s.readReg64 .x3 != 32#64 || s.readReg64 .x5 != 16#64 then
    retHook (fun s => s.setMem (s.mem.write64 (s.readReg64 .x8) errTag)) s
  else if 2 ^ 63 ≤ ((s.readReg64 .x1).toNat / 16 + 1) * 16 then
    Rust.panicked s
  else
    returnFreshVecU8 (aesEncOut E s) s

/-- `aes_256_cbc_decrypt(ctext = (x0, x1), key = (x2, x3), iv = (x4, x5))` with sret `x8`:
1. If `ctext.is_empty()` or `ctext.len() % 16 != 0` (`x1`), returns `Err(BadCiphertext)` (`errTag`
   @0 and non-null `&'static str` placeholder `1` @8, zero allocations).
2. If `key.len != 32` (`x3`) or `iv.len != 16` (`x5`), returns `Err(BadKeyOrIv)` (`errTag` @0 and
   niche `0` @8, zero allocations).
3. If `2 ^ 63 ≤ ctext.len()`, panics (`RawVec` capacity overflow).
4. Otherwise allocates the output `Vec<u8>` before PKCS#7 unpadding: on OOM (`bumpAddr? s.mem ctLen 1 = none`),
   panics via `allocPanicHook`; on `some pt`, returns `pt` in a fresh `Vec<u8>` at `x8`; on `none`
   (invalid PKCS#7 padding), consumes the `ctLen`-byte heap block (matching `alloc` + no-op `dealloc`
   under DEV-E6) and returns `Err(BadCiphertext)`. -/
noncomputable def aesDecHook0 (D : CBC.AesKey → CBC.Block → CBC.Block) (s : State) : State :=
  let ctLen := (s.readReg64 .x1).toNat
  if ctLen == 0 || ctLen % 16 != 0 then
    retHook (fun s =>
      let r := s.readReg64 .x8
      s.setMem ((s.mem.write64 r errTag).write64 (r + 8#64) 1#64)) s
  else if s.readReg64 .x3 != 32#64 || s.readReg64 .x5 != 16#64 then
    retHook (fun s =>
      let r := s.readReg64 .x8
      s.setMem ((s.mem.write64 r errTag).write64 (r + 8#64) 0#64)) s
  else if 2 ^ 63 ≤ ctLen then
    Rust.panicked s
  else
    match aesDecOut D s with
    | some pt =>
      if (bumpAddr? s.mem ctLen 1).isNone then allocPanicHook s
      else returnFreshVecU8 pt s
    | none =>
      bumpThen ctLen 1
        (fun s _ =>
          retHook (fun s =>
            let r := s.readReg64 .x8
            s.setMem ((s.mem.write64 r errTag).write64 (r + 8#64) 1#64)) s)
        allocPanicHook s

/-- The bytes of the `String` at `x0` (its header's `ptr` @8 and `len` @16). -/
def cloneSrc (s : State) : List (BitVec 8) :=
  let v := s.readReg64 .x0
  s.mem.readBytes (s.mem.read64 (v + 8#64)) (s.mem.read64 (v + 16#64)).toNat

/-- `<String as Clone>::clone`: the bytes of `x0`'s `String` in a fresh `Vec<u8>` at the sret. -/
noncomputable def stringCloneHook0 (s : State) : State := returnFreshVecU8 (cloneSrc s) s

/-! ## Hooks that allocate nothing -/

/-- `alloc::fmt::format::format_inner`: an empty `String` (capacity 0, dangling pointer 1) at the
sret `x8`. -/
def formatInnerHook0 : State → State :=
  retHook fun s => s.setMem (writeVecHeader s.mem (s.readReg64 .x8) 0#64 1#64 0#64)

/-- `core::fmt::write`: `Ok` (`x0 = 0`), the `String` unchanged. -/
def fmtWriteHook0 : State → State := retHook fun s => s.writeReg64 .x0 0#64

/-- `<SystemTime as Add<Duration>>::add(self = (x0 = tv_sec, w1 = tv_nsec), dur = (x2 = secs,
w3 = nanos))`: adds `secs` (unsigned) to signed `tv_sec` and `nanos` to `tv_nsec` (`u32`), carrying
`1` second when `nsec ≥ 10^9`; panics (`Rust.panicked`) if the resulting `sec` exceeds `i64::MAX`,
and otherwise writes `(sec, nsec)` to `(x0, x1)` and returns to `lr`. Matches `std`'s
`Timespec::checked_add_duration` followed by `expect`, and agrees with
`SystemTime.checkedAddSecs` when `nanos = 0`. -/
def timeAddHook (s : State) : State :=
  let sec := (s.readReg64 .x0).toInt + ((s.readReg64 .x2).toNat : Int)
  let ns : BitVec 32 := (s.readReg64 .x3).setWidth 32 + (s.readReg64 .x1).setWidth 32
  let carry : Bool := decide (1000000000 ≤ ns.toNat)
  let sec' := if carry then sec + 1 else sec
  let ns' := if carry then ns - 1000000000#32 else ns
  if sec' ≤ 2 ^ 63 - 1 then
    ((s.writeReg64 .x0 (BitVec.ofInt 64 sec')).writeReg64 .x1 (ns'.setWidth 64)).setPC
      (s.readReg64 .lr)
  else Rust.panicked s

/-! ## Panic functions -/

/-- Out-of-line panic stub `<alloc::vec::Vec<_, _>>::remove::assert_failed` not listed in
`Rust.isPanicSymbol`. -/
def extraImagePanicNames : List String :=
  ["<alloc::vec::Vec<_, _>>::remove::assert_failed"]

/-- Whether `s` is an engine or image-local Rust panic symbol. -/
def isImagePanicSymbol (s : String) : Bool :=
  Rust.isPanicSymbol s || extraImagePanicNames.contains s

/-- Extends `hooks` by mapping every symbol satisfying `isImagePanicSymbol` to `Rust.panicked`. -/
def withImagePanics (hooks : String → Option (State → State)) : String → Option (State → State) :=
  fun s => if isImagePanicSymbol s then some Rust.panicked else hooks s

end CryptoVerification.E2E
