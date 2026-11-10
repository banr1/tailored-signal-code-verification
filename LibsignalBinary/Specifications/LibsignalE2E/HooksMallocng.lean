/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.MultiCodeROHook
public import VerifiedLibraries.Mallocng.Spec
public import LibsignalBinary.Specifications.LibsignalE2E.HooksCommon
public import LibsignalBinary.Specifications.SignalSession.CliRun

/-!
# Shared-Pool (`mallocng`) Crypto Hooks for `libsignal-cli`

**Trusted: the statement.** Placed external-call hooks `aesEncHookMallocng`, `aesDecHookMallocng`
(DEV-E8), and `libcruxHmacHookMallocng` (DEV-PQ1) for the `libsignal-cli` CLI ELF, replaying each
compiled primitive's heap-allocator calls (`calloc`, `malloc`, `free`) through
`VerifiedLibraries.mallocngLib.codeROSubroutineHook` at its stack frame depth while preserving the
whole-function cryptographic specifications. See `Computational/docs/TRUSTED_BASE.md` and
`Computational/docs/DEVIATIONS.md` (DEV-E8, DEV-PQ1).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open Arm64 ProofLib CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession (unmodelled)

/-! ## Stack-frame depths at allocator call sites -/

/-- Own stack frame of `signal_crypto::aes_cbc::aes_256_cbc_encrypt` (`+0x00: stp x29, x30,
[sp, #-0x60]!` plus `+0x1c: sub sp, sp, #0xc50`): `0x60 + 0xc50 = 0xcb0 = 3248` bytes (`16`-byte
aligned; `3248 + mallocngStackBytes = 3248 + 1024 = 4272 ≤ extHookStack = 16384`). -/
abbrev aesEncFrameBytes : Nat := 0xcb0

/-- Own stack frame of `signal_crypto::aes_cbc::aes_256_cbc_decrypt` (`+0x00: stp x29, x30,
[sp, #-0x60]!` plus `+0x1c: sub sp, sp, #0x8f0`): `0x60 + 0x8f0 = 0x950 = 2384` bytes (`16`-byte
aligned; `2384 + mallocngStackBytes = 2384 + 1024 = 3408 ≤ extHookStack = 16384`). -/
abbrev aesDecFrameBytes : Nat := 0x950

/-- Own stack frame of `libcrux_hmac::hmac` (`sub sp, sp, #0xe0` at `+0x00`): `224` bytes
(`16`-byte aligned; `224 + mallocngStackBytes = 224 + 1024 = 1248 ≤ extHookStack = 16384`). -/
abbrev libcruxHmacFrameBytes : Nat := 0xe0

/-! ## Single-call `mallocng` replay combinators -/

/-- Restore caller architectural CPU registers (`regs`, `vregs`, `sp`, `pc`, `pstate`, `fpsr`) from
`sCaller` while keeping `sCallee`'s memory, VM state (`brk`, `physMemAvail`), hardware nondeterminism
indices (`oracleIdx`, `exclFails`), and process state (`fs`, `trace`, `status`, `tpidrEl0`,
`brkStart`, `oracle`, `symtab`, `sigActions`, `sigAltStack`). -/
def restoreCallerRegs (sCaller sCallee : State) : State :=
  { sCallee with
    regs := sCaller.regs
    vregs := sCaller.vregs
    sp := sCaller.sp
    pc := sCaller.pc
    pstate := sCaller.pstate
    fpsr := sCaller.fpsr }

/-- Replay one alignment-1 Rust global allocation (`__rustc::__rust_alloc(size, 1)` when
`zeroed = false`, `__rustc::__rust_alloc_zeroed(size, 1)` when `zeroed = true`) at caller stack
depth `frameBytes` (`sp := s.sp - BitVec.ofNat 64 frameBytes`) through verified `mallocng`
(`"malloc"` or `"calloc"` at placement `mpl` under `Syscall.standard`):
* if `mallocng` stops in a non-`.Running` state, propagate `s1` unchanged;
* if `mallocng` returns `0#64` (`NULL`), panic via `Rust.panicked` while retaining `s1`'s
  memory/VM/oracle effects;
* otherwise restore caller architectural registers (`restoreCallerRegs s s1`) and pass the non-null
  block pointer `p = s1.readReg64 .x0` to `k`.

`__rdl_alloc` tail-branches directly to `malloc` (`0` shim frame); `__rdl_alloc_zeroed` pops its
transient `0x30`-byte frame before tail-branching to `calloc` (within `mallocngStackBytes = 1024`). -/
noncomputable def stepRustAlloc1 (mpl : Obj.MultiPlacement) (zeroed : Bool)
    (frameBytes size : Nat) (k : State → BitVec 64 → State) (s : State) : State :=
  let spCall := s.sp - BitVec.ofNat 64 frameBytes
  let sCall0 := (s.writeReg64 .sp spCall).writeReg64 .x0 (BitVec.ofNat 64 size)
  let sCall := if zeroed then sCall0.writeReg64 .x1 1#64 else sCall0
  let fnName := if zeroed then "calloc" else "malloc"
  let s1 := VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl fnName
    (fun _ => none) (fun _ => none) Syscall.standard sCall
  if s1.status != .Running then
    s1
  else
    let p := s1.readReg64 .x0
    let sKeep := restoreCallerRegs s s1
    if p == 0#64 then
      Rust.panicked sKeep
    else
      k sKeep p

/-- Replay one alignment-1 Rust global deallocation (`__rustc::__rust_dealloc(ptr, _size, 1)` →
`free`, `0` shim frame) at caller stack depth `frameBytes` (`sp := s.sp - BitVec.ofNat 64 frameBytes`)
through verified `mallocng` (`"free"` at placement `mpl` under `Syscall.standard`). -/
noncomputable def stepRustDealloc1 (mpl : Obj.MultiPlacement) (frameBytes : Nat)
    (ptr : BitVec 64) (k : State → State) (s : State) : State :=
  let spCall := s.sp - BitVec.ofNat 64 frameBytes
  let sCall := (s.writeReg64 .sp spCall).writeReg64 .x0 ptr
  let s1 := VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl "free"
    (fun _ => none) (fun _ => none) Syscall.standard sCall
  if s1.status != .Running then
    s1
  else
    k (restoreCallerRegs s s1)

/-! ## Shared-pool cryptographic hooks -/

/-- `signal_crypto::aes_cbc::aes_256_cbc_encrypt` (frame `0xcb0 = 3248` B) over shared `mallocng`
at placement `mpl` (DEV-E8):
1. Fails closed (`unmodelled`) if `key.len() ≠ 32` (`x3`) or `iv.len() ≠ 16` (`x5`).
2. Panics via `Rust.panicked` (`0` allocations) if `2 ^ 63 ≤ (ptLen / 16 + 1) * 16`.
3. Replays `calloc(ctLen, 1)` at `sp = s0.sp - 0xcb0#64`, writes `ct = aesEncOut E s1` at `p`,
   writes `Vec` header `{ctLen, p, ctLen}` at sret `x8`, and returns. -/
noncomputable def aesEncHookMallocng (mpl : Obj.MultiPlacement)
    (E : CBC.AesKey → CBC.Block → CBC.Block) (s0 : State) : State :=
  if s0.readReg64 .x3 != 32#64 || s0.readReg64 .x5 != 16#64 then
    unmodelled "aes_256_cbc_encrypt: key.len != 32 or iv.len != 16" s0
  else
    let ptLen := (s0.readReg64 .x1).toNat
    let ctLen := (ptLen / 16 + 1) * 16
    if 2 ^ 63 ≤ ctLen then
      Rust.panicked s0
    else
      stepRustAlloc1 mpl true aesEncFrameBytes ctLen (fun s1 p =>
        let ct := aesEncOut E s1
        let n := BitVec.ofNat 64 ct.length
        retHook (fun s =>
          s.setMem (writeVecHeader (s.mem.writeBytes p ct) (s.readReg64 .x8) n p n)) s1) s0

/-- `signal_crypto::aes_cbc::aes_256_cbc_decrypt` (frame `0x950 = 2384` B) over shared `mallocng`
at placement `mpl` (DEV-E8):
1. Fails closed (`unmodelled`) if `key.len() ≠ 32` (`x3`) or `iv.len() ≠ 16` (`x5`).
2. Returns `Err(BadCiphertext)` (`errTag` at `x8`, `1` at `x8 + 8`, `0` allocations) when
   `ctLen = 0` or `ctLen % 16 ≠ 0`.
3. Replays `calloc(ctLen, 1)` at `sp = s0.sp - 0x950#64` and evaluates `aesDecOut D s1`:
   * `some pt`: writes `pt` at `p` and `Vec` header `{cap := ctLen, ptr := p, len := pt.length}`
     at `x8` (`Vec::truncate` leaves spare capacity `[p + pt.length .. p + ctLen)` unallocated);
   * `none` (invalid PKCS#7 padding): replays `free(p)` at `sp = s1.sp - 0x950#64` and returns
     `Err(BadCiphertext)` at `x8` (freed heap bytes return to `mallocng` and are unobservable to
     callers, DEV-E8). -/
noncomputable def aesDecHookMallocng (mpl : Obj.MultiPlacement)
    (D : CBC.AesKey → CBC.Block → CBC.Block) (s0 : State) : State :=
  if s0.readReg64 .x3 != 32#64 || s0.readReg64 .x5 != 16#64 then
    unmodelled "aes_256_cbc_decrypt: key.len != 32 or iv.len != 16" s0
  else
    let ctLen := (s0.readReg64 .x1).toNat
    if ctLen == 0 || ctLen % 16 != 0 then
      retHook (fun s =>
        let r := s.readReg64 .x8
        s.setMem ((s.mem.write64 r errTag).write64 (r + 8#64) 1#64)) s0
    else
      stepRustAlloc1 mpl true aesDecFrameBytes ctLen (fun s1 p =>
        match aesDecOut D s1 with
        | some pt =>
          retHook (fun s =>
            let r := s.readReg64 .x8
            s.setMem (writeVecHeader (s.mem.writeBytes p pt) r
              (BitVec.ofNat 64 ctLen) p (BitVec.ofNat 64 pt.length))) s1
        | none =>
          stepRustDealloc1 mpl aesDecFrameBytes p (fun s2 =>
            retHook (fun s =>
              let r := s.readReg64 .x8
              s.setMem ((s.mem.write64 r errTag).write64 (r + 8#64) 1#64)) s2) s1) s0

/-- `libcrux_hmac::hmac` (frame `0xe0 = 224` B) over shared `mallocng` at placement `mpl`
(DEV-PQ1):
1. Fails closed (`unmodelled`) unless `w0 == 0#32` (`Algorithm::Sha256`).
2. Panics via `Rust.panicked` (`0` allocations) if `2 ^ 32 ≤ keyLen` (`x2`) or `2 ^ 32 ≤ dataLen`
   (`x4`).
3. Replays the SHA-256 arm's 7 allocator calls at `sp = s0.sp - 0xe0#64`: `calloc(64, 1)` for
   `pKey`, `malloc(64)` for `pIpad`, `malloc(64)` for `pOpad`, `free(pOpad)`, `free(pIpad)`,
   `free(pKey)` (freed scratch buffers return to `mallocng`, DEV-PQ1), and `malloc(32)` for `pOut`,
   writing `HMAC.hmacWith F key data` to `pOut` and `Vec` header `{32, pOut, outLen}` at sret `x8`. -/
noncomputable def libcruxHmacHookMallocng (mpl : Obj.MultiPlacement)
    (F : HMAC.ShaState → List (BitVec 8) → HMAC.ShaState) (s0 : State) : State :=
  if (s0.readReg64 .x0).setWidth 32 != 0#32 then
    unmodelled "libcrux_hmac::hmac: alg != Sha256" s0
  else
    let keyLen := (s0.readReg64 .x2).toNat
    let dataLen := (s0.readReg64 .x4).toNat
    if 2 ^ 32 ≤ keyLen || 2 ^ 32 ≤ dataLen then
      Rust.panicked s0
    else
      stepRustAlloc1 mpl true libcruxHmacFrameBytes 64 (fun s1 pKey =>
        let key := s1.mem.readBytes (s1.readReg64 .x1) keyLen
        stepRustAlloc1 mpl false libcruxHmacFrameBytes 64 (fun s2 pIpad =>
          stepRustAlloc1 mpl false libcruxHmacFrameBytes 64 (fun s3 pOpad =>
            let data := s3.mem.readBytes (s3.readReg64 .x3) dataLen
            let tag := HMAC.hmacWith F key data
            stepRustDealloc1 mpl libcruxHmacFrameBytes pOpad (fun s4 =>
              stepRustDealloc1 mpl libcruxHmacFrameBytes pIpad (fun s5 =>
                stepRustDealloc1 mpl libcruxHmacFrameBytes pKey (fun s6 =>
                  stepRustAlloc1 mpl false libcruxHmacFrameBytes 32 (fun s7 pOut =>
                    let outLen :=
                      if (s7.readReg64 .x5).setWidth 32 &&& 1#32 != 0#32 then
                        min (s7.readReg64 .x6).toNat 32
                      else
                        32
                    retHook (fun s =>
                      s.setMem (writeVecHeader (s.mem.writeBytes pOut tag)
                        (s.readReg64 .x8) 32#64 pOut (BitVec.ofNat 64 outLen))) s7)
                    s6) s5) s4) s3) s2) s1) s0

end CryptoVerification.E2E
