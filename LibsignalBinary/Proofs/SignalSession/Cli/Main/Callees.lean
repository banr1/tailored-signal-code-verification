/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVec
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Kits
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Model
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top
public import LibsignalBinary.Proofs.SpecLemmas.FsFold
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.RecordCodecsBinary.SignedPreKey
public import LibsignalBinary.Specifications.SignalSession.Process
public import ProofLib
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunProofDefs

set_option warningAsError false

/-!
# Callee Contracts for `signal-session` `main`

In-image callee contracts (`strlen`, `from_utf8`, `address`, `do_reserve_and_handle`,
`try_allocate_in`, `AllocContractsFs`, and `runSpec`) and hook-shaped I/O contracts (`MainIo` over
an abstract `IoModel`: `read_stdin`, `read_file`, `write_file`, `write_stdout`) taken as hypotheses
by the `main` hop proofs.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit
/-- Program of `main` (`= cliProg img ext` under `Obj.Loads libsignalSessionImage img`). -/
noncomputable abbrev mProg (img : Obj.Image) (ext : String → Option (State → State)) : Program :=
  tripleRatchetProgAtExt img.base ext

noncomputable abbrev mPc (img : Obj.Image) (ext : String → Option (State → State)) (k : Nat) :
    BitVec 64 :=
  (mProg img ext).fnAddr mainName + BitVec.ofNat 64 k

/-- Adds `sf.fs = s0.fs` to `spec`'s normal-return postcondition (panic, exit, and OOM unchanged);
commutes with `Spec.inImage`. -/
def _root_.Arm64.Spec.keepsFs {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜sf.fs = s0.fs⌝ ∗ spec.post x s0 sf }

/-- Mangled symbol name for `do_reserve_and_handle` (`Vec<&str>` growth in M2, `path_of` pushes in M5). -/
abbrev reserve11Name : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"

/-- Mangled symbol name for `try_allocate_in` (`bundle.to_owned()` in `init`). -/
abbrev tryAllocateIn3Name : String := "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]"

abbrev addressName : String := "libsignal_cli::address"

abbrev runName : String := "libsignal_cli::run"

abbrev mainReadStdinName : String := CryptoVerification.SignalSession.readStdinName

abbrev mainWriteFileName : String := CryptoVerification.SignalSession.writeFileName

abbrev mainWriteStdoutName : String := CryptoVerification.SignalSession.writeStdoutName

/-! ## In-image callees -/

/-- Contract of `strlen(p)` on a NUL-terminated byte slice `s` containing no interior NULs. -/
def strlenSpec (hookStack : Nat) : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (p, s) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ ∀ b ∈ s, b ≠ 0#8⌝ ∗ cStrAt p s ∗ stackAt s0.sp hookStack
  post := fun (p, s) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 s.length ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      cStrAt p s ∗
      stackAt s0.sp hookStack

/-- Contract of `core::str::from_utf8(bytes)` on ASCII bytes, writing `Ok(&bytes)` (`tag = 0` @0,
pointer @8, length @16) into the 24-byte `sret` slot at `x8`. -/
def fromUtf8AsciiSpec (hookStack : Nat) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (r, p, bs) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      s0.readReg64 (.gpr 8#5) = r ∧ ∀ b ∈ bs, b.toNat < 128⌝ ∗
      (p ↦ₛ bs) ∗ memRegion r 24 ∗ stackAt s0.sp hookStack
  post := fun (r, p, bs) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗ (p ↦ₛ bs) ∗ (r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ p) ∗
      ((r + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ stackAt s0.sp hookStack

structure AddressCall where
  out : BitVec 64
  p : BitVec 64
  bs : List (BitVec 8)

/-- Contract of `signal_session::address(text)`: writes `Option<ProtocolAddress>` (32 bytes) at `x0`
(`None` iff word 0 is `-1`; `Some` is `protocolAddressAt` with an owned copy of `addrParse`'s name). -/
def addressSpec (A : RustAlloc) (uuidParse : UuidParser) (resStack : Nat) : Spec AddressCall where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.out ∧ s0.readReg64 .x1 = x.p ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 x.bs.length⌝ ∗
      (x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ A.pool ∗ stackAt s0.sp resStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗ (x.p ↦ₛ x.bs) ∗ A.pool ∗ stackAt s0.sp resStack ∗
      (match addrParse uuidParse x.bs with
       | none => (x.out ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.out + 8#64) 24
       | some a => ∃∗ g : AddrGhost,
           ⌜g.name.bytes = a.name ∧ g.name.cap = BitVec.ofNat 64 a.name.length ∧
             g.device = a.device⌝ ∗ protocolAddressAt A g x.out)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap

structure Reserve16Call where
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- A `Vec` of 16-byte elements at `v`, represented by its raw byte payload across reallocations. -/
def vec16At (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  vecHeader v cap ptr (BitVec.ofNat 64 (bs.length / 16)) ∗
    ⌜bs.length % 16 = 0 ∧ bs.length ≤ 16 * cap.toNat ∧ 16 * cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr (16 * cap.toNat) 8 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (16 * cap.toNat - bs.length))

/-- Contract of `do_reserve_and_handle` with `additional = 1`, align 8, and stride 16 (`M+0x180`),
requiring `16 * x.cap.toNat < 2 ^ 62` so amortized doubling cannot trigger capacity-overflow panic. -/
def reserve16Spec (A : RustAlloc) (resStack : Nat) : Spec Reserve16Call where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.v ∧ s0.readReg64 .x1 = BitVec.ofNat 64 (x.bs.length / 16) ∧
      s0.readReg64 .x2 = 1#64 ∧ s0.readReg64 .x3 = 8#64 ∧ s0.readReg64 .x4 = 16#64 ∧
      16 * (x.bs.length / 16 + 1) < 2 ^ 62 ∧ 16 * x.cap.toNat < 2 ^ 62⌝ ∗
      vec16At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s0.sp resStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜x.bs.length / 16 + 1 ≤ cap'.toNat⌝ ∗ vec16At A x.v cap' p' x.bs) ∗
      A.pool ∗ stackAt s0.sp resStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap

open CryptoVerification.E2E.Pqxdh.Shared in
/-- Contract of `try_allocate_in` parameterized by an explicit stack budget `resStack`. -/
def tryAllocateInSpecOf (resStack : Nat) (A : RustAlloc) : Spec TryAllocateInCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.new ∧
      s.readReg64 .x2 = x.align ∧ s.readReg64 .x3 = x.stride ∧
      0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
    memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp resStack
  post := fun x s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ tag) ∗
      (if tag = 1#64 then
        ((x.out + 8#64) ↦₆₄ x.align) ∗
        ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * x.stride.toNat)) ∗
        ⌜p' = 0#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ((x.out + 8#64) ↦₆₄ x.new) ∗
        ((x.out + 16#64) ↦₆₄ p') ∗
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (x.new.toNat * x.stride.toNat) x.align.toNat ∗
          memRegion p' (x.new.toNat * x.stride.toNat)) ∗
      A.pool ∗ stackAt s0.sp resStack

/-- `AllocContractsX` extended with `.keepsFs` on all 14 entries plus read-only-source `memcpy`
(`session_memcpy_region_ro`). -/
structure AllocContractsFs (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr allocName)
    ((rustAllocSpecWithStack A extHookStack).keepsFs.inImage img)
  dealloc : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr deallocName)
    ((rustDeallocExternSpecWithStack A extHookStack).keepsFs.inImage img)
  realloc : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr reallocName)
    ((rustReallocExternSpecWithStack A extHookStack).keepsFs.inImage img)
  shim : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr shimName)
      ((withStack CryptoVerification.LibsignalTripleRatchet.sessionShimSpec stk).keepsFs.inImage img)
  memcpy : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr memcpyName)
      ((libcMemcpySpec stk).keepsFs.inImage img)
  session_memcpy : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr memcpyName)
      ((CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec stk).keepsFs.inImage img)
  memcpy_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr memcpyName)
      ((withStack memcpyRegionSpec stk).keepsFs.inImage img)
  session_memcpy_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr memcpyName)
      ((withStack CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec stk).keepsFs.inImage
        img)
  memmove : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr memmoveName)
      ((libcMemmoveSpec stk).keepsFs.inImage img)
  session_memmove : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr memmoveName)
      ((CryptoVerification.LibsignalTripleRatchet.sessionMemmoveSpec stk).keepsFs.inImage img)
  memset : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr memsetName)
      ((libcMemsetSpec stk).keepsFs.inImage img)
  session_memset : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr memsetName)
      ((CryptoVerification.LibsignalTripleRatchet.sessionMemsetSpec stk).keepsFs.inImage img)
  memset_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr memsetName)
      ((withStack memsetRegionSpec stk).keepsFs.inImage img)
  session_memset_region : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr memsetName)
      ((withStack CryptoVerification.LibsignalTripleRatchet.sessionMemsetRegionSpec stk).keepsFs.inImage
        img)
  /-- Read-only-source `memcpy` (`src ↦ᵣ bs`), used when `path_of` copies `Dir.path` (`M+0x894`). -/
  session_memcpy_region_ro : ∀ (stk : Nat), extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr memcpyName)
      ((withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec stk).keepsFs.inImage img)

/-- Bundle of `main`'s in-image callee contracts (`alloc`, `allocFs`, `strlen`, `fromUtf8`,
`address`, `reserve16`, `reserve1`, and `tryAllocateIn3`). -/
structure MainCallees (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (uuidParse : UuidParser) (hookStack resStack : Nat) : Prop where
  alloc : AllocContractsX img A ext
  allocFs : AllocContractsFs img A ext
  strlen : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr "strlen")
    ((strlenSpec hookStack).inImage img)
  fromUtf8 : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr "core::str::converts::from_utf8")
    ((fromUtf8AsciiSpec hookStack).inImage img)
  address : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr addressName)
    ((addressSpec A uuidParse resStack).inImage img)
  reserve16 : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr reserve11Name)
    ((reserve16Spec A resStack).inImage img)
  reserve1 : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr reserve11Name)
    ((CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A).keepsFs.inImage img)
  tryAllocateIn3 : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr tryAllocateIn3Name)
    ((tryAllocateInSpecOf resStack A).keepsFs.inImage img)

/-! ## I/O Callees -/

/-- Abstract I/O model parameterizing `main`'s file and stdio contracts. -/
structure IoModel where
  /-- Read rule for `read_file`. -/
  rd : ReadRule
  /-- Write rule for `write_file`: `some F'` on `Ok`, `none` on `Err`. -/
  wr : WriteRule
  /-- Remaining stdin bytes on `FsState` (`none` if fd 0 is outside the model). -/
  stdin : FsState → Option (List (BitVec 8))
  /-- Modelled file-system paths. -/
  pathOk : List (BitVec 8) → Prop

structure ReadStdinGhost where
  ret : BitVec 64
  bs : List (BitVec 8)

/-- Contract of `read_stdin()` (`sret` at `x8`, 24 bytes): writes `readStdinResult x.bs` for
`x.bs = io.stdin s0.fs` keeping `fs.files` unchanged, or panics with `allocFailedEvent` on OOM. -/
def readStdinSpec (io : IoModel) (A : RustAlloc) (img : Obj.Image) (stk : Nat) :
    Spec ReadStdinGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x8 = x.ret ∧ io.stdin s.fs = some x.bs⌝ ∗
          memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        (∃∗ r : Except Unit (List (BitVec 8)),
          ⌜sf.fs.files = s0.fs.files ∧ r = readStdinResult x.bs ∧ sf.trace = s0.trace⌝ ∗
            ioVecAt A x.ret r) ∗
          stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

structure ReadFileLitGhost where
  pathA : BitVec 64
  path : List (BitVec 8)
  ret : BitVec 64

/-- Contract of `read_file(path)` on a read-only path literal (`↦ᵣ`), keeping `fs.files` unchanged. -/
def readFileLitSpec (io : IoModel) (A : RustAlloc) (img : Obj.Image) (stk : Nat) :
    Spec ReadFileLitGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
          s.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ io.pathOk x.path⌝ ∗
          (x.pathA ↦ᵣ x.path) ∗ memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        (∃∗ r : Except Unit (List (BitVec 8)),
          ⌜sf.fs.files = s0.fs.files ∧ r = io.rd s0.fs.files x.path ∧ sf.trace = s0.trace⌝ ∗
            ioVecAt A x.ret r) ∗
          (x.pathA ↦ᵣ x.path) ∗ stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

structure WriteFileGhost where
  pathA : BitVec 64
  path : List (BitVec 8)
  buf : BitVec 64
  bs : List (BitVec 8)

/-- Contract of `write_file(path, bytes)` (`Result<(), IoError>` in `x0`: `0` Ok, `1` Err):
updates `fs.files` via `io.wr` with stdout unchanged. -/
def writeFileSpec (io : IoModel) (img : Obj.Image) (stk : Nat) : Spec WriteFileGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
          s.readReg64 .x2 = x.buf ∧ (s.readReg64 .x3).toNat = x.bs.length ∧
          x.path.length < 2 ^ 32 ∧ io.pathOk x.path⌝ ∗
          (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜(match io.wr s0.fs.files x.path x.bs with
          | some F' => sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = F'
          | none => sf.readReg64 .x0 = 1#64 ∧ sf.fs.files = s0.fs.files) ∧
          s0.trace <+: sf.trace ∧
          ProcessOutcome.traceStreamBytes .stdout sf.trace =
            ProcessOutcome.traceStreamBytes .stdout s0.trace⌝ ∗
          (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk }
    img

structure WriteStdoutGhost where
  buf : BitVec 64
  bs : List (BitVec 8)

/-- Contract of `write_stdout(bytes)`: appends `bs` to stdout with `fs.files` unchanged and returns `0`. -/
def writeStdoutSpec (img : Obj.Image) (stk : Nat) : Spec WriteStdoutGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.buf ∧ (s.readReg64 .x1).toNat = x.bs.length⌝ ∗
          (x.buf ↦ₛ x.bs) ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = s0.fs.files ∧ s0.trace <+: sf.trace ∧
          ProcessOutcome.traceStreamBytes .stdout sf.trace =
            ProcessOutcome.traceStreamBytes .stdout s0.trace ++ x.bs⌝ ∗
          (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk }
    img

/-- Bundle of `main`'s four I/O callee contracts (`read_stdin`, `read_file`, `write_file`, `write_stdout`). -/
structure MainIo (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (io : IoModel) (hookStack : Nat) : Prop where
  readStdin : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr mainReadStdinName)
    (readStdinSpec io A img hookStack)
  readFile : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr Cli.readFileName)
    (readFileLitSpec io A img hookStack)
  writeFile : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr mainWriteFileName)
    (writeFileSpec io img hookStack)
  writeStdout : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr mainWriteStdoutName)
    (writeStdoutSpec img hookStack)

/-! ## `run` -/

structure RunCall where
  i : Inputs
  c : CallV
  a : RunAnswer
  res : BitVec 64
  call : BitVec 64
  stores : BitVec 64
  inp : BitVec 64
  coins : BitVec 64

/-- Contract of `signal_session::run(call, stores, input)` (`M+0x710`; result slot in `x0`,
`&Call` in `x1`, `&Stores` in `x2`, input slice in `x3, x4`). Requires `Run i a`, opened stores,
installed coins, `TokenInit`, and `logOff img`; on normal return `fs.files` and stdout are unchanged
and `x0` holds `runResAt` with all pending store write paths satisfying `wrOk`. -/
def runSpec (A : RustAlloc) (img : Obj.Image) (uuidParse : UuidParser)
    (Run : Inputs → RunAnswer → Prop) (wrOk : List (BitVec 8) → Prop) (resStack : Nat) :
    Spec RunCall where
  pre := fun g s0 =>
    ⌜Run g.i g.a ∧ parseArgs uuidParse (g.i.argv.map bytesOfString) = some g.c ∧
      s0.readReg64 .x0 = g.res ∧ s0.readReg64 .x1 = g.call ∧ s0.readReg64 .x2 = g.stores ∧
      s0.readReg64 .x3 = g.inp ∧
      s0.readReg64 .x4 = BitVec.ofNat 64 (inputOf g.i g.c).length ∧
      s0.fs.files = (initFsState (cliInputs g.i)).files ∧
      ProcessOutcome.traceStreamBytes .stdout s0.trace = [] ∧ resStack ≤ s0.sp.toNat⌝ ∗
      memRegion g.res runResSize ∗ callAt A g.call g.c ∗ storesAt A g.stores StoresGhost.opened ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalled img g.coins (coinsOf g.i) ∗
      CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
      CryptoVerification.LibsignalTripleRatchet.logOff img ∗ A.pool ∗ stackAt s0.sp resStack
  post := fun g s0 sf =>
    ⌜s0.trace <+: sf.trace ∧
      sf.fs.files = s0.fs.files ∧
      ProcessOutcome.traceStreamBytes .stdout sf.trace =
        ProcessOutcome.traceStreamBytes .stdout s0.trace⌝ ∗
      memRegion g.call 56 ∗ memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      A.pool ∗ stackAt s0.sp resStack ∗
      (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = g.a⌝ ∗
        runResAt A wrOk g.res a') ∗ anyHeap
  onPanic := fun g s0 sf => ⌜g.a = none ∨ allocFailedIn s0 sf⌝ ∗ anyHeap

end CryptoVerification.SignalSession.Cli.MainHops
