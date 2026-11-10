/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Kits
public import LibsignalBinary.Proofs.SpqrV1.Chain.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunFixed

/-!
# Function-Level Specifications of `address_text` and `Dir` Store Methods

Machine-level Hoare specifications of `address_text`, `Dir::put::<String>`, `Dir::put::<&str>`,
`RawVec<(String, Vec<u8>)>::grow_one`, and `Dir::get` against the functional store model
(`addressText`, `DirGhost.put`, `DirGhost.get`).

## Memory and ABI Layout

* `Dir` (40 bytes): `changed: Vec<(String, Vec<u8>)>` at `+0` (48-byte entries, alignment 8: owned
  `String` at `+0`, owned `Vec<u8>` at `+0x18`) and read-only `path: &'static str` at `+0x18`.
* `address_text(&ProtocolAddress) -> String`: sret `x0`, address `x1`, frame `0x70`.
* `Dir::put::<String>`: `x0 = self`, moved `name` at `x1`, moved `bytes` at `x2`, frame `0x60`.
* `Dir::put::<&str>`: `x0 = self`, `name = (x1, x2)`, moved `bytes` at `x3`, frame `0x50`.
* `Dir::get`: 48-byte sret `x0` (`okTagVec` + `Vec` at `+8`, or `InvalidState("read", "file could
  not be read")`), `x1 = self`, `name = (x2, x3)`, frame `0x70`.
* `io::read_file`: 24-byte sret `x8` (owned `Vec<u8>` on `Ok`, word 0 `-1` niche on `Err`); panics
  after logging `allocFailedEvent` on heap exhaustion.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## Entry points -/

abbrev addressTextName : String := "libsignal_cli::stores::address_text"

abbrev dirPutName : String := "<libsignal_cli::stores::Dir>::put::<alloc::string::String>"

abbrev dirPutStrName : String := "<libsignal_cli::stores::Dir>::put::<&str>"

abbrev dirGetName : String := "<libsignal_cli::stores::Dir>::get"

abbrev growOneDirName : String :=
  "<alloc::raw_vec::RawVec<(alloc::string::String, alloc::vec::Vec<u8>)>>::grow_one"

abbrev cliFinishGrowName : String := "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"

abbrev readFileName : String := "libsignal_cli_io::read_file"

abbrev cliBcmpName : String := "bcmp"

theorem addressText_fnOff :
    libsignalSessionCode.fnOff addressTextName =
      num% (ls_off% "libsignal_cli::stores::address_text") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "libsignal_cli::stores::address_text")

theorem dirPut_fnOff :
    libsignalSessionCode.fnOff dirPutName =
      num% (ls_off% "<libsignal_cli::stores::Dir>::put::<alloc::string::String>") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::Dir>::put::<alloc::string::String>")

theorem dirPutStr_fnOff :
    libsignalSessionCode.fnOff dirPutStrName =
      num% (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::Dir>::put::<&str>")

theorem dirGet_fnOff :
    libsignalSessionCode.fnOff dirGetName =
      num% (ls_off% "<libsignal_cli::stores::Dir>::get") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_cli::stores::Dir>::get")

theorem growOneDir_fnOff :
    libsignalSessionCode.fnOff growOneDirName =
      num% (ls_off% "<alloc::raw_vec::RawVec<(alloc::string::String, alloc::vec::Vec<u8>)>>::grow_one") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<alloc::raw_vec::RawVec<(alloc::string::String, alloc::vec::Vec<u8>)>>::grow_one")

theorem cliFinishGrow_fnOff :
    libsignalSessionCode.fnOff cliFinishGrowName =
      num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]")

theorem readFile_fnOff :
    libsignalSessionCode.fnOff readFileName = num% (ls_off% "libsignal_cli_io::read_file") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_stub% "libsignal_cli_io::read_file")

/-! ## Layouts -/

/-- One `Dir.changed` entry `(name: String, bytes: Vec<u8>)` at `a` (48 bytes): two owned
`Vec<u8>`s, the name @0 and the bytes @0x18. -/
def dirEntryAt (A : RustAlloc) (e : List (BitVec 8) × List (BitVec 8)) (a : BitVec 64) :
    SepProp :=
  vecU8 A a e.1 ∗ vecU8 A (a + 0x18#64) e.2

/-- A `Dir` at `d` (40 bytes) with ghost `g`: `changed` @0 (a `Vec` of 48-byte entries,
alignment 8, in first-change order) and `path` @0x18, a `&'static str` (`strRefAt`: read-only). -/
def dirAt (A : RustAlloc) (d : BitVec 64) (g : DirGhost) : SepProp :=
  RustHeap.vecOf A 48 8 (dirEntryAt A) d g.changed ∗ strRefAt (d + 0x18#64) g.path

/-- `Result<Vec<u8>, SignalProtocolError>` of `Dir::get` at `r` (48 bytes): `Ok` as
`vecResultAt` (`okTagVec`, the `Vec` @8); every `Err` is `unreadable`'s
`InvalidState("read", _)`. -/
def getResultAt (A : RustAlloc) (r : BitVec 64) : Except Unit (List (BitVec 8)) → SepProp
  | .ok bs => vecResultAt A r (.ok bs)
  | .error _ => speAt A (utf8 "read") r .invalidState

/-- `Result<Vec<u8>, IoError>` of `read_file` at `r` (24 bytes): `Ok` = an owned `Vec<u8>`;
`Err` = word 0 `-1` (the capacity niche), the other 16 bytes unspecified. -/
def ioVecAt (A : RustAlloc) (r : BitVec 64) : Except Unit (List (BitVec 8)) → SepProp
  | .ok bs => vecU8 A r bs
  | .error _ => (r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (r + 8#64) 16

/-! ## Callee contracts the hops take as hypotheses -/

/-- Ghost of a `bcmp(a = x0, b = x1, n = x2)` call; each side read-only (`ro = true`) or owned. -/
structure CliBcmpCall where
  a : BitVec 64
  aRo : Bool
  bsA : List (BitVec 8)
  b : BitVec 64
  bRo : Bool
  bsB : List (BitVec 8)

/-- `bcmp` on two equal-length slices, each `ChainProofs.bytesAt ro` (the name of a `Dir` entry
is owned; a `Dir::get` name may be a literal): `w0 = 0` iff the bytes are equal; trace unchanged.
The `ro`-generic form of `E2E.HooksE.e2eBcmpSpec`. -/
def cliBcmpSpec : Spec CliBcmpCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ s.readReg64 .x1 = x.b ∧
      (s.readReg64 .x2).toNat = x.bsA.length ∧ x.bsB.length = x.bsA.length⌝ ∗
      SpqrV1.ChainProofs.bytesAt x.aRo x.a x.bsA ∗ SpqrV1.ChainProofs.bytesAt x.bRo x.b x.bsB ∗
      stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 32 = 0#32 ↔ x.bsA = x.bsB) ∧ sf.trace = s0.trace⌝ ∗
      SpqrV1.ChainProofs.bytesAt x.aRo x.a x.bsA ∗ SpqrV1.ChainProofs.bytesAt x.bRo x.b x.bsB ∗
      stackAt s0.sp extHookStack

/-- Ghost of a `read_file` call: the owned path `String`'s bytes and the sret (`x8`). -/
structure ReadFileGhost where
  pathA : BitVec 64
  path : List (BitVec 8)
  ret : BitVec 64

/-- Specification of `signal_session_io::read_file`: evaluates `rd` on the entry filesystem for
paths satisfying `pathOk`, returning `ioVecAt` at `x8` and panicking with `allocFailedIn` on OOM. -/
def readFileSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) : Spec ReadFileGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
          s.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ pathOk x.path⌝ ∗
          (x.pathA ↦ₛ x.path) ∗ memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        (∃∗ r : Except Unit (List (BitVec 8)),
          ⌜r = rd s0.fs.files x.path ∧ sf.trace = s0.trace⌝ ∗ ioVecAt A x.ret r) ∗
          (x.pathA ↦ₛ x.path) ∗ stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## `address_text` -/

/-- Ghost of an `address_text` call: the address (its name `Vec` exactly) and the sret. -/
structure AddrTextGhost where
  addr : BitVec 64
  g : AddrGhost
  ret : BitVec 64

/-- Specification of `address_text`: writes an owned `String` holding `addressText g.val` to `ret`
(`name.length < 2 ^ 32`), panicking only on allocation failure. -/
def addrTextSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) : Spec AddrTextGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.addr ∧ x.g.name.bytes.length < 2 ^ 32⌝ ∗
          protocolAddressAt A x.g x.addr ∗ memRegion x.ret 24 ∗ stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ vecU8 A x.ret (addressText x.g.val) ∗
          protocolAddressAt A x.g x.addr ∗ stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## `RawVec<(String, Vec<u8>)>::grow_one` -/

/-- Ghost of a `grow_one` call on `Dir.changed`: the `Vec` header address, its capacity and
buffer, and the entries. -/
structure GrowOneDirGhost where
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  xs : List (List (BitVec 8) × List (BitVec 8))

/-- Specification of `RawVec<(String, Vec<u8>)>::grow_one`: grows capacity to `max (2 * cap) 4`
and relocates the 48-byte entry headers while preserving per-entry heap buffers (`cap < 2 ^ 32`). -/
def growOneDirSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) : Spec GrowOneDirGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.v ∧ x.cap.toNat < 2 ^ 32⌝ ∗
          RustHeap.vecAt A 48 8 (dirEntryAt A) x.v x.cap x.ptr x.xs ∗ stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          (∃∗ ptr' : BitVec 64, RustHeap.vecAt A 48 8 (dirEntryAt A) x.v
            (BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ptr' x.xs) ∗
          stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## `Dir::put` -/

/-- Ghost of a `Dir::put::<String>` call: the `Dir`, and the moved name and bytes (at their
24-byte slots). -/
structure DirPutGhost where
  self : BitVec 64
  dir : DirGhost
  nameV : BitVec 64
  name : List (BitVec 8)
  bytesV : BitVec 64
  bytes : List (BitVec 8)

/-- Specification of `Dir::put::<String>`: updates `dir` to `dir.put name bytes`, returning the
moved 24-byte `name` and `bytes` slots as `memRegion` and panicking only on `grow_one` OOM. -/
def dirPutSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) : Spec DirPutGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.nameV ∧ s.readReg64 .x2 = x.bytesV ∧
          x.dir.changed.length < 2 ^ 32⌝ ∗
          dirAt A x.self x.dir ∗ vecU8 A x.nameV x.name ∗ vecU8 A x.bytesV x.bytes ∗
          stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ dirAt A x.self (x.dir.put x.name x.bytes) ∗
          memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗ stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Ghost of a `Dir::put::<&str>` call: the `Dir`, the borrowed name (read-only literal or
owned), and the moved bytes. -/
structure DirPutStrGhost where
  self : BitVec 64
  dir : DirGhost
  nameA : BitVec 64
  name : List (BitVec 8)
  nameRo : Bool
  bytesV : BitVec 64
  bytes : List (BitVec 8)

/-- Specification of `Dir::put::<&str>`: clones `name` and updates `dir` to `dir.put name bytes`,
returning the `name` slice and uninitialized `bytes` slot and panicking only on allocation failure. -/
def dirPutStrSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) : Spec DirPutStrGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.nameA ∧
          (s.readReg64 .x2).toNat = x.name.length ∧ s.readReg64 .x3 = x.bytesV ∧
          x.name.length < 2 ^ 32 ∧ x.dir.changed.length < 2 ^ 32⌝ ∗
          dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          vecU8 A x.bytesV x.bytes ∗ stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ dirAt A x.self (x.dir.put x.name x.bytes) ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ memRegion x.bytesV 24 ∗
          stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## `Dir::get` -/

/-- Ghost of a `Dir::get` call: the sret, the `Dir`, and the borrowed name. -/
structure DirGetGhost where
  ret : BitVec 64
  self : BitVec 64
  dir : DirGhost
  nameA : BitVec 64
  name : List (BitVec 8)
  nameRo : Bool

/-- Specification of `Dir::get`: writes `dir.get rd F name` as `getResultAt` to `ret` for paths
satisfying `pathOk`, preserving `dir` and `name` and panicking only on allocation failure. -/
def dirGetSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) : Spec DirGetGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.self ∧ s.readReg64 .x2 = x.nameA ∧
          (s.readReg64 .x3).toNat = x.name.length ∧ x.name.length < 2 ^ 32 ∧
          x.dir.path.length < 2 ^ 32 ∧ pathOk (pathOf x.dir.path x.name)⌝ ∗
          dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗ stackAt s.sp stk ∗ A.pool
      post := fun x s0 sf =>
        (∃∗ r : Except Unit (List (BitVec 8)),
          ⌜r = x.dir.get rd s0.fs.files x.name ∧ sf.trace = s0.trace⌝ ∗
            getResultAt A x.ret r) ∗
          dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt s0.sp stk ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

end CryptoVerification.SignalSession.Cli
