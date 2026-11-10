/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Defs
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr

/-!
# Compiled SipHash-1-3 Subroutine Specifications

Hoare-triple specifications for `SipHasher13::write` (36-byte UUID slice from `ntail = 0`
and 1-byte append for `1 ≤ ntail ≤ 6`), `RandomState::hash_one::<&ProtocolAddress>`
(on `addrBorrowAt` and `protocolAddressAt`), and the `RawTable::reserve_rehash` closures.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.SipHashBin

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.InMem.SipHashModel

/-! ## `SipHasher13::write` Specifications -/

/-- Ghost inputs for `SipHasher13::write` on a byte slice at `msgPtr`. -/
structure SipWriteGhost where
  hAddr : BitVec 64
  msgPtr : BitVec 64
  h : SipHasher13
  msg : List (BitVec 8)

/-- Specification of `SipHasher13::write` for a 36-byte slice starting from `h.ntail = 0`
(4 full 8-byte blocks plus a 4-byte tail). -/
def sipWrite36Spec : Spec SipWriteGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.hAddr ∧ s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = 36#64 ∧ x.msg.length = 36 ∧
      x.h.ntail = 0 ∧ x.h.length + 36 < 2 ^ 64⌝ ∗
      sipHasher13At x.hAddr x.h ∗ (x.msgPtr ↦ₛ x.msg)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sipHasher13At x.hAddr (x.h.write (x.msg.map UInt8.ofBitVec)) ∗ (x.msgPtr ↦ₛ x.msg)

/-- Ghost inputs for a 1-byte `SipHasher13::write` call. -/
structure SipWriteU8Ghost where
  hAddr : BitVec 64
  bPtr : BitVec 64
  h : SipHasher13
  b : BitVec 8

/-- Specification of `SipHasher13::write` for a 1-byte slice when `1 ≤ h.ntail ≤ 6`. -/
def sipWriteU8Spec : Spec SipWriteU8Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.hAddr ∧ s.readReg64 .x1 = x.bPtr ∧
      s.readReg64 .x2 = 1#64 ∧ 1 ≤ x.h.ntail ∧ x.h.ntail ≤ 6 ∧
      x.h.length + 1 < 2 ^ 64⌝ ∗
      sipHasher13At x.hAddr x.h ∗ (x.bPtr ↦₈ x.b)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sipHasher13At x.hAddr (x.h.writeU8 (UInt8.ofBitVec x.b)) ∗ (x.bPtr ↦₈ x.b)

/-! ## `RandomState::hash_one::<&ProtocolAddress>` Specifications -/

/-- Ghost inputs for `hash_one::<&ProtocolAddress>` over `addrBorrowAt`. -/
structure HashOneAddrBorrowGhost where
  k0 : BitVec 64
  k1 : BitVec 64
  addr : BitVec 64
  ptr : BitVec 64
  name : List (BitVec 8)
  dev : BitVec 8

/-- Borrowed-footprint specification of `hash_one::<&ProtocolAddress>` for a 36-byte name. -/
def hashOneAddrBorrow36Spec : Spec HashOneAddrBorrowGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.k0 ∧ s.readReg64 .x1 = x.k1 ∧
      s.readReg64 .x2 = x.addr ∧ x.name.length = 36⌝ ∗
      addrBorrowAt x.addr x.ptr x.name x.dev ∗
      stackAt s.sp hashOneAddrStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = hashAddrBv x.k0 x.k1 x.name x.dev ∧ sf.trace = s0.trace⌝ ∗
      addrBorrowAt x.addr x.ptr x.name x.dev ∗
      stackAt s0.sp hashOneAddrStack

/-- Ghost inputs for `hash_one::<&ProtocolAddress>` over `protocolAddressAt`. -/
structure HashOneAddrGhost where
  k0 : BitVec 64
  k1 : BitVec 64
  addr : BitVec 64
  g : AddrGhost

/-- Full `protocolAddressAt` specification of `hash_one::<&ProtocolAddress>` for a 36-byte name. -/
def hashOneAddr36Spec (A : RustAlloc) : Spec HashOneAddrGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.k0 ∧ s.readReg64 .x1 = x.k1 ∧
      s.readReg64 .x2 = x.addr ∧ x.g.name.bytes.length = 36⌝ ∗
      protocolAddressAt A x.g x.addr ∗
      stackAt s.sp hashOneAddrStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = hashAddrBv x.k0 x.k1 x.g.name.bytes x.g.device ∧ sf.trace = s0.trace⌝ ∗
      protocolAddressAt A x.g x.addr ∗
      stackAt s0.sp hashOneAddrStack

/-! ## `RawTable::reserve_rehash` Closure Specifications -/

/-- Ghost inputs for the `RawTable::reserve_rehash` inner hasher closures. -/
structure RehashClosureGhost where
  closurePtr : BitVec 64
  outerClosurePtr : BitVec 64
  rsPtr : BitVec 64
  tablePtr : BitVec 64
  dataEnd : BitVec 64
  idx : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  ptr : BitVec 64
  name : List (BitVec 8)
  dev : BitVec 8

/-- Downward 64-byte bucket address `dataEnd - (idx <<< 6) - 0x40` in `RawTable<(ProtocolAddress, IdentityKey)>`. -/
def idBucketAddr (dataEnd idx : BitVec 64) : BitVec 64 :=
  (dataEnd - (idx <<< 6#64)) - 0x40#64

/-- Downward 400-byte bucket address `dataEnd - idx * 0x190 - 0x190` in `RawTable<(ProtocolAddress, SessionRecord)>`. -/
def sessionBucketAddr (dataEnd idx : BitVec 64) : BitVec 64 :=
  (dataEnd + (0#64 - idx * 0x190#64)) - 0x190#64

/-- Specification of the `RawTable<(ProtocolAddress, IdentityKey)>::reserve_rehash` hasher closure. -/
def rehashIdClosure36Spec : Spec RehashClosureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.closurePtr ∧ s.readReg64 .x1 = x.tablePtr ∧
      s.readReg64 .x2 = x.idx ∧ x.name.length = 36⌝ ∗
      (x.closurePtr ↦₆₄ x.outerClosurePtr) ∗
      (x.outerClosurePtr ↦₆₄ x.rsPtr) ∗
      randomStateAt x.rsPtr x.k0 x.k1 ∗
      (x.tablePtr ↦₆₄ x.dataEnd) ∗
      addrBorrowAt (idBucketAddr x.dataEnd x.idx) x.ptr x.name x.dev ∗
      stackAt s.sp rehashIdClosureStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = hashAddrBv x.k0 x.k1 x.name x.dev ∧ sf.trace = s0.trace⌝ ∗
      (x.closurePtr ↦₆₄ x.outerClosurePtr) ∗
      (x.outerClosurePtr ↦₆₄ x.rsPtr) ∗
      randomStateAt x.rsPtr x.k0 x.k1 ∗
      (x.tablePtr ↦₆₄ x.dataEnd) ∗
      addrBorrowAt (idBucketAddr x.dataEnd x.idx) x.ptr x.name x.dev ∗
      stackAt s0.sp rehashIdClosureStack

/-- Specification of the `RawTable<(ProtocolAddress, SessionRecord)>::reserve_rehash` hasher closure. -/
def rehashSessionClosure36Spec : Spec RehashClosureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.closurePtr ∧ s.readReg64 .x1 = x.tablePtr ∧
      s.readReg64 .x2 = x.idx ∧ x.name.length = 36⌝ ∗
      (x.closurePtr ↦₆₄ x.outerClosurePtr) ∗
      (x.outerClosurePtr ↦₆₄ x.rsPtr) ∗
      randomStateAt x.rsPtr x.k0 x.k1 ∗
      (x.tablePtr ↦₆₄ x.dataEnd) ∗
      addrBorrowAt (sessionBucketAddr x.dataEnd x.idx) x.ptr x.name x.dev ∗
      stackAt s.sp rehashSessionClosureStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = hashAddrBv x.k0 x.k1 x.name x.dev ∧ sf.trace = s0.trace⌝ ∗
      (x.closurePtr ↦₆₄ x.outerClosurePtr) ∗
      (x.outerClosurePtr ↦₆₄ x.rsPtr) ∗
      randomStateAt x.rsPtr x.k0 x.k1 ∗
      (x.tablePtr ↦₆₄ x.dataEnd) ∗
      addrBorrowAt (sessionBucketAddr x.dataEnd x.idx) x.ptr x.name x.dev ∗
      stackAt s0.sp rehashSessionClosureStack

end CryptoVerification.E2E.InMem.SipHashBin
