/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalTripleRatchetProofDefs

/-!
# Specifications for In-Image Whole-Crate Callees

Separation-logic contracts and stack budgets for compiled `uuid` and `libsignal-core` callees:
- `<uuid::Uuid>::try_parse` (`uuidTryParseSpec`, `uuidTryParseCodeSpec`);
- `ServiceId::parse_from_service_id_string` (`parseSidCodeSpec`, `parseSidCodeStackSpec`);
- `<PublicKey as TryFrom<&[u8]>>::try_from` (`pkTryFromCodeSpec`);
- `PrivateKey::serialize` (`privSerializeSpec`, `privSerializeSpecX`);
- `<ProtocolAddress as Display>::fmt` (`addrDisplaySpec`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

/-! ## `<uuid::Uuid>::try_parse` -/

/-- The 32-byte `Result<Uuid, uuid::Error>` that `try_parse` writes at `out`: `some u` = word 0
`uuidOkTag`, the UUID at `+4..+20`, 12 bytes unspecified; `none` = word 0 `uuidErrParseOther`, 28
bytes unspecified. -/
def uuidResultAt (out : BitVec 64) : Option (List.Vector (BitVec 8) 16) → SepProp
  | some u => (out ↦₃₂ uuidOkTag) ∗ ((out + 4#64) ↦ₛ u.toList) ∗ memRegion (out + 20#64) 12
  | none => (out ↦₃₂ uuidErrParseOther) ∗ memRegion (out + 4#64) 28

/-- Stack-free contract for `<uuid::Uuid>::try_parse(x0 = ptr, x1 = len)` (sret `x8`, 32 bytes):
writes `uuidResultAt out (parse bs)`. Ghost: `(p, bs, out)`. -/
def uuidTryParseSpec (parse : UuidParser) : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p, bs, out) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 32
  post := fun (p, bs, out) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (p ↦ₛ bs) ∗ uuidResultAt out (parse bs)

/-- Stack budget `0xC0` for `<uuid::Uuid>::try_parse` (`0x40` own frame + `0x60`
`uuid::parser::try_parse` + `0x20` `decode_hex32`). -/
abbrev uuidTryParseStack : Nat := 0xC0

/-- `uuidTryParseSpec parse` with stack budget `uuidTryParseStack`. -/
def uuidTryParseCodeSpec (parse : UuidParser) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun x s => (uuidTryParseSpec parse).pre x s ∗ stackAt s.sp uuidTryParseStack
  post := fun x s0 sf => (uuidTryParseSpec parse).post x s0 sf ∗ stackAt s0.sp uuidTryParseStack
/-- `uuidTryParseSpec uuidTryParse` with configurable stack budget `hookStack`. -/
def uuidTryParseStackSpec (hookStack : Nat := 0) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun x s => (uuidTryParseSpec uuidTryParse).pre x s ∗ stackAt s.sp hookStack
  post := fun x s0 sf => (uuidTryParseSpec uuidTryParse).post x s0 sf ∗ stackAt s0.sp hookStack

/-! ## `ServiceId::parse_from_service_id_string` -/

/-- Total stack budget `0x50 + uuidTryParseStack` for `ServiceId::parse_from_service_id_string`. -/
abbrev parseSidStack : Nat := 0x50 + uuidTryParseStack

/-- `parse_from_service_id_string`'s own frame (`sub sp, sp, #0x50`), without the callee's stack. -/
abbrev parseSidFrameStack : Nat := 0x50

/-- `parseSidSpec (serviceIdParse parse)` augmented with stack budget `parseSidStack`. -/
def parseSidCodeSpec (parse : UuidParser) : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun x s => (parseSidSpec (serviceIdParse parse)).pre x s ∗ stackAt s.sp parseSidStack
  post := fun x s0 sf =>
    (parseSidSpec (serviceIdParse parse)).post x s0 sf ∗ stackAt s0.sp parseSidStack

/-- Stack-framed variant of `parseSidCodeSpec uuidTryParse`, threading
`stackAt (s.sp - 80#64) hookStack` below `parseSidFrameStack`. -/
def parseSidCodeStackSpec (hookStack : Nat := 0) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun x s =>
    (parseSidSpec (serviceIdParse uuidTryParse)).pre x s ∗
      stackAt (s.sp - 80#64) hookStack ∗ stackAt s.sp parseSidFrameStack
  post := fun x s0 sf =>
    (parseSidSpec (serviceIdParse uuidTryParse)).post x s0 sf ∗
      stackAt (s0.sp - 80#64) hookStack ∗ stackAt s0.sp parseSidFrameStack

/-! ## `<PublicKey as TryFrom<&[u8]>>::try_from` -/

/-- `pkTryFromSpec` augmented with `logOff img` (so the `log::Log::log` trailing-bytes warning
path is skipped without allocating a stack frame). -/
def pkTryFromCodeSpec (img : Obj.Image) : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun x s => pkTryFromSpec.pre x s ∗ logOff img
  post := fun x s0 sf => pkTryFromSpec.post x s0 sf ∗ logOff img

/-! ## `PrivateKey::serialize` -/

/-- `<PrivateKey>::serialize(x0 = &self)` (sret `x8`, `Vec<u8>`): allocates a fresh 32-byte
`Vec<u8>` copy of `bs` at `ret`. Ghost: `(k, bs, ret)`. -/
def privSerializeSpec (A : RustAlloc) : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (k, bs, ret) s =>
    ⌜s.readReg64 .x0 = k ∧ s.readReg64 .x8 = ret ∧ bs.length = 32⌝ ∗ (k ↦ₛ bs) ∗
      memRegion ret 24 ∗ A.pool ∗ stackAt s.sp extHookStack
  post := fun (k, bs, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (k ↦ₛ bs) ∗ vecU8 A ret bs ∗ A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Stack budget `extHookStack + 32` for `PrivateKey::serialize`. -/
abbrev privSerializeStackX : Nat := extHookStack + 32

/-- `privSerializeSpec A` at stack budget `privSerializeStackX`. -/
def privSerializeSpecX (A : RustAlloc) : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (k, bs, ret) s =>
    ⌜s.readReg64 .x0 = k ∧ s.readReg64 .x8 = ret ∧ bs.length = 32⌝ ∗ (k ↦ₛ bs) ∗
      memRegion ret 24 ∗ A.pool ∗ stackAt s.sp privSerializeStackX
  post := fun (k, bs, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (k ↦ₛ bs) ∗ vecU8 A ret bs ∗ A.pool ∗ stackAt s0.sp privSerializeStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `<ProtocolAddress as Display>::fmt` -/

/-- Stack budget `extHookStack + 0x30` for `<ProtocolAddress as Display>::fmt`. -/
abbrev addrDisplayStack : Nat := extHookStack + 0x30

/-- `<ProtocolAddress as Display>::fmt(x0 = &addr, x1 = &Formatter)`: delegates to
`core::fmt::write` on the `Formatter` writer `(v, vt)`, returning `w0 = 0` and updating `v` to
an owned `Vec<u8>`. Ghost: `(f, v, vt, bs)`. -/
def addrDisplaySpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (f, v, vt, bs) s =>
    ⌜s.readReg64 .x1 = f⌝ ∗ (f ↦₆₄ v) ∗ ((f + 8#64) ↦₆₄ vt) ∗ vecU8 A v bs ∗ A.pool ∗
      stackAt s.sp addrDisplayStack
  post := fun (f, v, vt, _) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗ (f ↦₆₄ v) ∗
      ((f + 8#64) ↦₆₄ vt) ∗ (∃∗ bs' : List (BitVec 8), vecU8 A v bs') ∗ A.pool ∗
      stackAt s0.sp addrDisplayStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.LibsignalTripleRatchet
