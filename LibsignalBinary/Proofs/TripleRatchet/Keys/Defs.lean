/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.Defs
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Specifications for Ratchet Key Derivation

Separation-logic contracts, result layouts, and stack budgets for:
- `<[u8] as subtle::ConstantTimeEq>::ct_eq` with a read-only second operand (`ctEqSliceROSpec`);
- `<PrivateKey>::calculate_agreement` (`calculateAgreementSpec` ↔ `Ratchet.dh`);
- `<RootKey>::create_chain` (`createChainSpec` ↔ `rootCreateChain`);
- `<MessageKeyGenerator>::generate_keys` (`generateKeysSpec` ↔ `MessageKeyGenerator.generateKeys`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

/-! ## Symbol names -/

abbrev ctEqName : String :=
  "<[u8] as subtle::ConstantTimeEq>::ct_eq"

abbrev calculateAgreementName : String :=
  "<libsignal_core::curve::PrivateKey>::calculate_agreement"

abbrev createChainName : String :=
  "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"

abbrev generateKeysName : String :=
  "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys"

/-! ## Stack budgets (own frame + callee budget) -/

/-- `<PrivateKey>::calculate_agreement` frame (`0x3e5fc: sub sp, sp, #0xa0` = 160 B) +
`allocHookStack` (4096 B, `≥ ct_eq` frame 48 B). -/
abbrev calculateAgreementStack : Nat := 160 + allocHookStack

/-- `<PrivateKey>::calculate_agreement` frame (160 B) + `extHookStack` (`16384` B = `externStack`). -/
abbrev calculateAgreementExtStack : Nat := 160 + extHookStack

/-- `<RootKey>::create_chain` frame (`0x14d14: stp ... [sp, #-0x40]!; +0x014: sub sp, sp, #0x200`
= 576 B) + `calculateAgreementStack` (4256 B, `≥ allocHookStack` = 4096 B, `≥ extractStack` = 976 B,
`≥ expandMultiInfoStack` = 640 B). -/
abbrev createChainStack : Nat := 576 + calculateAgreementStack

/-- `<RootKey>::create_chain` frame (576 B) + `calculateAgreementExtStack` (16544 B). -/
abbrev createChainExtStack : Nat := 576 + calculateAgreementExtStack

/-- `<MessageKeyGenerator>::generate_keys` frame (`0x1ee50: sub sp, sp, #0x1f0` = 496 B) +
`allocHookStack` (4096 B, `≥ extractStack` = 976 B, `≥ expandMultiInfoStack` = 640 B). -/
abbrev generateKeysStack : Nat := 496 + allocHookStack

/-! ## Read-only `ct_eq` contract -/

/-- `<[u8] as subtle::ConstantTimeEq>::ct_eq` contract with a read-only second operand
`p2 ↦ᵣ k2` in `pre` and `post`. -/
noncomputable def ctEqSliceROSpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackFrameFor libsignalSessionImage ctEqName sp
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackFrameFor libsignalSessionImage ctEqName sp

/-- `ct_eq` meets `ctEqSliceROSpec` on `tripleRatchetProgAtExt`. -/
def CtEqROOkExt (b : BitVec 64) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ctEqName) ctEqSliceROSpec

/-- `ct_eq` satisfies `ctEqSliceROSpec` on `tripleRatchetProgAt`. -/
def CtEqROOk (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  CtEqROOkExt b (tripleRatchetExterns C ctl abs)

/-- `ct_eq` meets `ctEqSliceROSpec` on `trTrapProgAt`. -/
def CtEqROOk_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) : Prop :=
  CtEqROOkExt b (trTrapExterns C abs)

/-! ## `<PrivateKey>::calculate_agreement` -/

/-- Pure model of `<PrivateKey>::calculate_agreement`: clamps `our.bytes`, applies `X`, and
returns `none` (`CurveError::InvalidKeyAgreement`) iff the 32-byte shared secret is all zero. -/
def calculateAgreement (X : Ratchet.X25519Fn) (their : PublicKey) (our : PrivateKey) :
    Option (List.Vector (BitVec 8) 32) :=
  let ss := X (Ratchet.clampScalar our.bytes) their.bytes
  if ss.toList = List.replicate 32 0#8 then none else some ss

/-- 24-byte `Result<Box<[u8]>, CurveError>` layout at `r`:
- `some shared`: tag `0#64` at `r` and `boxU8At A (r + 8) ptr shared.toList` at `r + 8..r + 24`;
- `none`: tag `1#64` at `r`, discriminant `3#8` (`InvalidKeyAgreement`) at `r + 8`, and
  `memRegion (r + 9) 15`. -/
def calculateAgreementResultAt (A : RustAlloc) (r : BitVec 64) :
    Option (List.Vector (BitVec 8) 32) → SepProp
  | some shared => (r ↦₆₄ 0#64) ∗ (∃∗ ptr : BitVec 64, boxU8At A (r + 8#64) ptr shared.toList)
  | none => (r ↦₆₄ 1#64) ∗ ((r + 8#64) ↦₈ 3#8) ∗ memRegion (r + 9#64) 15

/-- Ghost arguments of `<PrivateKey>::calculate_agreement` (`0x3e5fc`). -/
structure CalculateAgreementGhost where
  /-- `&self: &PrivateKey` (`x0`, 32 bytes; `+0x010..+0x020: ldur q0/q1, ldrb w8/w9`). -/
  ourA : BitVec 64
  our : PrivateKey
  /-- `their: &PublicKey` (`x1`, 32 bytes; `+0x034: ldp q0, q1, [x1]`). -/
  theirA : BitVec 64
  their : PublicKey
  /-- Sret (`x8`, 24-byte `Result<Box<[u8]>, CurveError>`; `+0x018: mov x19, x8`). -/
  ret : BitVec 64

/-- Contract for `<PrivateKey>::calculate_agreement(x0 = ourA, x1 = theirA)` (sret `x8 = ret`,
24 bytes): clamps `our`, computes X25519 `X`, checks for an all-zero shared secret via `ct_eq`,
writes `calculateAgreementResultAt A x.ret (calculateAgreement X x.their x.our)`, and zeroizes
temporary stack secrets. -/
def calculateAgreementSpec (X : Ratchet.X25519Fn) (A : RustAlloc) :
    Spec CalculateAgreementGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ourA ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x8 = x.ret⌝ ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp calculateAgreementStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      calculateAgreementResultAt A x.ret (calculateAgreement X x.their x.our) ∗
      A.pool ∗ stackAt s0.sp calculateAgreementStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def CalculateAgreementOkExt (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr calculateAgreementName)
    ((calculateAgreementSpec C.X A).inImage img)

def CalculateAgreementOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  CalculateAgreementOkExt img C A (tripleRatchetExterns C ctl abs)

def CalculateAgreementOk_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  CalculateAgreementOkExt img C A (trTrapExterns C abs)

/-! ## `<RootKey>::create_chain` -/

/-- 72-byte `Result<(RootKey, ChainKey), SignalProtocolError>` layout at `r`:
- `.ok (rk', ck)`: `u32` tag `0` at `r`, 32-byte `RootKey` at `r + 4`, and 36-byte `ChainKey`
  at `r + 36`;
- `.error .invalidKeyAgreement`: `u32` tag `1` at `r`, `speWord 10` at `r + 8`, and trailing
  padding at `r + 4..r + 8` and `r + 16..r + 72`. -/
def createChainResultAt (r : BitVec 64) :
    Except SignalProtocolError (RootKey × ChainKey) → SepProp
  | .ok (rk', ck) =>
    (r ↦₃₂ 0#32) ∗ ((r + 4#64) ↦ₛ keyToBytes32 rk') ∗ ((r + 0x24#64) ↦ₛ chainKeyBytes ck)
  | .error .invalidKeyAgreement =>
    (r ↦₃₂ 1#32) ∗ memRegion (r + 4#64) 4 ∗
      ((r + 8#64) ↦₆₄ speWord 10) ∗ memRegion (r + 16#64) 56
  | .error _ => ⌜False⌝

/-- Ghost arguments of `<RootKey>::create_chain` (`0x14d14`). -/
structure CreateChainGhost where
  /-- `self: RootKey` passed by pointer (`x0`, 32 bytes, non-null; `+0x018: mov x22, x0`,
  `+0x078: mov x1, x22; +0x07c: mov w2, #0x20`). -/
  rkA : BitVec 64
  rk : RootKey
  /-- `their_ratchet_key: &PublicKey` (`x1`, 32 bytes). -/
  theirA : BitVec 64
  their : PublicKey
  /-- `our_ratchet_key: &PrivateKey` (`x2`, 32 bytes; `+0x024: mov x0, x2`). -/
  ourA : BitVec 64
  our : PrivateKey
  /-- Sret (`x8`, 72-byte `Result<(RootKey, ChainKey), SPE>`; `+0x01c: mov x19, x8`). -/
  ret : BitVec 64

/-- Contract for `<RootKey>::create_chain(x0 = rkA, x1 = theirA, x2 = ourA)` (sret `x8 = ret`,
72 bytes): runs `calculate_agreement`, derives `(rk', ck)` via HKDF-SHA256 with info
`"WhisperRatchet"`, frees the temporary shared-secret box, and writes
`createChainResultAt x.ret (rootCreateChain C x.rk x.their x.our)`. -/
def createChainSpec (C : Crypto) (A : RustAlloc) : Spec CreateChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.rkA ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x2 = x.ourA ∧
      s.readReg64 .x8 = x.ret ∧ x.rkA ≠ 0#64⌝ ∗
      (x.rkA ↦ₛ keyToBytes32 x.rk) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗ memRegion x.ret 72 ∗
      A.pool ∗ stackAt s.sp createChainStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.rkA ↦ₛ keyToBytes32 x.rk) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗
      createChainResultAt x.ret (rootCreateChain C x.rk x.their x.our) ∗
      A.pool ∗ stackAt s0.sp createChainStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def CreateChainOkExt (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr createChainName)
    ((createChainSpec C A).inImage img)

def CreateChainOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  CreateChainOkExt img C A (tripleRatchetExterns C ctl abs)

def CreateChainOk_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  CreateChainOkExt img C A (trTrapExterns C abs)

/-! ## `<MessageKeyGenerator>::generate_keys` -/

/-- 84-byte `MessageKeys { cipher_key, mac_key, iv, counter }` layout at `r`:
32-byte `cipher_key` at `+0`, 32-byte `mac_key` at `+32`, 16-byte `iv` at `+64`, and
`u32` `counter` at `+80`. -/
def messageKeysAt (r : BitVec 64) (mk : MessageKeys) : SepProp :=
  (r ↦ₛ keyToBytes32 mk.cipherKey) ∗
    ((r + 0x20#64) ↦ₛ keyToBytes32 mk.macKey) ∗
    ((r + 0x40#64) ↦ₛ CBC.blockToBytesLE mk.iv) ∗
    ((r + 0x50#64) ↦₃₂ mk.counter)

/-- Ghost arguments of `<MessageKeyGenerator>::generate_keys` (`0x1ee50`). -/
structure GenerateKeysGhost where
  /-- `self: MessageKeyGenerator` passed by pointer (`x0`, 40 bytes, consumed; `mkgAt A genA g`). -/
  genA : BitVec 64
  g : MessageKeyGenerator
  /-- `pqr_key: Option<Vec<u8>>` passed by pointer (`x1`, 24 bytes, consumed;
  `spqrRecvKeyAt A pqrKeyA pqrKey` from `Specifications/LibsignalTripleRatchet.lean`). -/
  pqrKeyA : BitVec 64
  pqrKey : Salt
  /-- Sret (`x8`, 84-byte `MessageKeys`; `+0x024: mov x19, x8`). -/
  ret : BitVec 64

/-- Contract for `<MessageKeyGenerator>::generate_keys(x0 = genA, x1 = pqrKeyA)` (sret
`x8 = ret`, 84 bytes) on a `Seed` generator (`mkgAt A x.genA x.g`): derives 80 HKDF-SHA256
bytes with info `"WhisperMessageKeys"`, writes `messageKeysAt x.ret (x.g.generateKeys F x.pqrKey)`,
and frees the consumed `seed` and `pqrKey` heap buffers. -/
def generateKeysSpec (F : ShaCompress) (A : RustAlloc) : Spec GenerateKeysGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.genA ∧ s.readReg64 .x1 = x.pqrKeyA ∧ s.readReg64 .x8 = x.ret ∧
      x.g.seed.length = 32⌝ ∗
      mkgAt A x.genA x.g ∗ spqrRecvKeyAt A x.pqrKeyA x.pqrKey ∗ memRegion x.ret 84 ∗
      A.pool ∗ stackAt s.sp generateKeysStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.genA 40 ∗ memRegion x.pqrKeyA 24 ∗
      messageKeysAt x.ret (x.g.generateKeys F x.pqrKey) ∗
      A.pool ∗ stackAt s0.sp generateKeysStack

def GenerateKeysOkExt (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr generateKeysName)
    ((generateKeysSpec C.F A).inImage img)

def GenerateKeysOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  GenerateKeysOkExt img C A (tripleRatchetExterns C ctl abs)

def GenerateKeysOk_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  GenerateKeysOkExt img C A (trTrapExterns C abs)

/-! ## `extHookStack` stack budgets, specs, and `OkX` predicates -/

/-- `<PrivateKey>::calculate_agreement` frame (160 B) + `extHookStack` (`= calculateAgreementExtStack`). -/
abbrev calculateAgreementStackX : Nat := calculateAgreementExtStack

/-- `<RootKey>::create_chain` frame (576 B) + `calculateAgreementStackX` (`= createChainExtStack`). -/
abbrev createChainStackX : Nat := createChainExtStack

/-- `<MessageKeyGenerator>::generate_keys` frame (496 B) + `extHookStack`. -/
abbrev generateKeysStackX : Nat := 496 + extHookStack

/-- `calculateAgreementSpec X A` at `calculateAgreementStackX`. -/
def calculateAgreementSpecX (X : Ratchet.X25519Fn) (A : RustAlloc) :
    Spec CalculateAgreementGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ourA ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x8 = x.ret⌝ ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp calculateAgreementStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      calculateAgreementResultAt A x.ret (calculateAgreement X x.their x.our) ∗
      A.pool ∗ stackAt s0.sp calculateAgreementStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def CalculateAgreementOkX (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr calculateAgreementName)
    ((calculateAgreementSpecX C.X A).inImage img)

/-- `createChainSpec C A` at `createChainStackX`. -/
def createChainSpecX (C : Crypto) (A : RustAlloc) : Spec CreateChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.rkA ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x2 = x.ourA ∧
      s.readReg64 .x8 = x.ret ∧ x.rkA ≠ 0#64⌝ ∗
      (x.rkA ↦ₛ keyToBytes32 x.rk) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗ memRegion x.ret 72 ∗
      A.pool ∗ stackAt s.sp createChainStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.rkA ↦ₛ keyToBytes32 x.rk) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗
      createChainResultAt x.ret (rootCreateChain C x.rk x.their x.our) ∗
      A.pool ∗ stackAt s0.sp createChainStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def CreateChainOkX (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr createChainName)
    ((createChainSpecX C A).inImage img)

/-- `generateKeysSpec F A` at `generateKeysStackX`. -/
def generateKeysSpecX (F : ShaCompress) (A : RustAlloc) : Spec GenerateKeysGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.genA ∧ s.readReg64 .x1 = x.pqrKeyA ∧ s.readReg64 .x8 = x.ret ∧
      x.g.seed.length = 32⌝ ∗
      mkgAt A x.genA x.g ∗ spqrRecvKeyAt A x.pqrKeyA x.pqrKey ∗ memRegion x.ret 84 ∗
      A.pool ∗ stackAt s.sp generateKeysStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.genA 40 ∗ memRegion x.pqrKeyA 24 ∗
      messageKeysAt x.ret (x.g.generateKeys F x.pqrKey) ∗
      A.pool ∗ stackAt s0.sp generateKeysStackX

def GenerateKeysOkX (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr generateKeysName)
    ((generateKeysSpecX C.F A).inImage img)

/-! ## Relocatable `[LibsignalPlacement]` helpers -/

/-- Both code blocks (`LibsignalCodeLoaded`) and `.rodata` (`LibsignalRoLoaded`) are loaded in `m`. -/
def LibsignalCodeRoLoaded (pl : Obj.MultiPlacement) (m : Memory) : Prop :=
  LibsignalCodeLoaded pl m ∧ LibsignalRoLoaded pl m

theorem LibsignalCodeRoLoaded.of_keepsFrozen {pl : Obj.MultiPlacement} {m m' : Memory}
    (h : LibsignalCodeRoLoaded pl m) (hk : m.KeepsFrozen m') : LibsignalCodeRoLoaded pl m' :=
  ⟨h.1.of_keepsFrozen hk, libsignalRoLoaded_of_keepsFrozen h.2 hk⟩

theorem LibsignalCodeRoLoaded.of_libsignalFrozen {pl : Obj.MultiPlacement} {m : Memory}
    (h : LibsignalFrozen pl m) : LibsignalCodeRoLoaded pl m :=
  ⟨LibsignalCodeLoaded.of_codeLoaded h.2, h.1⟩

/-- Add `⌜LibsignalCodeRoLoaded pl s0.mem⌝` (`LibsignalCodeLoaded pl s0.mem ∧ LibsignalRoLoaded pl s0.mem`)
to `spec`'s precondition. -/
abbrev withLsCodeRoLoaded {α : Type} (pl : Obj.MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalCodeRoLoaded pl s0.mem⌝ }

/-- Add `⌜LibsignalFrozen pl s0.mem⌝` to `spec`'s precondition. -/
abbrev withLsFrozen {α : Type} (pl : Obj.MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalFrozen pl s0.mem⌝ }

theorem extract_withLsCodeRoLoaded {α : Type} {pl : Obj.MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withLsCodeRoLoaded pl spec).pre x s0 ∗ R) :
    LibsignalCodeRoLoaded pl s0.mem ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withLsCodeRoLoaded] at hpre
  rwa [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre

theorem extract_withLsFrozen {α : Type} {pl : Obj.MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withLsFrozen pl spec).pre x s0 ∗ R) :
    LibsignalFrozen pl s0.mem ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withLsFrozen] at hpre
  rwa [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre

theorem subroutine_ok_withLsCodeRoLoaded_of_plain {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => (extract_withLsCodeRoLoaded hp).2) (fun _ _ _ _ hq => hq)

theorem subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hp
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hfr.1, hpre⟩)
    (fun _ _ _ _ hq => hq)

theorem subroutine_ok_withLsFrozen_of_withLsCodeRoLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded pl spec)) :
    subroutine_ok prog entry (withLsFrozen pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := extract_withLsFrozen hp
      dsimp only [withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨LibsignalCodeRoLoaded.of_libsignalFrozen hfr, hpre⟩)
    (fun _ _ _ _ hq => hq)

theorem sepWP_seq_lscro {prog : Program} {mid tgt : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {post : State → SepProp → Prop}
    (hfr : LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded pl sm.mem → SepWP prog tgt sm Pm post)) :
    SepWP prog tgt s P post :=
  SepWP.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hfr h

theorem sepWPp_seq_lscro {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {Q Qp : State → SepProp → Prop}
    (hfr : LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hfr h

/-- Add a read-only slice `(roAddr ↦ᵣ roBytes)` to `spec`'s precondition and postcondition. -/
abbrev withRoSlice {α : Type} (roAddr : BitVec 64) (roBytes : List (BitVec 8)) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s => (roAddr ↦ᵣ roBytes) ∗ spec.pre x s
    post := fun x s0 sf => (roAddr ↦ᵣ roBytes) ∗ spec.post x s0 sf }

theorem subroutine_ok_withLsCodeRoLoaded_of_withRoSlice {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {roSym : String} {roBytes : List (BitVec 8)} {spec : Spec α}
    (hchk : lsroCheck roSym roBytes = true)
    (h : subroutine_ok prog entry (withLsCodeRoLoaded pl (withRoSlice (pl.ρ roSym) roBytes spec))) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _
  obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hpre
  have hpre' : s0.mem ⊨ (withLsCodeRoLoaded pl (withRoSlice (pl.ρ roSym) roBytes spec)).pre x s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, withRoSlice]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr, ?_⟩
    rw [sepConj_assoc]
    exact lsro_intro_chk hfr.2 hchk hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hsp (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, withRoSlice] at hq
    rw [sepConj_assoc] at hq
    exact Satisfies.of_sep_right hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem subroutine_ok_withLsCodeRoLoaded_rodata' {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {roSym : String} {roBytes : List (BitVec 8)} {spec : Spec α}
    (hchk : lsroCheck roSym roBytes = true)
    (h : subroutine_ok prog entry
      { spec with
        pre := fun x s => ⌜LibsignalCodeRoLoaded pl s.mem⌝ ∗ (pl.ρ roSym ↦ᵣ roBytes) ∗ spec.pre x s
        post := fun x s0 sf => (pl.ρ roSym ↦ᵣ roBytes) ∗ spec.post x s0 sf }) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) := by
  refine subroutine_ok_withLsCodeRoLoaded_of_withRoSlice hchk ?_
  refine subroutine_ok_mono h ?_ (fun _ _ _ _ hq => hq)
  intro x R s0 hp
  obtain ⟨hfr, hp⟩ := extract_withLsCodeRoLoaded hp
  dsimp only [withRoSlice] at hp ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
  exact ⟨hfr, hp⟩

theorem keys_ls_subroutine_ok_of_block_cro [LibsignalPlacement] {α : Type} {callerProg calleeProg : Program}
    {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec))
    {bi bj : Nat} [LsBlockBound bi] [hbj : LsBlockBound bj]
    (_hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hfr0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸
      hfr0.1 j (Nat.lt_of_lt_of_le hj hbj.le_blocks) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

theorem keys_ls_externAt?_of_mem [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} (hmem : sym ∈ libsignalSessionExterns := by decide)
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ sym) = H sym := by
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem hmem
  exact ls_externAt?_of_blockProg (k := k) (by rw [List.getElem?_eq_getElem hlt, hk]) hi hunmut

theorem keys_ls_hook_ok_of_mem [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide)
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk ((keys_ls_externAt?_of_mem hmem hi hunmut).trans hf) hok

/-- Image-free relocatable `ct_eq` contract with a read-only second operand and `memRegion (sp - 48#64) 48` own frame. -/
def ctEqSliceROMemSpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ memRegion (sp - 48#64) 48
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ memRegion (sp - 48#64) 48

end CryptoVerification.LibsignalTripleRatchet
